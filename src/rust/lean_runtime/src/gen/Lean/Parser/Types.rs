// Lean compiler output
// Module: Lean.Parser.Types
// Imports: Lean.Data.Trie Lean.DocString.Extension Init.Data.String.OrderInstances
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_shrink___redArg};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_eraseRepsBy___redArg,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Hashable::l_String_instHashableRaw_hash;
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_structEq;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Char_utf8Size, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Syntax_getPos_x3f, l_Lean_mkAtom, l_String_decEq___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Data::Position::{
    l_Lean_FileMap_toPosition, l_Lean_instInhabitedFileMap_default,
};
use crate::r#gen::Lean::Data::Trie::{
    initialize_Lean_Data_Trie, runtime_initialize_Lean_Data_Trie,
};
use crate::r#gen::Lean::DocString::Extension::{
    initialize_Lean_DocString_Extension, l_Lean_addBuiltinDocString,
    runtime_initialize_Lean_DocString_Extension,
};
use crate::r#gen::Lean::Message::l_Lean_mkErrorStringWithPos;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_pop, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_dec_lt, lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next, lean_string_utf8_next_fast, lean_string_utf8_prev,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_box_uint32, lean_box_uint64, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Lean_Parser_maxPrec: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_argPrec: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_leadPrec: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_minPrec: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value)
        as *mut LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value)
            as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value: LeanArrayObject<
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
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value)
        as *mut LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value)
            as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value)
            as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value:
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
    m_data: [115, 105, 109, 112, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value)
        as *mut LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value)
            as *mut LeanObject,
        12783917532758215986 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value)
        as *mut LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value)
            as *mut LeanObject,
        3488656302031949961 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_InputContext_endPos__valid___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_instInhabitedInputContext___closed__0_value: LeanStringObject<1> =
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
static mut l_Lean_Parser_instInhabitedInputContext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedInputContext___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_instInhabitedInputContext___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_instInhabitedInputContext___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_instInhabitedInputContext___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_instInhabitedInputContext___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_instInhabitedInputContext: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_InputContext_mk___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_instBEqCacheableParserContext___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_instBEqCacheableParserContext_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instBEqCacheableParserContext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqCacheableParserContext___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instBEqCacheableParserContext: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqCacheableParserContext___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_instCoeParserContextInputContext___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instCoeParserContextInputContext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instCoeParserContextInputContext___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instCoeParserContextInputContext: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instCoeParserContextInputContext___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_instInhabitedError_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_instInhabitedInputContext___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_instInhabitedError_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedError_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedError_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedError_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedError: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedError_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_instBEqError___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_instBEqError_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instBEqError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqError___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Parser_instBEqError: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqError___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0_value:
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
    m_data: [32, 111, 114, 32, 0],
};
static mut l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1_value:
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
    m_data: [44, 32, 0],
};
static mut l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1_value
) as *mut LeanObject;
pub static l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Parser_Error_toString___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [59, 32, 0],
};
static mut l_Lean_Parser_Error_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_toString___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Error_toString___closed__1_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 0],
    };
static mut l_Lean_Parser_Error_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_toString___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Error_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Error_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Error_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Error_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_instBEqParserCacheKey___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_instBEqParserCacheKey_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instBEqParserCacheKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqParserCacheKey___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Parser_instBEqParserCacheKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqParserCacheKey___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_instHashableParserCacheKey___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instHashableParserCacheKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instHashableParserCacheKey___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instHashableParserCacheKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instHashableParserCacheKey___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_initCacheForInput___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_initCacheForInput___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_initCacheForInput___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_initCacheForInput___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_initCacheForInput___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_initCacheForInput___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_SyntaxStack_empty___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Parser_SyntaxStack_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_SyntaxStack_empty___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_SyntaxStack_empty___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_Parser_SyntaxStack_empty: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_SyntaxStack_back___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 80, 97, 114, 115, 101, 114, 46, 84, 121, 112, 101, 115, 0,
        ],
    };
static mut l_Lean_Parser_SyntaxStack_back___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_back___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_SyntaxStack_back___closed__1_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 80, 97, 114, 115, 101, 114, 46, 83, 121, 110, 116, 97, 120, 83,
            116, 97, 99, 107, 46, 98, 97, 99, 107, 0,
        ],
    };
static mut l_Lean_Parser_SyntaxStack_back___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_back___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_SyntaxStack_back___closed__2_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            83, 121, 110, 116, 97, 120, 83, 116, 97, 99, 107, 46, 98, 97, 99, 107, 58, 32, 101,
            108, 101, 109, 101, 110, 116, 32, 105, 115, 32, 105, 110, 97, 99, 99, 101, 115, 115,
            105, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Parser_SyntaxStack_back___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_back___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_SyntaxStack_back___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_SyntaxStack_back___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_SyntaxStack_get_x21___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 80, 97, 114, 115, 101, 114, 46, 83, 121, 110, 116, 97, 120, 83,
            116, 97, 99, 107, 46, 103, 101, 116, 33, 0,
        ],
    };
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_get_x21___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_SyntaxStack_get_x21___closed__1_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            83, 121, 110, 116, 97, 120, 83, 116, 97, 99, 107, 46, 103, 101, 116, 33, 58, 32, 101,
            108, 101, 109, 101, 110, 116, 32, 105, 115, 32, 105, 110, 97, 99, 99, 101, 115, 115,
            105, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_get_x21___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_SyntaxStack_instHAppendArraySyntax: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_ParserState_allErrors___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Parser_ParserState_allErrors___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_allErrors___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_ParserState_mkEOIError___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32,
            105, 110, 112, 117, 116, 0,
        ],
    };
static mut l_Lean_Parser_ParserState_mkEOIError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkEOIError___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0_value: LeanStringObject<
    26,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2_value: LeanStringObject<
    14,
> = LeanStringObject {
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
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_instInhabitedParserFn___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_instInhabitedParserFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instInhabitedParserFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserFn___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedParserFn: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserFn___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedFirstTokens_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_instInhabitedFirstTokens: *mut LeanObject = core::ptr::null_mut();
pub static l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0_value:
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
    m_data: [91, 93, 0],
};
static mut l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1_value:
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
    m_data: [91, 0],
};
static mut l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2_value:
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
    m_data: [93, 0],
};
static mut l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_FirstTokens_toStr___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 112, 115, 105, 108, 111, 110, 0],
    };
static mut l_Lean_Parser_FirstTokens_toStr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_toStr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_FirstTokens_toStr___closed__1_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [117, 110, 107, 110, 111, 119, 110, 0],
    };
static mut l_Lean_Parser_FirstTokens_toStr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_toStr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_FirstTokens_toStr___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [63, 0],
    };
static mut l_Lean_Parser_FirstTokens_toStr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_toStr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_FirstTokens_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_FirstTokens_toStr___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_FirstTokens_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_instToString___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_FirstTokens_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_instToString___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instInhabitedParserInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instInhabitedParserInfo_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_instInhabitedParserInfo_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedParserInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedParserInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_instInhabitedParser_default___closed__0_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserFn___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_instInhabitedParser_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParser_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedParser_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParser_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_instInhabitedParser: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParser_default___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [119, 105, 116, 104, 67, 97, 99, 104, 101, 0]};
static mut l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value) as *mut LeanObject,13015283372816199961 as *mut LeanObject] };
static mut l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value: LeanStringObject<542> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 542, m_capacity: 542, m_length: 541, m_data: [82, 117, 110, 32, 96, 112, 96, 32, 97, 110, 100, 32, 114, 101, 99, 111, 114, 100, 32, 114, 101, 115, 117, 108, 116, 32, 105, 110, 32, 112, 97, 114, 115, 101, 114, 32, 99, 97, 99, 104, 101, 32, 102, 111, 114, 32, 97, 110, 121, 32, 102, 117, 114, 116, 104, 101, 114, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 116, 104, 105, 115, 32, 96, 112, 97, 114, 115, 101, 114, 78, 97, 109, 101, 96, 44, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 110, 116, 101, 120, 116, 44, 32, 97, 110, 100, 32, 112, 97, 114, 115, 101, 114, 32, 115, 116, 97, 116, 101, 46, 10, 96, 112, 96, 32, 99, 97, 110, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 32, 115, 121, 110, 116, 97, 120, 32, 115, 116, 97, 99, 107, 32, 101, 108, 101, 109, 101, 110, 116, 115, 32, 112, 117, 115, 104, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 116, 104, 101, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 32, 105, 110, 32, 111, 114, 100, 101, 114, 32, 116, 111, 32, 109, 97, 107, 101, 32, 99, 97, 99, 104, 105, 110, 103, 32, 105, 110, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 111, 102, 32, 112, 97, 114, 115, 101, 114, 32, 104, 105, 115, 116, 111, 114, 121, 46, 10, 65, 115, 32, 116, 104, 105, 115, 32, 101, 120, 99, 108, 117, 100, 101, 115, 32, 116, 114, 97, 105, 108, 105, 110, 103, 32, 112, 97, 114, 115, 101, 114, 115, 32, 102, 114, 111, 109, 32, 98, 101, 105, 110, 103, 32, 99, 97, 99, 104, 101, 100, 44, 32, 119, 101, 32, 97, 108, 115, 111, 32, 114, 101, 115, 101, 116, 32, 96, 108, 104, 115, 80, 114, 101, 99, 96, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 110, 111, 116, 32, 114, 101, 97, 100, 32, 98, 117, 116, 32, 115, 101, 116, 32, 98, 121, 32, 108, 101, 97, 100, 105, 110, 103, 32, 112, 97, 114, 115, 101, 114, 115, 44, 32, 116, 111, 32, 48, 10, 105, 110, 32, 111, 114, 100, 101, 114, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 99, 97, 99, 104, 101, 32, 104, 105, 116, 115, 46, 32, 70, 105, 110, 97, 108, 108, 121, 44, 32, 96, 101, 114, 114, 111, 114, 77, 115, 103, 96, 32, 105, 115, 32, 97, 108, 115, 111, 32, 114, 101, 115, 101, 116, 32, 116, 111, 32, 96, 110, 111, 110, 101, 96, 32, 97, 115, 32, 97, 32, 108, 101, 97, 100, 105, 110, 103, 32, 112, 97, 114, 115, 101, 114, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 99, 97, 108, 108, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 10, 112, 108, 97, 99, 101, 32, 105, 102, 32, 116, 104, 101, 114, 101, 32, 119, 97, 115, 32, 97, 110, 32, 101, 114, 114, 111, 114, 46, 10, 0]};
static mut l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_ParserFn_run___closed__0_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 8) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_ParserFn_run___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserFn_run___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Parser_mkAtom(
    mut v_info_2149_: *mut LeanObject,
    mut v_val_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    v___x_2151_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_2151_, 0, v_info_2149_);
    lean_ctor_set(v___x_2151_, 1, v_val_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Lean_Parser_mkIdent(
    mut v_info_2152_: *mut LeanObject,
    mut v_rawVal_2153_: *mut LeanObject,
    mut v_val_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    v___x_2155_ = lean_box(0);
    v___x_2156_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_2156_, 0, v_info_2152_);
    lean_ctor_set(v___x_2156_, 1, v_rawVal_2153_);
    lean_ctor_set(v___x_2156_, 2, v_val_2154_);
    lean_ctor_set(v___x_2156_, 3, v___x_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Lean_Parser_getNext(
    mut v_input_2157_: *mut LeanObject,
    mut v_pos_2158_: *mut LeanObject,
) -> u32 {
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u32 = 0;
    v___x_2159_ = lean_string_utf8_next(v_input_2157_, v_pos_2158_);
    v___x_2160_ = lean_string_utf8_get(v_input_2157_, v___x_2159_);
    lean_dec(v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn l_Lean_Parser_getNext___boxed(
    mut v_input_2161_: *mut LeanObject,
    mut v_pos_2162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2163_: u32 = 0;
    let mut v_r_2164_: *mut LeanObject = core::ptr::null_mut();
    v_res_2163_ = l_Lean_Parser_getNext(v_input_2161_, v_pos_2162_);
    lean_dec(v_pos_2162_);
    lean_dec_ref(v_input_2161_);
    v_r_2164_ = lean_box_uint32(v_res_2163_);
    return v_r_2164_;
}
pub unsafe fn _init_l_Lean_Parser_maxPrec() -> *mut LeanObject {
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v___x_2165_ = lean_unsigned_to_nat(1024);
    return v___x_2165_;
}
pub unsafe fn _init_l_Lean_Parser_argPrec() -> *mut LeanObject {
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    v___x_2166_ = lean_unsigned_to_nat(1023);
    return v___x_2166_;
}
pub unsafe fn _init_l_Lean_Parser_leadPrec() -> *mut LeanObject {
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    v___x_2167_ = lean_unsigned_to_nat(1022);
    return v___x_2167_;
}
pub unsafe fn _init_l_Lean_Parser_minPrec() -> *mut LeanObject {
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    v___x_2168_ = lean_unsigned_to_nat(10);
    return v___x_2168_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2169_: *mut LeanObject,
    mut v_x_2170_: *mut LeanObject,
    mut v_x_2171_: *mut LeanObject,
    mut v_x_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2173_ = lean_ctor_get(v_x_2169_, 0);
                v_vs_2174_ = lean_ctor_get(v_x_2169_, 1);
                v_isSharedCheck_2198_ = (!lean_is_exclusive(v_x_2169_)) as u8;
                if v_isSharedCheck_2198_ == 0 {
                    v___x_2176_ = v_x_2169_;
                    v_isShared_2177_ = v_isSharedCheck_2198_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2174_);
                    lean_inc(v_ks_2173_);
                    lean_dec(v_x_2169_);
                    v___x_2176_ = lean_box(0);
                    v_isShared_2177_ = v_isSharedCheck_2198_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2178_ = lean_array_get_size(v_ks_2173_);
                v___x_2179_ = lean_nat_dec_lt(v_x_2170_, v___x_2178_);
                if v___x_2179_ == 0 {
                    lean_dec(v_x_2170_);
                    v___x_2180_ = lean_array_push(v_ks_2173_, v_x_2171_);
                    v___x_2181_ = lean_array_push(v_vs_2174_, v_x_2172_);
                    if v_isShared_2177_ == 0 {
                        lean_ctor_set(v___x_2176_, 1, v___x_2181_);
                        lean_ctor_set(v___x_2176_, 0, v___x_2180_);
                        v___x_2183_ = v___x_2176_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2180_);
                        lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_2181_);
                        v___x_2183_ = v_reuseFailAlloc_2184_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2185_ = lean_array_fget_borrowed(v_ks_2173_, v_x_2170_);
                    v___x_2186_ = lean_name_eq(v_x_2171_, v_k_x27_2185_);
                    if v___x_2186_ == 0 {
                        if v_isShared_2177_ == 0 {
                            v___x_2188_ = v___x_2176_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_ks_2173_);
                            lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_vs_2174_);
                            v___x_2188_ = v_reuseFailAlloc_2192_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2193_ = lean_array_fset(v_ks_2173_, v_x_2170_, v_x_2171_);
                        v___x_2194_ = lean_array_fset(v_vs_2174_, v_x_2170_, v_x_2172_);
                        lean_dec(v_x_2170_);
                        if v_isShared_2177_ == 0 {
                            lean_ctor_set(v___x_2176_, 1, v___x_2194_);
                            lean_ctor_set(v___x_2176_, 0, v___x_2193_);
                            v___x_2196_ = v___x_2176_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2193_);
                            lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2194_);
                            v___x_2196_ = v_reuseFailAlloc_2197_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2183_;
            }
            3 => {
                v___x_2189_ = lean_unsigned_to_nat(1);
                v___x_2190_ = lean_nat_add(v_x_2170_, v___x_2189_);
                lean_dec(v_x_2170_);
                v_x_2169_ = v___x_2188_;
                v_x_2170_ = v___x_2190_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(
    mut v_n_2199_: *mut LeanObject,
    mut v_k_2200_: *mut LeanObject,
    mut v_v_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    v___x_2202_ = lean_unsigned_to_nat(0);
    v___x_2203_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2199_, v___x_2202_, v_k_2200_, v_v_2201_);
    return v___x_2203_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: u64 = 0;
    v___x_2204_ = lean_unsigned_to_nat(1723);
    v___x_2205_ = lean_uint64_of_nat(v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2206_: usize = 0;
    let mut v___x_2207_: usize = 0;
    let mut v___x_2208_: usize = 0;
    v___x_2206_ = 5usize;
    v___x_2207_ = 1usize;
    v___x_2208_ = lean_usize_shift_left(v___x_2207_, v___x_2206_);
    return v___x_2208_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: usize = 0;
    let mut v___x_2211_: usize = 0;
    v___x_2209_ = 1usize;
    v___x_2210_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0);
    v___x_2211_ = lean_usize_sub(v___x_2210_, v___x_2209_);
    return v___x_2211_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    v___x_2212_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2212_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(
    mut v_x_2213_: *mut LeanObject,
    mut v_x_2214_: usize,
    mut v_x_2215_: usize,
    mut v_x_2216_: *mut LeanObject,
    mut v_x_2217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: usize = 0;
    let mut v___x_2220_: usize = 0;
    let mut v___x_2221_: usize = 0;
    let mut v___x_2222_: usize = 0;
    let mut v_j_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v_v_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_node_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v___x_2254_: usize = 0;
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_unused_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: u8 = 0;
    let mut v_ks_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: usize = 0;
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut v_reuseFailAlloc_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2213_) == 0 {
                    v_es_2218_ = lean_ctor_get(v_x_2213_, 0);
                    v___x_2219_ = 5usize;
                    v___x_2220_ = 1usize;
                    v___x_2221_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_2222_ = lean_usize_land(v_x_2214_, v___x_2221_);
                    v_j_2223_ = lean_usize_to_nat(v___x_2222_);
                    v___x_2224_ = lean_array_get_size(v_es_2218_);
                    v___x_2225_ = lean_nat_dec_lt(v_j_2223_, v___x_2224_);
                    if v___x_2225_ == 0 {
                        lean_dec(v_j_2223_);
                        lean_dec(v_x_2217_);
                        lean_dec(v_x_2216_);
                        return v_x_2213_;
                    } else {
                        lean_inc_ref(v_es_2218_);
                        v_isSharedCheck_2262_ = (!lean_is_exclusive(v_x_2213_)) as u8;
                        if v_isSharedCheck_2262_ == 0 {
                            v_unused_2263_ = lean_ctor_get(v_x_2213_, 0);
                            lean_dec(v_unused_2263_);
                            v___x_2227_ = v_x_2213_;
                            v_isShared_2228_ = v_isSharedCheck_2262_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2213_);
                            v___x_2227_ = lean_box(0);
                            v_isShared_2228_ = v_isSharedCheck_2262_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2264_ = lean_ctor_get(v_x_2213_, 0);
                    v_vs_2265_ = lean_ctor_get(v_x_2213_, 1);
                    v_isSharedCheck_2285_ = (!lean_is_exclusive(v_x_2213_)) as u8;
                    if v_isSharedCheck_2285_ == 0 {
                        v___x_2267_ = v_x_2213_;
                        v_isShared_2268_ = v_isSharedCheck_2285_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2265_);
                        lean_inc(v_ks_2264_);
                        lean_dec(v_x_2213_);
                        v___x_2267_ = lean_box(0);
                        v_isShared_2268_ = v_isSharedCheck_2285_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2229_ = lean_array_fget(v_es_2218_, v_j_2223_);
                v___x_2230_ = lean_box(0);
                v_xs_x27_2231_ = lean_array_fset(v_es_2218_, v_j_2223_, v___x_2230_);
                match lean_obj_tag(v_v_2229_) {
                    0 => {
                        v_key_2238_ = lean_ctor_get(v_v_2229_, 0);
                        v_val_2239_ = lean_ctor_get(v_v_2229_, 1);
                        v_isSharedCheck_2249_ = (!lean_is_exclusive(v_v_2229_)) as u8;
                        if v_isSharedCheck_2249_ == 0 {
                            v___x_2241_ = v_v_2229_;
                            v_isShared_2242_ = v_isSharedCheck_2249_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2239_);
                            lean_inc(v_key_2238_);
                            lean_dec(v_v_2229_);
                            v___x_2241_ = lean_box(0);
                            v_isShared_2242_ = v_isSharedCheck_2249_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2250_ = lean_ctor_get(v_v_2229_, 0);
                        v_isSharedCheck_2260_ = (!lean_is_exclusive(v_v_2229_)) as u8;
                        if v_isSharedCheck_2260_ == 0 {
                            v___x_2252_ = v_v_2229_;
                            v_isShared_2253_ = v_isSharedCheck_2260_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2250_);
                            lean_dec(v_v_2229_);
                            v___x_2252_ = lean_box(0);
                            v_isShared_2253_ = v_isSharedCheck_2260_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2261_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2261_, 0, v_x_2216_);
                        lean_ctor_set(v___x_2261_, 1, v_x_2217_);
                        v___y_2233_ = v___x_2261_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2234_ = lean_array_fset(v_xs_x27_2231_, v_j_2223_, v___y_2233_);
                lean_dec(v_j_2223_);
                if v_isShared_2228_ == 0 {
                    lean_ctor_set(v___x_2227_, 0, v___x_2234_);
                    v___x_2236_ = v___x_2227_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
                    v___x_2236_ = v_reuseFailAlloc_2237_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2236_;
            }
            4 => {
                v___x_2243_ = lean_name_eq(v_x_2216_, v_key_2238_);
                if v___x_2243_ == 0 {
                    lean_del_object(v___x_2241_);
                    v___x_2244_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2238_,
                        v_val_2239_,
                        v_x_2216_,
                        v_x_2217_,
                    );
                    v___x_2245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2245_, 0, v___x_2244_);
                    v___y_2233_ = v___x_2245_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2239_);
                    lean_dec(v_key_2238_);
                    if v_isShared_2242_ == 0 {
                        lean_ctor_set(v___x_2241_, 1, v_x_2217_);
                        lean_ctor_set(v___x_2241_, 0, v_x_2216_);
                        v___x_2247_ = v___x_2241_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_x_2216_);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_x_2217_);
                        v___x_2247_ = v_reuseFailAlloc_2248_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2233_ = v___x_2247_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2254_ = lean_usize_shift_right(v_x_2214_, v___x_2219_);
                v___x_2255_ = lean_usize_add(v_x_2215_, v___x_2220_);
                v___x_2256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_node_2250_, v___x_2254_, v___x_2255_, v_x_2216_, v_x_2217_);
                if v_isShared_2253_ == 0 {
                    lean_ctor_set(v___x_2252_, 0, v___x_2256_);
                    v___x_2258_ = v___x_2252_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
                    v___x_2258_ = v_reuseFailAlloc_2259_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2233_ = v___x_2258_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2268_ == 0 {
                    v___x_2270_ = v___x_2267_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_ks_2264_);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_vs_2265_);
                    v___x_2270_ = v_reuseFailAlloc_2284_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v___x_2270_, v_x_2216_, v_x_2217_);
                v___x_2279_ = 7usize;
                v___x_2280_ = lean_usize_dec_le(v___x_2279_, v_x_2215_);
                if v___x_2280_ == 0 {
                    v___x_2281_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2271_);
                    v___x_2282_ = lean_unsigned_to_nat(4);
                    v___x_2283_ = lean_nat_dec_lt(v___x_2281_, v___x_2282_);
                    lean_dec(v___x_2281_);
                    v___y_2273_ = v___x_2283_;
                    state = 10;
                    continue;
                } else {
                    v___y_2273_ = v___x_2280_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2273_ == 0 {
                    v_ks_2274_ = lean_ctor_get(v_newNode_2271_, 0);
                    lean_inc_ref(v_ks_2274_);
                    v_vs_2275_ = lean_ctor_get(v_newNode_2271_, 1);
                    lean_inc_ref(v_vs_2275_);
                    lean_dec_ref(v_newNode_2271_);
                    v___x_2276_ = lean_unsigned_to_nat(0);
                    v___x_2277_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2);
                    v___x_2278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_x_2215_, v_ks_2274_, v_vs_2275_, v___x_2276_, v___x_2277_);
                    lean_dec_ref(v_vs_2275_);
                    lean_dec_ref(v_ks_2274_);
                    return v___x_2278_;
                } else {
                    return v_newNode_2271_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(
    mut v_depth_2286_: usize,
    mut v_keys_2287_: *mut LeanObject,
    mut v_vals_2288_: *mut LeanObject,
    mut v_i_2289_: *mut LeanObject,
    mut v_entries_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v_k_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: u64 = 0;
    let mut v_h_2297_: usize = 0;
    let mut v___x_2298_: usize = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: usize = 0;
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: usize = 0;
    let mut v_h_2303_: usize = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u64 = 0;
    let mut v_hash_2308_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2291_ = lean_array_get_size(v_keys_2287_);
                v___x_2292_ = lean_nat_dec_lt(v_i_2289_, v___x_2291_);
                if v___x_2292_ == 0 {
                    lean_dec(v_i_2289_);
                    return v_entries_2290_;
                } else {
                    v_k_2293_ = lean_array_fget_borrowed(v_keys_2287_, v_i_2289_);
                    v_v_2294_ = lean_array_fget_borrowed(v_vals_2288_, v_i_2289_);
                    if lean_obj_tag(v_k_2293_) == 0 {
                        v___x_2307_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_2296_ = v___x_2307_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2308_ = lean_ctor_get_uint64(
                            v_k_2293_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_2296_ = v_hash_2308_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2297_ = lean_uint64_to_usize(v___y_2296_);
                v___x_2298_ = 5usize;
                v___x_2299_ = lean_unsigned_to_nat(1);
                v___x_2300_ = 1usize;
                v___x_2301_ = lean_usize_sub(v_depth_2286_, v___x_2300_);
                v___x_2302_ = lean_usize_mul(v___x_2298_, v___x_2301_);
                v_h_2303_ = lean_usize_shift_right(v_h_2297_, v___x_2302_);
                v___x_2304_ = lean_nat_add(v_i_2289_, v___x_2299_);
                lean_dec(v_i_2289_);
                lean_inc(v_v_2294_);
                lean_inc(v_k_2293_);
                v___x_2305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_entries_2290_, v_h_2303_, v_depth_2286_, v_k_2293_, v_v_2294_);
                v_i_2289_ = v___x_2304_;
                v_entries_2290_ = v___x_2305_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_2309_: *mut LeanObject,
    mut v_keys_2310_: *mut LeanObject,
    mut v_vals_2311_: *mut LeanObject,
    mut v_i_2312_: *mut LeanObject,
    mut v_entries_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2314_: usize = 0;
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2314_ = lean_unbox_usize(v_depth_2309_);
    lean_dec(v_depth_2309_);
    v_res_2315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2314_, v_keys_2310_, v_vals_2311_, v_i_2312_, v_entries_2313_);
    lean_dec_ref(v_vals_2311_);
    lean_dec_ref(v_keys_2310_);
    return v_res_2315_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_2316_: *mut LeanObject,
    mut v_x_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
    mut v_x_2319_: *mut LeanObject,
    mut v_x_2320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_371__boxed_2321_: usize = 0;
    let mut v_x_372__boxed_2322_: usize = 0;
    let mut v_res_2323_: *mut LeanObject = core::ptr::null_mut();
    v_x_371__boxed_2321_ = lean_unbox_usize(v_x_2317_);
    lean_dec(v_x_2317_);
    v_x_372__boxed_2322_ = lean_unbox_usize(v_x_2318_);
    lean_dec(v_x_2318_);
    v_res_2323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_2316_, v_x_371__boxed_2321_, v_x_372__boxed_2322_, v_x_2319_, v_x_2320_);
    return v_res_2323_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(
    mut v_x_2324_: *mut LeanObject,
    mut v_x_2325_: *mut LeanObject,
    mut v_x_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2328_: u64 = 0;
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u64 = 0;
    let mut v_hash_2333_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2325_) == 0 {
                    v___x_2332_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2328_ = v___x_2332_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2333_ = lean_ctor_get_uint64(
                        v_x_2325_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2328_ = v_hash_2333_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2329_ = lean_uint64_to_usize(v___y_2328_);
                v___x_2330_ = 1usize;
                v___x_2331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_2324_, v___x_2329_, v___x_2330_, v_x_2325_, v_x_2326_);
                return v___x_2331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_SyntaxNodeKindSet_insert(
    mut v_s_2334_: *mut LeanObject,
    mut v_k_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v___x_2336_ = lean_box(0);
    v___x_2337_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_s_2334_, v_k_2335_, v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(
    mut v_00_u03b2_2338_: *mut LeanObject,
    mut v_x_2339_: *mut LeanObject,
    mut v_x_2340_: *mut LeanObject,
    mut v_x_2341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    v___x_2342_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
    return v___x_2342_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(
    mut v_00_u03b2_2343_: *mut LeanObject,
    mut v_x_2344_: *mut LeanObject,
    mut v_x_2345_: usize,
    mut v_x_2346_: usize,
    mut v_x_2347_: *mut LeanObject,
    mut v_x_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    v___x_2349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_, v_x_2348_);
    return v___x_2349_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_2350_: *mut LeanObject,
    mut v_x_2351_: *mut LeanObject,
    mut v_x_2352_: *mut LeanObject,
    mut v_x_2353_: *mut LeanObject,
    mut v_x_2354_: *mut LeanObject,
    mut v_x_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_570__boxed_2356_: usize = 0;
    let mut v_x_571__boxed_2357_: usize = 0;
    let mut v_res_2358_: *mut LeanObject = core::ptr::null_mut();
    v_x_570__boxed_2356_ = lean_unbox_usize(v_x_2352_);
    lean_dec(v_x_2352_);
    v_x_571__boxed_2357_ = lean_unbox_usize(v_x_2353_);
    lean_dec(v_x_2353_);
    v_res_2358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_2350_, v_x_2351_, v_x_570__boxed_2356_, v_x_571__boxed_2357_, v_x_2354_, v_x_2355_);
    return v_res_2358_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2359_: *mut LeanObject,
    mut v_n_2360_: *mut LeanObject,
    mut v_k_2361_: *mut LeanObject,
    mut v_v_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    v___x_2363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v_n_2360_, v_k_2361_, v_v_2362_);
    return v___x_2363_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2364_: *mut LeanObject,
    mut v_depth_2365_: usize,
    mut v_keys_2366_: *mut LeanObject,
    mut v_vals_2367_: *mut LeanObject,
    mut v_heq_2368_: *mut LeanObject,
    mut v_i_2369_: *mut LeanObject,
    mut v_entries_2370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    v___x_2371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_2365_, v_keys_2366_, v_vals_2367_, v_i_2369_, v_entries_2370_);
    return v___x_2371_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2372_: *mut LeanObject,
    mut v_depth_2373_: *mut LeanObject,
    mut v_keys_2374_: *mut LeanObject,
    mut v_vals_2375_: *mut LeanObject,
    mut v_heq_2376_: *mut LeanObject,
    mut v_i_2377_: *mut LeanObject,
    mut v_entries_2378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2379_: usize = 0;
    let mut v_res_2380_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2379_ = lean_unbox_usize(v_depth_2373_);
    lean_dec(v_depth_2373_);
    v_res_2380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(v_00_u03b2_2372_, v_depth_boxed_2379_, v_keys_2374_, v_vals_2375_, v_heq_2376_, v_i_2377_, v_entries_2378_);
    lean_dec_ref(v_vals_2375_);
    lean_dec_ref(v_keys_2374_);
    return v_res_2380_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2381_: *mut LeanObject,
    mut v_x_2382_: *mut LeanObject,
    mut v_x_2383_: *mut LeanObject,
    mut v_x_2384_: *mut LeanObject,
    mut v_x_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    v___x_2386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2382_, v_x_2383_, v_x_2384_, v_x_2385_);
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12()
-> *mut LeanObject {
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    v___x_2413_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10;
    v___x_2414_ = l_Lean_mkAtom(v___x_2413_);
    return v___x_2414_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13()
-> *mut LeanObject {
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    v___x_2415_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12,
    );
    v___x_2416_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5;
    v___x_2417_ = lean_array_push(v___x_2416_, v___x_2415_);
    return v___x_2417_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17()
-> *mut LeanObject {
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    v___x_2428_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2429_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5;
    v___x_2430_ = lean_array_push(v___x_2429_, v___x_2428_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18()
-> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    v___x_2431_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17,
    );
    v___x_2432_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15;
    v___x_2433_ = lean_box(2);
    v___x_2434_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2434_, 0, v___x_2433_);
    lean_ctor_set(v___x_2434_, 1, v___x_2432_);
    lean_ctor_set(v___x_2434_, 2, v___x_2431_);
    return v___x_2434_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19()
-> *mut LeanObject {
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v___x_2435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18,
    );
    v___x_2436_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13,
    );
    v___x_2437_ = lean_array_push(v___x_2436_, v___x_2435_);
    return v___x_2437_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20()
-> *mut LeanObject {
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    v___x_2438_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19,
    );
    v___x_2440_ = lean_array_push(v___x_2439_, v___x_2438_);
    return v___x_2440_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21()
-> *mut LeanObject {
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    v___x_2441_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20,
    );
    v___x_2443_ = lean_array_push(v___x_2442_, v___x_2441_);
    return v___x_2443_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22()
-> *mut LeanObject {
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    v___x_2444_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2445_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21,
    );
    v___x_2446_ = lean_array_push(v___x_2445_, v___x_2444_);
    return v___x_2446_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23()
-> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    v___x_2447_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22,
    );
    v___x_2449_ = lean_array_push(v___x_2448_, v___x_2447_);
    return v___x_2449_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24()
-> *mut LeanObject {
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    v___x_2450_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23,
    );
    v___x_2451_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11;
    v___x_2452_ = lean_box(2);
    v___x_2453_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2453_, 0, v___x_2452_);
    lean_ctor_set(v___x_2453_, 1, v___x_2451_);
    lean_ctor_set(v___x_2453_, 2, v___x_2450_);
    return v___x_2453_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25()
-> *mut LeanObject {
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    v___x_2454_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24,
    );
    v___x_2455_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5;
    v___x_2456_ = lean_array_push(v___x_2455_, v___x_2454_);
    return v___x_2456_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26()
-> *mut LeanObject {
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2457_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25,
    );
    v___x_2458_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9;
    v___x_2459_ = lean_box(2);
    v___x_2460_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2460_, 0, v___x_2459_);
    lean_ctor_set(v___x_2460_, 1, v___x_2458_);
    lean_ctor_set(v___x_2460_, 2, v___x_2457_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27()
-> *mut LeanObject {
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    v___x_2461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26,
    );
    v___x_2462_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5;
    v___x_2463_ = lean_array_push(v___x_2462_, v___x_2461_);
    return v___x_2463_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28()
-> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    v___x_2464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27,
    );
    v___x_2465_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7;
    v___x_2466_ = lean_box(2);
    v___x_2467_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2467_, 0, v___x_2466_);
    lean_ctor_set(v___x_2467_, 1, v___x_2465_);
    lean_ctor_set(v___x_2467_, 2, v___x_2464_);
    return v___x_2467_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29()
-> *mut LeanObject {
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    v___x_2468_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28,
    );
    v___x_2469_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5;
    v___x_2470_ = lean_array_push(v___x_2469_, v___x_2468_);
    return v___x_2470_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30()
-> *mut LeanObject {
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2471_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29,
    );
    v___x_2472_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4;
    v___x_2473_ = lean_box(2);
    v___x_2474_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    lean_ctor_set(v___x_2474_, 1, v___x_2472_);
    lean_ctor_set(v___x_2474_, 2, v___x_2471_);
    return v___x_2474_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam() -> *mut LeanObject {
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2475_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30,
    );
    return v___x_2475_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedInputContext___closed__1() -> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
    v___x_2478_ = lean_string_utf8_byte_size(v___x_2477_);
    return v___x_2478_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedInputContext___closed__2() -> *mut LeanObject {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    v___x_2479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__1_once),
        _init_l_Lean_Parser_instInhabitedInputContext___closed__1,
    );
    v___x_2480_ = l_Lean_instInhabitedFileMap_default;
    v___x_2481_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
    v___x_2482_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2482_, 0, v___x_2481_);
    lean_ctor_set(v___x_2482_, 1, v___x_2481_);
    lean_ctor_set(v___x_2482_, 2, v___x_2480_);
    lean_ctor_set(v___x_2482_, 3, v___x_2479_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedInputContext() -> *mut LeanObject {
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2483_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__2_once),
        _init_l_Lean_Parser_instInhabitedInputContext___closed__2,
    );
    return v___x_2483_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_mk___auto__1() -> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30,
    );
    return v___x_2484_;
}
pub unsafe fn l_Lean_Parser_InputContext_mk___redArg(
    mut v_input_2485_: *mut LeanObject,
    mut v_fileName_2486_: *mut LeanObject,
    mut v_endPos_2487_: *mut LeanObject,
    mut v_fileMap_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2489_, 0, v_input_2485_);
    lean_ctor_set(v___x_2489_, 1, v_fileName_2486_);
    lean_ctor_set(v___x_2489_, 2, v_fileMap_2488_);
    lean_ctor_set(v___x_2489_, 3, v_endPos_2487_);
    return v___x_2489_;
}
pub unsafe fn l_Lean_Parser_InputContext_mk(
    mut v_input_2490_: *mut LeanObject,
    mut v_fileName_2491_: *mut LeanObject,
    mut v_endPos_2492_: *mut LeanObject,
    mut v_endPos__valid_2493_: *mut LeanObject,
    mut v_fileMap_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    v___x_2495_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2495_, 0, v_input_2490_);
    lean_ctor_set(v___x_2495_, 1, v_fileName_2491_);
    lean_ctor_set(v___x_2495_, 2, v_fileMap_2494_);
    lean_ctor_set(v___x_2495_, 3, v_endPos_2492_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Parser_InputContext_input(mut v_c_2496_: *mut LeanObject) -> *mut LeanObject {
    let mut v_inputString_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v_inputString_2497_ = lean_ctor_get(v_c_2496_, 0);
    v_endPos_2498_ = lean_ctor_get(v_c_2496_, 3);
    v___x_2499_ = lean_unsigned_to_nat(0);
    v___x_2500_ = lean_string_utf8_extract(v_inputString_2497_, v___x_2499_, v_endPos_2498_);
    return v___x_2500_;
}
pub unsafe fn l_Lean_Parser_InputContext_input___boxed(
    mut v_c_2501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2502_: *mut LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Lean_Parser_InputContext_input(v_c_2501_);
    lean_dec_ref(v_c_2501_);
    return v_res_2502_;
}
pub unsafe fn l_Lean_Parser_InputContext_atEnd(
    mut v_c_2503_: *mut LeanObject,
    mut v_p_2504_: *mut LeanObject,
) -> u8 {
    let mut v_endPos_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: u8 = 0;
    v_endPos_2505_ = lean_ctor_get(v_c_2503_, 3);
    v___x_2506_ = lean_nat_dec_le(v_endPos_2505_, v_p_2504_);
    return v___x_2506_;
}
pub unsafe fn l_Lean_Parser_InputContext_atEnd___boxed(
    mut v_c_2507_: *mut LeanObject,
    mut v_p_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2509_: u8 = 0;
    let mut v_r_2510_: *mut LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Parser_InputContext_atEnd(v_c_2507_, v_p_2508_);
    lean_dec(v_p_2508_);
    lean_dec_ref(v_c_2507_);
    v_r_2510_ = lean_box((v_res_2509_) as usize);
    return v_r_2510_;
}
pub unsafe fn l_Lean_Parser_InputContext_get(
    mut v_c_2511_: *mut LeanObject,
    mut v_p_2512_: *mut LeanObject,
) -> u32 {
    let mut v_inputString_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u32 = 0;
    v_inputString_2513_ = lean_ctor_get(v_c_2511_, 0);
    v___x_2514_ = lean_string_utf8_get(v_inputString_2513_, v_p_2512_);
    return v___x_2514_;
}
pub unsafe fn l_Lean_Parser_InputContext_get___boxed(
    mut v_c_2515_: *mut LeanObject,
    mut v_p_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2517_: u32 = 0;
    let mut v_r_2518_: *mut LeanObject = core::ptr::null_mut();
    v_res_2517_ = l_Lean_Parser_InputContext_get(v_c_2515_, v_p_2516_);
    lean_dec(v_p_2516_);
    lean_dec_ref(v_c_2515_);
    v_r_2518_ = lean_box_uint32(v_res_2517_);
    return v_r_2518_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_2519_: *mut LeanObject,
    mut v_x_2520_: *mut LeanObject,
    mut v_h__1_2521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    v___x_2522_ = lean_apply_2(v_h__1_2521_, v_x_2519_, v_x_2520_);
    return v___x_2522_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_2523_: *mut LeanObject,
    mut v_x_2524_: *mut LeanObject,
    mut v_x_2525_: *mut LeanObject,
    mut v_h__1_2526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    v___x_2527_ = lean_apply_2(v_h__1_2526_, v_x_2524_, v_x_2525_);
    return v___x_2527_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27___redArg(
    mut v_c_2528_: *mut LeanObject,
    mut v_p_2529_: *mut LeanObject,
) -> u32 {
    let mut v_inputString_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u32 = 0;
    v_inputString_2530_ = lean_ctor_get(v_c_2528_, 0);
    v___x_2531_ = lean_string_utf8_get_fast(v_inputString_2530_, v_p_2529_);
    return v___x_2531_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27___redArg___boxed(
    mut v_c_2532_: *mut LeanObject,
    mut v_p_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2534_: u32 = 0;
    let mut v_r_2535_: *mut LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_2532_, v_p_2533_);
    lean_dec(v_p_2533_);
    lean_dec_ref(v_c_2532_);
    v_r_2535_ = lean_box_uint32(v_res_2534_);
    return v_r_2535_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27(
    mut v_c_2536_: *mut LeanObject,
    mut v_p_2537_: *mut LeanObject,
    mut v_h_2538_: *mut LeanObject,
) -> u32 {
    let mut v_inputString_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u32 = 0;
    v_inputString_2539_ = lean_ctor_get(v_c_2536_, 0);
    v___x_2540_ = lean_string_utf8_get_fast(v_inputString_2539_, v_p_2537_);
    return v___x_2540_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27___boxed(
    mut v_c_2541_: *mut LeanObject,
    mut v_p_2542_: *mut LeanObject,
    mut v_h_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2544_: u32 = 0;
    let mut v_r_2545_: *mut LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_Lean_Parser_InputContext_get_x27(v_c_2541_, v_p_2542_, v_h_2543_);
    lean_dec(v_p_2542_);
    lean_dec_ref(v_c_2541_);
    v_r_2545_ = lean_box_uint32(v_res_2544_);
    return v_r_2545_;
}
pub unsafe fn l_Lean_Parser_InputContext_next(
    mut v_c_2546_: *mut LeanObject,
    mut v_p_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inputString_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    v_inputString_2548_ = lean_ctor_get(v_c_2546_, 0);
    v___x_2549_ = lean_string_utf8_next(v_inputString_2548_, v_p_2547_);
    return v___x_2549_;
}
pub unsafe fn l_Lean_Parser_InputContext_next___boxed(
    mut v_c_2550_: *mut LeanObject,
    mut v_p_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2552_: *mut LeanObject = core::ptr::null_mut();
    v_res_2552_ = l_Lean_Parser_InputContext_next(v_c_2550_, v_p_2551_);
    lean_dec(v_p_2551_);
    lean_dec_ref(v_c_2550_);
    return v_res_2552_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27___redArg(
    mut v_c_2553_: *mut LeanObject,
    mut v_p_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inputString_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    v_inputString_2555_ = lean_ctor_get(v_c_2553_, 0);
    v___x_2556_ = lean_string_utf8_next_fast(v_inputString_2555_, v_p_2554_);
    return v___x_2556_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27___redArg___boxed(
    mut v_c_2557_: *mut LeanObject,
    mut v_p_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2559_: *mut LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_2557_, v_p_2558_);
    lean_dec(v_p_2558_);
    lean_dec_ref(v_c_2557_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27(
    mut v_c_2560_: *mut LeanObject,
    mut v_p_2561_: *mut LeanObject,
    mut v_h_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inputString_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    v_inputString_2563_ = lean_ctor_get(v_c_2560_, 0);
    v___x_2564_ = lean_string_utf8_next_fast(v_inputString_2563_, v_p_2561_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27___boxed(
    mut v_c_2565_: *mut LeanObject,
    mut v_p_2566_: *mut LeanObject,
    mut v_h_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2568_: *mut LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lean_Parser_InputContext_next_x27(v_c_2565_, v_p_2566_, v_h_2567_);
    lean_dec(v_p_2566_);
    lean_dec_ref(v_c_2565_);
    return v_res_2568_;
}
pub unsafe fn l_Lean_Parser_InputContext_extract(
    mut v_c_2569_: *mut LeanObject,
    mut v_a_2570_: *mut LeanObject,
    mut v_a_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inputString_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    v_inputString_2572_ = lean_ctor_get(v_c_2569_, 0);
    v___x_2573_ = lean_string_utf8_extract(v_inputString_2572_, v_a_2570_, v_a_2571_);
    return v___x_2573_;
}
pub unsafe fn l_Lean_Parser_InputContext_extract___boxed(
    mut v_c_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Lean_Parser_InputContext_extract(v_c_2574_, v_a_2575_, v_a_2576_);
    lean_dec(v_a_2576_);
    lean_dec(v_a_2575_);
    lean_dec_ref(v_c_2574_);
    return v_res_2577_;
}
pub unsafe fn l_Lean_Parser_InputContext_substring(
    mut v_c_2578_: *mut LeanObject,
    mut v_startPos_2579_: *mut LeanObject,
    mut v_stopPos_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inputString_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    v_inputString_2581_ = lean_ctor_get(v_c_2578_, 0);
    v_endPos_2582_ = lean_ctor_get(v_c_2578_, 3);
    v___x_2583_ = lean_nat_dec_le(v_stopPos_2580_, v_endPos_2582_);
    if v___x_2583_ == 0 {
        let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stopPos_2580_);
        lean_inc(v_endPos_2582_);
        lean_inc_ref(v_inputString_2581_);
        v___x_2584_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_2584_, 0, v_inputString_2581_);
        lean_ctor_set(v___x_2584_, 1, v_startPos_2579_);
        lean_ctor_set(v___x_2584_, 2, v_endPos_2582_);
        return v___x_2584_;
    } else {
        let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_inputString_2581_);
        v___x_2585_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_2585_, 0, v_inputString_2581_);
        lean_ctor_set(v___x_2585_, 1, v_startPos_2579_);
        lean_ctor_set(v___x_2585_, 2, v_stopPos_2580_);
        return v___x_2585_;
    }
}
pub unsafe fn l_Lean_Parser_InputContext_substring___boxed(
    mut v_c_2586_: *mut LeanObject,
    mut v_startPos_2587_: *mut LeanObject,
    mut v_stopPos_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2589_: *mut LeanObject = core::ptr::null_mut();
    v_res_2589_ =
        l_Lean_Parser_InputContext_substring(v_c_2586_, v_startPos_2587_, v_stopPos_2588_);
    lean_dec_ref(v_c_2586_);
    return v_res_2589_;
}
pub unsafe fn l_Lean_Parser_InputContext_getNext(
    mut v_input_2590_: *mut LeanObject,
    mut v_pos_2591_: *mut LeanObject,
) -> u32 {
    let mut v_inputString_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u32 = 0;
    v_inputString_2592_ = lean_ctor_get(v_input_2590_, 0);
    v___x_2593_ = lean_string_utf8_next(v_inputString_2592_, v_pos_2591_);
    v___x_2594_ = lean_string_utf8_get(v_inputString_2592_, v___x_2593_);
    lean_dec(v___x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_Parser_InputContext_getNext___boxed(
    mut v_input_2595_: *mut LeanObject,
    mut v_pos_2596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2597_: u32 = 0;
    let mut v_r_2598_: *mut LeanObject = core::ptr::null_mut();
    v_res_2597_ = l_Lean_Parser_InputContext_getNext(v_input_2595_, v_pos_2596_);
    lean_dec(v_pos_2596_);
    lean_dec_ref(v_input_2595_);
    v_r_2598_ = lean_box_uint32(v_res_2597_);
    return v_r_2598_;
}
pub unsafe fn l_Lean_Parser_InputContext_prev(
    mut v_c_2599_: *mut LeanObject,
    mut v_pos_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inputString_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    v_inputString_2601_ = lean_ctor_get(v_c_2599_, 0);
    v___x_2602_ = lean_string_utf8_prev(v_inputString_2601_, v_pos_2600_);
    return v___x_2602_;
}
pub unsafe fn l_Lean_Parser_InputContext_prev___boxed(
    mut v_c_2603_: *mut LeanObject,
    mut v_pos_2604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2605_: *mut LeanObject = core::ptr::null_mut();
    v_res_2605_ = l_Lean_Parser_InputContext_prev(v_c_2603_, v_pos_2604_);
    lean_dec(v_pos_2604_);
    lean_dec_ref(v_c_2603_);
    return v_res_2605_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(
    mut v_x_2606_: *mut LeanObject,
    mut v_x_2607_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2606_) == 0 {
        if lean_obj_tag(v_x_2607_) == 0 {
            let mut v___x_2608_: u8 = 0;
            v___x_2608_ = 1;
            return v___x_2608_;
        } else {
            let mut v___x_2609_: u8 = 0;
            v___x_2609_ = 0;
            return v___x_2609_;
        }
    } else {
        if lean_obj_tag(v_x_2607_) == 0 {
            let mut v___x_2610_: u8 = 0;
            v___x_2610_ = 0;
            return v___x_2610_;
        } else {
            let mut v_val_2611_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2612_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2613_: u8 = 0;
            v_val_2611_ = lean_ctor_get(v_x_2606_, 0);
            v_val_2612_ = lean_ctor_get(v_x_2607_, 0);
            v___x_2613_ = lean_nat_dec_eq(v_val_2611_, v_val_2612_);
            return v___x_2613_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0___boxed(
    mut v_x_2614_: *mut LeanObject,
    mut v_x_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2616_: u8 = 0;
    let mut v_r_2617_: *mut LeanObject = core::ptr::null_mut();
    v_res_2616_ =
        l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(
            v_x_2614_, v_x_2615_,
        );
    lean_dec(v_x_2615_);
    lean_dec(v_x_2614_);
    v_r_2617_ = lean_box((v_res_2616_) as usize);
    return v_r_2617_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(
    mut v_x_2618_: *mut LeanObject,
    mut v_x_2619_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2618_) == 0 {
        if lean_obj_tag(v_x_2619_) == 0 {
            let mut v___x_2620_: u8 = 0;
            v___x_2620_ = 1;
            return v___x_2620_;
        } else {
            let mut v___x_2621_: u8 = 0;
            v___x_2621_ = 0;
            return v___x_2621_;
        }
    } else {
        if lean_obj_tag(v_x_2619_) == 0 {
            let mut v___x_2622_: u8 = 0;
            v___x_2622_ = 0;
            return v___x_2622_;
        } else {
            let mut v_val_2623_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2624_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2625_: u8 = 0;
            v_val_2623_ = lean_ctor_get(v_x_2618_, 0);
            v_val_2624_ = lean_ctor_get(v_x_2619_, 0);
            v___x_2625_ = lean_string_dec_eq(v_val_2623_, v_val_2624_);
            return v___x_2625_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___boxed(
    mut v_x_2626_: *mut LeanObject,
    mut v_x_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2628_: u8 = 0;
    let mut v_r_2629_: *mut LeanObject = core::ptr::null_mut();
    v_res_2628_ =
        l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(
            v_x_2626_, v_x_2627_,
        );
    lean_dec(v_x_2627_);
    lean_dec(v_x_2626_);
    v_r_2629_ = lean_box((v_res_2628_) as usize);
    return v_r_2629_;
}
pub unsafe fn l_Lean_Parser_instBEqCacheableParserContext_beq(
    mut v_x_2630_: *mut LeanObject,
    mut v_x_2631_: *mut LeanObject,
) -> u8 {
    let mut v_prec_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotDepth_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressInsideQuot_2634_: u8 = 0;
    let mut v_savedPos_x3f_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenTk_x3f_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prec_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotDepth_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressInsideQuot_2639_: u8 = 0;
    let mut v_savedPos_x3f_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenTk_x3f_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: u8 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: u8 = 0;
    let mut v___x_2646_: u8 = 0;
    let mut v___x_2647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_prec_2632_ = lean_ctor_get(v_x_2630_, 0);
                v_quotDepth_2633_ = lean_ctor_get(v_x_2630_, 1);
                v_suppressInsideQuot_2634_ = lean_ctor_get_uint8(
                    v_x_2630_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_savedPos_x3f_2635_ = lean_ctor_get(v_x_2630_, 2);
                v_forbiddenTk_x3f_2636_ = lean_ctor_get(v_x_2630_, 3);
                v_prec_2637_ = lean_ctor_get(v_x_2631_, 0);
                v_quotDepth_2638_ = lean_ctor_get(v_x_2631_, 1);
                v_suppressInsideQuot_2639_ = lean_ctor_get_uint8(
                    v_x_2631_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_savedPos_x3f_2640_ = lean_ctor_get(v_x_2631_, 2);
                v_forbiddenTk_x3f_2641_ = lean_ctor_get(v_x_2631_, 3);
                v___x_2646_ = lean_nat_dec_eq(v_prec_2632_, v_prec_2637_);
                if v___x_2646_ == 0 {
                    return v___x_2646_;
                } else {
                    v___x_2647_ = lean_nat_dec_eq(v_quotDepth_2633_, v_quotDepth_2638_);
                    if v___x_2647_ == 0 {
                        return v___x_2647_;
                    } else {
                        if v_suppressInsideQuot_2634_ == 0 {
                            if v_suppressInsideQuot_2639_ == 0 {
                                v___y_2643_ = v___x_2647_;
                                state = 1;
                                continue;
                            } else {
                                return v_suppressInsideQuot_2634_;
                            }
                        } else {
                            v___y_2643_ = v_suppressInsideQuot_2639_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_2643_ == 0 {
                    return v___y_2643_;
                } else {
                    v___x_2644_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(v_savedPos_x3f_2635_, v_savedPos_x3f_2640_);
                    if v___x_2644_ == 0 {
                        return v___x_2644_;
                    } else {
                        v___x_2645_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(v_forbiddenTk_x3f_2636_, v_forbiddenTk_x3f_2641_);
                        return v___x_2645_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_instBEqCacheableParserContext_beq___boxed(
    mut v_x_2648_: *mut LeanObject,
    mut v_x_2649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2650_: u8 = 0;
    let mut v_r_2651_: *mut LeanObject = core::ptr::null_mut();
    v_res_2650_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_x_2648_, v_x_2649_);
    lean_dec_ref(v_x_2649_);
    lean_dec_ref(v_x_2648_);
    v_r_2651_ = lean_box((v_res_2650_) as usize);
    return v_r_2651_;
}
pub unsafe fn l_Lean_Parser_instCoeParserContextInputContext___lam__0(
    mut v_x_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_2655_: *mut LeanObject = core::ptr::null_mut();
    v_toInputContext_2655_ = lean_ctor_get(v_x_2654_, 0);
    lean_inc_ref(v_toInputContext_2655_);
    return v_toInputContext_2655_;
}
pub unsafe fn l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(
    mut v_x_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2657_: *mut LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_2656_);
    lean_dec_ref(v_x_2656_);
    return v_res_2657_;
}
pub unsafe fn l_Lean_Parser_ParserContext_setEndPos___redArg(
    mut v_c_2660_: *mut LeanObject,
    mut v_endPos_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toParserModuleContext_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tokens_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v_inputString_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2681_: u8 = 0;
    let mut v_unused_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2662_ = lean_ctor_get(v_c_2660_, 0);
                v_toParserModuleContext_2663_ = lean_ctor_get(v_c_2660_, 1);
                v_toCacheableParserContext_2664_ = lean_ctor_get(v_c_2660_, 2);
                v_tokens_2665_ = lean_ctor_get(v_c_2660_, 3);
                v_isSharedCheck_2683_ = (!lean_is_exclusive(v_c_2660_)) as u8;
                if v_isSharedCheck_2683_ == 0 {
                    v___x_2667_ = v_c_2660_;
                    v_isShared_2668_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tokens_2665_);
                    lean_inc(v_toCacheableParserContext_2664_);
                    lean_inc(v_toParserModuleContext_2663_);
                    lean_inc(v_toInputContext_2662_);
                    lean_dec(v_c_2660_);
                    v___x_2667_ = lean_box(0);
                    v_isShared_2668_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputString_2669_ = lean_ctor_get(v_toInputContext_2662_, 0);
                v_fileName_2670_ = lean_ctor_get(v_toInputContext_2662_, 1);
                v_fileMap_2671_ = lean_ctor_get(v_toInputContext_2662_, 2);
                v_isSharedCheck_2681_ = (!lean_is_exclusive(v_toInputContext_2662_)) as u8;
                if v_isSharedCheck_2681_ == 0 {
                    v_unused_2682_ = lean_ctor_get(v_toInputContext_2662_, 3);
                    lean_dec(v_unused_2682_);
                    v___x_2673_ = v_toInputContext_2662_;
                    v_isShared_2674_ = v_isSharedCheck_2681_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fileMap_2671_);
                    lean_inc(v_fileName_2670_);
                    lean_inc(v_inputString_2669_);
                    lean_dec(v_toInputContext_2662_);
                    v___x_2673_ = lean_box(0);
                    v_isShared_2674_ = v_isSharedCheck_2681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2674_ == 0 {
                    lean_ctor_set(v___x_2673_, 3, v_endPos_2661_);
                    v___x_2676_ = v___x_2673_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_inputString_2669_);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_fileName_2670_);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_fileMap_2671_);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_endPos_2661_);
                    v___x_2676_ = v_reuseFailAlloc_2680_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2668_ == 0 {
                    lean_ctor_set(v___x_2667_, 0, v___x_2676_);
                    v___x_2678_ = v___x_2667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
                    lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_toParserModuleContext_2663_);
                    lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_toCacheableParserContext_2664_);
                    lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_tokens_2665_);
                    v___x_2678_ = v_reuseFailAlloc_2679_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserContext_setEndPos(
    mut v_c_2684_: *mut LeanObject,
    mut v_endPos_2685_: *mut LeanObject,
    mut v_endPos__valid_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    v___x_2687_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_2684_, v_endPos_2685_);
    return v___x_2687_;
}
pub unsafe fn l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(
    mut v_x_2694_: *mut LeanObject,
    mut v_x_2695_: *mut LeanObject,
) -> u8 {
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2698_: u8 = 0;
    let mut v_head_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2694_) == 0 {
                    if lean_obj_tag(v_x_2695_) == 0 {
                        v___x_2696_ = 1;
                        return v___x_2696_;
                    } else {
                        v___x_2697_ = 0;
                        return v___x_2697_;
                    }
                } else {
                    if lean_obj_tag(v_x_2695_) == 0 {
                        v___x_2698_ = 0;
                        return v___x_2698_;
                    } else {
                        v_head_2699_ = lean_ctor_get(v_x_2694_, 0);
                        v_tail_2700_ = lean_ctor_get(v_x_2694_, 1);
                        v_head_2701_ = lean_ctor_get(v_x_2695_, 0);
                        v_tail_2702_ = lean_ctor_get(v_x_2695_, 1);
                        v___x_2703_ = lean_string_dec_eq(v_head_2699_, v_head_2701_);
                        if v___x_2703_ == 0 {
                            return v___x_2703_;
                        } else {
                            v_x_2694_ = v_tail_2700_;
                            v_x_2695_ = v_tail_2702_;
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
pub unsafe fn l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(
    mut v_x_2705_: *mut LeanObject,
    mut v_x_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2707_: u8 = 0;
    let mut v_r_2708_: *mut LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_2705_, v_x_2706_);
    lean_dec(v_x_2706_);
    lean_dec(v_x_2705_);
    v_r_2708_ = lean_box((v_res_2707_) as usize);
    return v_r_2708_;
}
pub unsafe fn l_Lean_Parser_instBEqError_beq(
    mut v_x_2709_: *mut LeanObject,
    mut v_x_2710_: *mut LeanObject,
) -> u8 {
    let mut v_unexpectedTk_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unexpected_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unexpectedTk_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unexpected_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    v_unexpectedTk_2711_ = lean_ctor_get(v_x_2709_, 0);
    lean_inc(v_unexpectedTk_2711_);
    v_unexpected_2712_ = lean_ctor_get(v_x_2709_, 1);
    lean_inc_ref(v_unexpected_2712_);
    v_expected_2713_ = lean_ctor_get(v_x_2709_, 2);
    lean_inc(v_expected_2713_);
    lean_dec_ref(v_x_2709_);
    v_unexpectedTk_2714_ = lean_ctor_get(v_x_2710_, 0);
    lean_inc(v_unexpectedTk_2714_);
    v_unexpected_2715_ = lean_ctor_get(v_x_2710_, 1);
    lean_inc_ref(v_unexpected_2715_);
    v_expected_2716_ = lean_ctor_get(v_x_2710_, 2);
    lean_inc(v_expected_2716_);
    lean_dec_ref(v_x_2710_);
    v___x_2717_ = l_Lean_Syntax_structEq(v_unexpectedTk_2711_, v_unexpectedTk_2714_);
    if v___x_2717_ == 0 {
        lean_dec(v_expected_2716_);
        lean_dec_ref(v_unexpected_2715_);
        lean_dec(v_expected_2713_);
        lean_dec_ref(v_unexpected_2712_);
        return v___x_2717_;
    } else {
        let mut v___x_2718_: u8 = 0;
        v___x_2718_ = lean_string_dec_eq(v_unexpected_2712_, v_unexpected_2715_);
        lean_dec_ref(v_unexpected_2715_);
        lean_dec_ref(v_unexpected_2712_);
        if v___x_2718_ == 0 {
            lean_dec(v_expected_2716_);
            lean_dec(v_expected_2713_);
            return v___x_2718_;
        } else {
            let mut v___x_2719_: u8 = 0;
            v___x_2719_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(
                v_expected_2713_,
                v_expected_2716_,
            );
            lean_dec(v_expected_2716_);
            lean_dec(v_expected_2713_);
            return v___x_2719_;
        }
    }
}
pub unsafe fn l_Lean_Parser_instBEqError_beq___boxed(
    mut v_x_2720_: *mut LeanObject,
    mut v_x_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2722_: u8 = 0;
    let mut v_r_2723_: *mut LeanObject = core::ptr::null_mut();
    v_res_2722_ = l_Lean_Parser_instBEqError_beq(v_x_2720_, v_x_2721_);
    v_r_2723_ = lean_box((v_res_2722_) as usize);
    return v_r_2723_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(
    mut v_x_2728_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2728_) == 0 {
        let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
        v___x_2729_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
        return v___x_2729_;
    } else {
        let mut v_tail_2730_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2730_ = lean_ctor_get(v_x_2728_, 1);
        if lean_obj_tag(v_tail_2730_) == 0 {
            let mut v_head_2731_: *mut LeanObject = core::ptr::null_mut();
            v_head_2731_ = lean_ctor_get(v_x_2728_, 0);
            lean_inc(v_head_2731_);
            lean_dec_ref_known(v_x_2728_, 2);
            return v_head_2731_;
        } else {
            let mut v_tail_2732_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_2730_);
            v_tail_2732_ = lean_ctor_get(v_tail_2730_, 1);
            if lean_obj_tag(v_tail_2732_) == 0 {
                let mut v_head_2733_: *mut LeanObject = core::ptr::null_mut();
                let mut v_head_2734_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
                v_head_2733_ = lean_ctor_get(v_x_2728_, 0);
                lean_inc(v_head_2733_);
                lean_dec_ref_known(v_x_2728_, 2);
                v_head_2734_ = lean_ctor_get(v_tail_2730_, 0);
                lean_inc(v_head_2734_);
                lean_dec_ref_known(v_tail_2730_, 2);
                v___x_2735_ =
                    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0;
                v___x_2736_ = lean_string_append(v_head_2733_, v___x_2735_);
                v___x_2737_ = lean_string_append(v___x_2736_, v_head_2734_);
                lean_dec(v_head_2734_);
                return v___x_2737_;
            } else {
                let mut v_head_2738_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
                v_head_2738_ = lean_ctor_get(v_x_2728_, 0);
                lean_inc(v_head_2738_);
                lean_dec_ref_known(v_x_2728_, 2);
                v___x_2739_ =
                    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1;
                v___x_2740_ = lean_string_append(v_head_2738_, v___x_2739_);
                v___x_2741_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(
                    v_tail_2730_,
                );
                v___x_2742_ = lean_string_append(v___x_2740_, v___x_2741_);
                lean_dec_ref(v___x_2741_);
                return v___x_2742_;
            }
        }
    }
}
pub unsafe fn l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(
    mut v_as_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v___f_2745_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0;
    v___x_2746_ = l_List_eraseRepsBy___redArg(v___f_2745_, v_as_2744_);
    return v___x_2746_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(
    mut v_hi_2747_: *mut LeanObject,
    mut v_pivot_2748_: *mut LeanObject,
    mut v_as_2749_: *mut LeanObject,
    mut v_i_2750_: *mut LeanObject,
    mut v_k_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2752_ = lean_nat_dec_lt(v_k_2751_, v_hi_2747_);
                if v___x_2752_ == 0 {
                    lean_dec(v_k_2751_);
                    v___x_2753_ = lean_array_fswap(v_as_2749_, v_i_2750_, v_hi_2747_);
                    v___x_2754_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2754_, 0, v_i_2750_);
                    lean_ctor_set(v___x_2754_, 1, v___x_2753_);
                    return v___x_2754_;
                } else {
                    v___x_2755_ = lean_array_fget_borrowed(v_as_2749_, v_k_2751_);
                    v___x_2756_ = lean_string_dec_lt(v___x_2755_, v_pivot_2748_);
                    if v___x_2756_ == 0 {
                        v___x_2757_ = lean_unsigned_to_nat(1);
                        v___x_2758_ = lean_nat_add(v_k_2751_, v___x_2757_);
                        lean_dec(v_k_2751_);
                        v_k_2751_ = v___x_2758_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2760_ = lean_array_fswap(v_as_2749_, v_i_2750_, v_k_2751_);
                        v___x_2761_ = lean_unsigned_to_nat(1);
                        v___x_2762_ = lean_nat_add(v_i_2750_, v___x_2761_);
                        lean_dec(v_i_2750_);
                        v___x_2763_ = lean_nat_add(v_k_2751_, v___x_2761_);
                        lean_dec(v_k_2751_);
                        v_as_2749_ = v___x_2760_;
                        v_i_2750_ = v___x_2762_;
                        v_k_2751_ = v___x_2763_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(
    mut v_hi_2765_: *mut LeanObject,
    mut v_pivot_2766_: *mut LeanObject,
    mut v_as_2767_: *mut LeanObject,
    mut v_i_2768_: *mut LeanObject,
    mut v_k_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2770_: *mut LeanObject = core::ptr::null_mut();
    v_res_2770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_2765_, v_pivot_2766_, v_as_2767_, v_i_2768_, v_k_2769_);
    lean_dec_ref(v_pivot_2766_);
    lean_dec(v_hi_2765_);
    return v_res_2770_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(
    mut v_n_2771_: *mut LeanObject,
    mut v_as_2772_: *mut LeanObject,
    mut v_lo_2773_: *mut LeanObject,
    mut v_hi_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: u8 = 0;
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2786_ = lean_nat_dec_lt(v_lo_2773_, v_hi_2774_);
                if v___x_2786_ == 0 {
                    lean_dec(v_lo_2773_);
                    return v_as_2772_;
                } else {
                    v___x_2787_ = lean_nat_add(v_lo_2773_, v_hi_2774_);
                    v___x_2788_ = lean_unsigned_to_nat(1);
                    v_mid_2789_ = lean_nat_shiftr(v___x_2787_, v___x_2788_);
                    lean_dec(v___x_2787_);
                    v___x_2802_ = lean_array_fget_borrowed(v_as_2772_, v_mid_2789_);
                    v___x_2803_ = lean_array_fget_borrowed(v_as_2772_, v_lo_2773_);
                    v___x_2804_ = lean_string_dec_lt(v___x_2802_, v___x_2803_);
                    if v___x_2804_ == 0 {
                        v___y_2797_ = v_as_2772_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2805_ = lean_array_fswap(v_as_2772_, v_lo_2773_, v_mid_2789_);
                        v___y_2797_ = v___x_2805_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2777_ = lean_array_fget(v___y_2776_, v_hi_2774_);
                lean_inc_n(v_lo_2773_, 2);
                v___x_2778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_2774_, v_pivot_2777_, v___y_2776_, v_lo_2773_, v_lo_2773_);
                lean_dec(v_pivot_2777_);
                v_fst_2779_ = lean_ctor_get(v___x_2778_, 0);
                lean_inc(v_fst_2779_);
                v_snd_2780_ = lean_ctor_get(v___x_2778_, 1);
                lean_inc(v_snd_2780_);
                lean_dec_ref(v___x_2778_);
                v___x_2781_ = lean_nat_dec_le(v_hi_2774_, v_fst_2779_);
                if v___x_2781_ == 0 {
                    v___x_2782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_2771_, v_snd_2780_, v_lo_2773_, v_fst_2779_);
                    v___x_2783_ = lean_unsigned_to_nat(1);
                    v___x_2784_ = lean_nat_add(v_fst_2779_, v___x_2783_);
                    lean_dec(v_fst_2779_);
                    v_as_2772_ = v___x_2782_;
                    v_lo_2773_ = v___x_2784_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_2779_);
                    lean_dec(v_lo_2773_);
                    return v_snd_2780_;
                }
            }
            2 => {
                v___x_2792_ = lean_array_fget_borrowed(v___y_2791_, v_mid_2789_);
                v___x_2793_ = lean_array_fget_borrowed(v___y_2791_, v_hi_2774_);
                v___x_2794_ = lean_string_dec_lt(v___x_2792_, v___x_2793_);
                if v___x_2794_ == 0 {
                    lean_dec(v_mid_2789_);
                    v___y_2776_ = v___y_2791_;
                    state = 1;
                    continue;
                } else {
                    v___x_2795_ = lean_array_fswap(v___y_2791_, v_mid_2789_, v_hi_2774_);
                    lean_dec(v_mid_2789_);
                    v___y_2776_ = v___x_2795_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2798_ = lean_array_fget_borrowed(v___y_2797_, v_hi_2774_);
                v___x_2799_ = lean_array_fget_borrowed(v___y_2797_, v_lo_2773_);
                v___x_2800_ = lean_string_dec_lt(v___x_2798_, v___x_2799_);
                if v___x_2800_ == 0 {
                    v___y_2791_ = v___y_2797_;
                    state = 2;
                    continue;
                } else {
                    v___x_2801_ = lean_array_fswap(v___y_2797_, v_lo_2773_, v_hi_2774_);
                    v___y_2791_ = v___x_2801_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(
    mut v_n_2806_: *mut LeanObject,
    mut v_as_2807_: *mut LeanObject,
    mut v_lo_2808_: *mut LeanObject,
    mut v_hi_2809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2810_: *mut LeanObject = core::ptr::null_mut();
    v_res_2810_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_2806_, v_as_2807_, v_lo_2808_, v_hi_2809_);
    lean_dec(v_hi_2809_);
    lean_dec(v_n_2806_);
    return v_res_2810_;
}
pub unsafe fn l_Lean_Parser_Error_toString(mut v_e_2813_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: u8 = 0;
    let mut v_unexpected_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_unexpected_2846_ = lean_ctor_get(v_e_2813_, 1);
                lean_inc_ref(v_unexpected_2846_);
                v_expected_2847_ = lean_ctor_get(v_e_2813_, 2);
                lean_inc(v_expected_2847_);
                lean_dec_ref(v_e_2813_);
                v___x_2859_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_2860_ = lean_string_dec_eq(v_unexpected_2846_, v___x_2859_);
                if v___x_2860_ == 0 {
                    v___x_2861_ = lean_box(0);
                    v___x_2862_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2862_, 0, v_unexpected_2846_);
                    lean_ctor_set(v___x_2862_, 1, v___x_2861_);
                    v___y_2849_ = v___x_2862_;
                    state = 5;
                    continue;
                } else {
                    lean_dec_ref(v_unexpected_2846_);
                    v___x_2863_ = lean_box(0);
                    v___y_2849_ = v___x_2863_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_2817_ = l_Lean_Parser_Error_toString___closed__0;
                v___x_2818_ = l_List_appendTR___redArg(v___y_2815_, v___y_2816_);
                v___x_2819_ = l_String_intercalate(v___x_2817_, v___x_2818_);
                return v___x_2819_;
            }
            2 => {
                v___x_2824_ = lean_array_to_list(v___y_2823_);
                v_expected_2825_ =
                    l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_2824_);
                v___x_2826_ = l_Lean_Parser_Error_toString___closed__1;
                v___x_2827_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(
                    v_expected_2825_,
                );
                v___x_2828_ = lean_string_append(v___x_2826_, v___x_2827_);
                lean_dec_ref(v___x_2827_);
                v___x_2829_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2829_, 0, v___x_2828_);
                lean_ctor_set(v___x_2829_, 1, v___y_2821_);
                v___y_2815_ = v___y_2822_;
                v___y_2816_ = v___x_2829_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2837_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_2835_, v___y_2831_, v___y_2834_, v___y_2836_);
                lean_dec(v___y_2836_);
                lean_dec(v___y_2835_);
                v___y_2821_ = v___y_2832_;
                v___y_2822_ = v___y_2833_;
                v___y_2823_ = v___x_2837_;
                state = 2;
                continue;
            }
            4 => {
                v___x_2845_ = lean_nat_dec_le(v___y_2844_, v___y_2839_);
                if v___x_2845_ == 0 {
                    lean_dec(v___y_2839_);
                    lean_inc(v___y_2844_);
                    v___y_2831_ = v___y_2840_;
                    v___y_2832_ = v___y_2841_;
                    v___y_2833_ = v___y_2842_;
                    v___y_2834_ = v___y_2844_;
                    v___y_2835_ = v___y_2843_;
                    v___y_2836_ = v___y_2844_;
                    state = 3;
                    continue;
                } else {
                    v___y_2831_ = v___y_2840_;
                    v___y_2832_ = v___y_2841_;
                    v___y_2833_ = v___y_2842_;
                    v___y_2834_ = v___y_2844_;
                    v___y_2835_ = v___y_2843_;
                    v___y_2836_ = v___y_2839_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_2850_ = lean_box(0);
                v___x_2851_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(
                    v_expected_2847_,
                    v___x_2850_,
                );
                if v___x_2851_ == 0 {
                    v___x_2852_ = lean_array_mk(v_expected_2847_);
                    v___x_2853_ = lean_array_get_size(v___x_2852_);
                    v___x_2854_ = lean_unsigned_to_nat(0);
                    v___x_2855_ = lean_nat_dec_eq(v___x_2853_, v___x_2854_);
                    if v___x_2855_ == 0 {
                        v___x_2856_ = lean_unsigned_to_nat(1);
                        v___x_2857_ = lean_nat_sub(v___x_2853_, v___x_2856_);
                        v___x_2858_ = lean_nat_dec_le(v___x_2854_, v___x_2857_);
                        if v___x_2858_ == 0 {
                            lean_inc(v___x_2857_);
                            v___y_2839_ = v___x_2857_;
                            v___y_2840_ = v___x_2852_;
                            v___y_2841_ = v___x_2850_;
                            v___y_2842_ = v___y_2849_;
                            v___y_2843_ = v___x_2853_;
                            v___y_2844_ = v___x_2857_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2839_ = v___x_2857_;
                            v___y_2840_ = v___x_2852_;
                            v___y_2841_ = v___x_2850_;
                            v___y_2842_ = v___y_2849_;
                            v___y_2843_ = v___x_2853_;
                            v___y_2844_ = v___x_2854_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_2821_ = v___x_2850_;
                        v___y_2822_ = v___y_2849_;
                        v___y_2823_ = v___x_2852_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_expected_2847_);
                    v___y_2815_ = v___y_2849_;
                    v___y_2816_ = v___x_2850_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(
    mut v_n_2864_: *mut LeanObject,
    mut v_as_2865_: *mut LeanObject,
    mut v_lo_2866_: *mut LeanObject,
    mut v_hi_2867_: *mut LeanObject,
    mut v_w_2868_: *mut LeanObject,
    mut v_hlo_2869_: *mut LeanObject,
    mut v_hhi_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    v___x_2871_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_2864_, v_as_2865_, v_lo_2866_, v_hi_2867_);
    return v___x_2871_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(
    mut v_n_2872_: *mut LeanObject,
    mut v_as_2873_: *mut LeanObject,
    mut v_lo_2874_: *mut LeanObject,
    mut v_hi_2875_: *mut LeanObject,
    mut v_w_2876_: *mut LeanObject,
    mut v_hlo_2877_: *mut LeanObject,
    mut v_hhi_2878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2879_: *mut LeanObject = core::ptr::null_mut();
    v_res_2879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_2872_, v_as_2873_, v_lo_2874_, v_hi_2875_, v_w_2876_, v_hlo_2877_, v_hhi_2878_);
    lean_dec(v_hi_2875_);
    lean_dec(v_n_2872_);
    return v_res_2879_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(
    mut v_n_2880_: *mut LeanObject,
    mut v_lo_2881_: *mut LeanObject,
    mut v_hi_2882_: *mut LeanObject,
    mut v_hhi_2883_: *mut LeanObject,
    mut v_pivot_2884_: *mut LeanObject,
    mut v_as_2885_: *mut LeanObject,
    mut v_i_2886_: *mut LeanObject,
    mut v_k_2887_: *mut LeanObject,
    mut v_ilo_2888_: *mut LeanObject,
    mut v_ik_2889_: *mut LeanObject,
    mut v_w_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    v___x_2891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_2882_, v_pivot_2884_, v_as_2885_, v_i_2886_, v_k_2887_);
    return v___x_2891_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(
    mut v_n_2892_: *mut LeanObject,
    mut v_lo_2893_: *mut LeanObject,
    mut v_hi_2894_: *mut LeanObject,
    mut v_hhi_2895_: *mut LeanObject,
    mut v_pivot_2896_: *mut LeanObject,
    mut v_as_2897_: *mut LeanObject,
    mut v_i_2898_: *mut LeanObject,
    mut v_k_2899_: *mut LeanObject,
    mut v_ilo_2900_: *mut LeanObject,
    mut v_ik_2901_: *mut LeanObject,
    mut v_w_2902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2903_: *mut LeanObject = core::ptr::null_mut();
    v_res_2903_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_2892_, v_lo_2893_, v_hi_2894_, v_hhi_2895_, v_pivot_2896_, v_as_2897_, v_i_2898_, v_k_2899_, v_ilo_2900_, v_ik_2901_, v_w_2902_);
    lean_dec_ref(v_pivot_2896_);
    lean_dec(v_hi_2894_);
    lean_dec(v_lo_2893_);
    lean_dec(v_n_2892_);
    return v_res_2903_;
}
pub unsafe fn l_Lean_Parser_Error_merge(
    mut v_e_u2081_2906_: *mut LeanObject,
    mut v_e_u2082_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_unexpectedTk_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unexpected_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v_unused_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v_unexpected_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_unexpectedTk_2908_ = lean_ctor_get(v_e_u2082_2907_, 0);
                lean_inc(v_unexpectedTk_2908_);
                v_unexpected_2909_ = lean_ctor_get(v_e_u2082_2907_, 1);
                lean_inc_ref(v_unexpected_2909_);
                v_expected_2910_ = lean_ctor_get(v_e_u2082_2907_, 2);
                lean_inc(v_expected_2910_);
                lean_dec_ref(v_e_u2082_2907_);
                v___x_2924_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_2925_ = lean_string_dec_eq(v_unexpected_2909_, v___x_2924_);
                if v___x_2925_ == 0 {
                    v___y_2912_ = v_unexpected_2909_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_unexpected_2909_);
                    v_unexpected_2926_ = lean_ctor_get(v_e_u2081_2906_, 1);
                    lean_inc_ref(v_unexpected_2926_);
                    v___y_2912_ = v_unexpected_2926_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_expected_2913_ = lean_ctor_get(v_e_u2081_2906_, 2);
                v_isSharedCheck_2921_ = (!lean_is_exclusive(v_e_u2081_2906_)) as u8;
                if v_isSharedCheck_2921_ == 0 {
                    v_unused_2922_ = lean_ctor_get(v_e_u2081_2906_, 1);
                    lean_dec(v_unused_2922_);
                    v_unused_2923_ = lean_ctor_get(v_e_u2081_2906_, 0);
                    lean_dec(v_unused_2923_);
                    v___x_2915_ = v_e_u2081_2906_;
                    v_isShared_2916_ = v_isSharedCheck_2921_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_expected_2913_);
                    lean_dec(v_e_u2081_2906_);
                    v___x_2915_ = lean_box(0);
                    v_isShared_2916_ = v_isSharedCheck_2921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2917_ = l_List_appendTR___redArg(v_expected_2913_, v_expected_2910_);
                if v_isShared_2916_ == 0 {
                    lean_ctor_set(v___x_2915_, 2, v___x_2917_);
                    lean_ctor_set(v___x_2915_, 1, v___y_2912_);
                    lean_ctor_set(v___x_2915_, 0, v_unexpectedTk_2908_);
                    v___x_2919_ = v___x_2915_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_unexpectedTk_2908_);
                    lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___y_2912_);
                    lean_ctor_set(v_reuseFailAlloc_2920_, 2, v___x_2917_);
                    v___x_2919_ = v_reuseFailAlloc_2920_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_instBEqParserCacheKey_beq(
    mut v_x_2927_: *mut LeanObject,
    mut v_x_2928_: *mut LeanObject,
) -> u8 {
    let mut v_toCacheableParserContext_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parserName_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parserName_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: u8 = 0;
    v_toCacheableParserContext_2929_ = lean_ctor_get(v_x_2927_, 0);
    v_parserName_2930_ = lean_ctor_get(v_x_2927_, 1);
    v_pos_2931_ = lean_ctor_get(v_x_2927_, 2);
    v_toCacheableParserContext_2932_ = lean_ctor_get(v_x_2928_, 0);
    v_parserName_2933_ = lean_ctor_get(v_x_2928_, 1);
    v_pos_2934_ = lean_ctor_get(v_x_2928_, 2);
    v___x_2935_ = l_Lean_Parser_instBEqCacheableParserContext_beq(
        v_toCacheableParserContext_2929_,
        v_toCacheableParserContext_2932_,
    );
    if v___x_2935_ == 0 {
        return v___x_2935_;
    } else {
        let mut v___x_2936_: u8 = 0;
        v___x_2936_ = lean_name_eq(v_parserName_2930_, v_parserName_2933_);
        if v___x_2936_ == 0 {
            return v___x_2936_;
        } else {
            let mut v___x_2937_: u8 = 0;
            v___x_2937_ = lean_nat_dec_eq(v_pos_2931_, v_pos_2934_);
            return v___x_2937_;
        }
    }
}
pub unsafe fn l_Lean_Parser_instBEqParserCacheKey_beq___boxed(
    mut v_x_2938_: *mut LeanObject,
    mut v_x_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2940_: u8 = 0;
    let mut v_r_2941_: *mut LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_2938_, v_x_2939_);
    lean_dec_ref(v_x_2939_);
    lean_dec_ref(v_x_2938_);
    v_r_2941_ = lean_box((v_res_2940_) as usize);
    return v_r_2941_;
}
pub unsafe fn l_Lean_Parser_instHashableParserCacheKey___lam__0(
    mut v_k_2944_: *mut LeanObject,
) -> u64 {
    let mut v_parserName_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: u64 = 0;
    v_parserName_2945_ = lean_ctor_get(v_k_2944_, 1);
    v_pos_2946_ = lean_ctor_get(v_k_2944_, 2);
    v___x_2947_ = l_String_instHashableRaw_hash(v_pos_2946_);
    if lean_obj_tag(v_parserName_2945_) == 0 {
        let mut v___x_2948_: u64 = 0;
        let mut v___x_2949_: u64 = 0;
        v___x_2948_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
        v___x_2949_ = lean_uint64_mix_hash(v___x_2947_, v___x_2948_);
        return v___x_2949_;
    } else {
        let mut v_hash_2950_: u64 = 0;
        let mut v___x_2951_: u64 = 0;
        v_hash_2950_ = lean_ctor_get_uint64(
            v_parserName_2945_,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        );
        v___x_2951_ = lean_uint64_mix_hash(v___x_2947_, v_hash_2950_);
        return v___x_2951_;
    }
}
pub unsafe fn l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(
    mut v_k_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2953_: u64 = 0;
    let mut v_r_2954_: *mut LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_2952_);
    lean_dec_ref(v_k_2952_);
    v_r_2954_ = lean_box_uint64(v_res_2953_);
    return v_r_2954_;
}
pub unsafe fn _init_l_Lean_Parser_initCacheForInput___closed__0() -> *mut LeanObject {
    let mut v___x_2957_: u32 = 0;
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    v___x_2957_ = 32;
    v___x_2958_ = l_Char_utf8Size(v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn _init_l_Lean_Parser_initCacheForInput___closed__1() -> *mut LeanObject {
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = lean_box(0);
    v___x_2960_ = lean_unsigned_to_nat(16);
    v___x_2961_ = lean_mk_array(v___x_2960_, v___x_2959_);
    return v___x_2961_;
}
pub unsafe fn _init_l_Lean_Parser_initCacheForInput___closed__2() -> *mut LeanObject {
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    v___x_2962_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__1_once),
        _init_l_Lean_Parser_initCacheForInput___closed__1,
    );
    v___x_2963_ = lean_unsigned_to_nat(0);
    v___x_2964_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2964_, 0, v___x_2963_);
    lean_ctor_set(v___x_2964_, 1, v___x_2962_);
    return v___x_2964_;
}
pub unsafe fn l_Lean_Parser_initCacheForInput(
    mut v_input_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    v___x_2966_ = lean_string_utf8_byte_size(v_input_2965_);
    v___x_2967_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__0_once),
        _init_l_Lean_Parser_initCacheForInput___closed__0,
    );
    v___x_2968_ = lean_nat_add(v___x_2966_, v___x_2967_);
    v___x_2969_ = lean_unsigned_to_nat(0);
    v___x_2970_ = lean_box(0);
    v___x_2971_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2971_, 0, v___x_2968_);
    lean_ctor_set(v___x_2971_, 1, v___x_2969_);
    lean_ctor_set(v___x_2971_, 2, v___x_2970_);
    v___x_2972_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2_once),
        _init_l_Lean_Parser_initCacheForInput___closed__2,
    );
    v___x_2973_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2973_, 0, v___x_2971_);
    lean_ctor_set(v___x_2973_, 1, v___x_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Lean_Parser_initCacheForInput___boxed(
    mut v_input_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2975_: *mut LeanObject = core::ptr::null_mut();
    v_res_2975_ = l_Lean_Parser_initCacheForInput(v_input_2974_);
    lean_dec_ref(v_input_2974_);
    return v_res_2975_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_toSubarray(
    mut v_stack_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_raw_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    v_raw_2977_ = lean_ctor_get(v_stack_2976_, 0);
    lean_inc_ref(v_raw_2977_);
    v_drop_2978_ = lean_ctor_get(v_stack_2976_, 1);
    lean_inc(v_drop_2978_);
    lean_dec_ref(v_stack_2976_);
    v___x_2979_ = lean_array_get_size(v_raw_2977_);
    v___x_2980_ = l_Array_toSubarray___redArg(v_raw_2977_, v_drop_2978_, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_size(
    mut v_stack_2987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_raw_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    v_raw_2988_ = lean_ctor_get(v_stack_2987_, 0);
    v_drop_2989_ = lean_ctor_get(v_stack_2987_, 1);
    v___x_2990_ = lean_array_get_size(v_raw_2988_);
    v___x_2991_ = lean_nat_sub(v___x_2990_, v_drop_2989_);
    return v___x_2991_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_size___boxed(
    mut v_stack_2992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2993_: *mut LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Lean_Parser_SyntaxStack_size(v_stack_2992_);
    lean_dec_ref(v_stack_2992_);
    return v_res_2993_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_isEmpty(mut v_stack_2994_: *mut LeanObject) -> u8 {
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    v___x_2995_ = l_Lean_Parser_SyntaxStack_size(v_stack_2994_);
    v___x_2996_ = lean_unsigned_to_nat(0);
    v___x_2997_ = lean_nat_dec_eq(v___x_2995_, v___x_2996_);
    lean_dec(v___x_2995_);
    return v___x_2997_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_isEmpty___boxed(
    mut v_stack_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: u8 = 0;
    let mut v_r_3000_: *mut LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_2998_);
    lean_dec_ref(v_stack_2998_);
    v_r_3000_ = lean_box((v_res_2999_) as usize);
    return v_r_3000_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_shrink(
    mut v_stack_3001_: *mut LeanObject,
    mut v_n_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_raw_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3007_: u8 = 0;
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3003_ = lean_ctor_get(v_stack_3001_, 0);
                v_drop_3004_ = lean_ctor_get(v_stack_3001_, 1);
                v_isSharedCheck_3013_ = (!lean_is_exclusive(v_stack_3001_)) as u8;
                if v_isSharedCheck_3013_ == 0 {
                    v___x_3006_ = v_stack_3001_;
                    v_isShared_3007_ = v_isSharedCheck_3013_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_drop_3004_);
                    lean_inc(v_raw_3003_);
                    lean_dec(v_stack_3001_);
                    v___x_3006_ = lean_box(0);
                    v_isShared_3007_ = v_isSharedCheck_3013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3008_ = lean_nat_add(v_drop_3004_, v_n_3002_);
                v___x_3009_ = l_Array_shrink___redArg(v_raw_3003_, v___x_3008_);
                lean_dec(v___x_3008_);
                if v_isShared_3007_ == 0 {
                    lean_ctor_set(v___x_3006_, 0, v___x_3009_);
                    v___x_3011_ = v___x_3006_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_drop_3004_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_shrink___boxed(
    mut v_stack_3014_: *mut LeanObject,
    mut v_n_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3016_: *mut LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_3014_, v_n_3015_);
    lean_dec(v_n_3015_);
    return v_res_3016_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_push(
    mut v_stack_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_raw_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3019_ = lean_ctor_get(v_stack_3017_, 0);
                v_drop_3020_ = lean_ctor_get(v_stack_3017_, 1);
                v_isSharedCheck_3028_ = (!lean_is_exclusive(v_stack_3017_)) as u8;
                if v_isSharedCheck_3028_ == 0 {
                    v___x_3022_ = v_stack_3017_;
                    v_isShared_3023_ = v_isSharedCheck_3028_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_drop_3020_);
                    lean_inc(v_raw_3019_);
                    lean_dec(v_stack_3017_);
                    v___x_3022_ = lean_box(0);
                    v_isShared_3023_ = v_isSharedCheck_3028_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3024_ = lean_array_push(v_raw_3019_, v_a_3018_);
                if v_isShared_3023_ == 0 {
                    lean_ctor_set(v___x_3022_, 0, v___x_3024_);
                    v___x_3026_ = v___x_3022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_drop_3020_);
                    v___x_3026_ = v_reuseFailAlloc_3027_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_pop(mut v_stack_3029_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v_raw_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3030_ = lean_unsigned_to_nat(0);
                v___x_3031_ = l_Lean_Parser_SyntaxStack_size(v_stack_3029_);
                v___x_3032_ = lean_nat_dec_lt(v___x_3030_, v___x_3031_);
                lean_dec(v___x_3031_);
                if v___x_3032_ == 0 {
                    return v_stack_3029_;
                } else {
                    v_raw_3033_ = lean_ctor_get(v_stack_3029_, 0);
                    v_drop_3034_ = lean_ctor_get(v_stack_3029_, 1);
                    v_isSharedCheck_3042_ = (!lean_is_exclusive(v_stack_3029_)) as u8;
                    if v_isSharedCheck_3042_ == 0 {
                        v___x_3036_ = v_stack_3029_;
                        v_isShared_3037_ = v_isSharedCheck_3042_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_drop_3034_);
                        lean_inc(v_raw_3033_);
                        lean_dec(v_stack_3029_);
                        v___x_3036_ = lean_box(0);
                        v_isShared_3037_ = v_isSharedCheck_3042_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3038_ = lean_array_pop(v_raw_3033_);
                if v_isShared_3037_ == 0 {
                    lean_ctor_set(v___x_3036_, 0, v___x_3038_);
                    v___x_3040_ = v___x_3036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
                    lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_drop_3034_);
                    v___x_3040_ = v_reuseFailAlloc_3041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(
    mut v_msg_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    v___x_3044_ = lean_box(0);
    v___x_3045_ = lean_panic_fn_borrowed(v___x_3044_, v_msg_3043_);
    return v___x_3045_;
}
pub unsafe fn _init_l_Lean_Parser_SyntaxStack_back___closed__3() -> *mut LeanObject {
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    v___x_3049_ = l_Lean_Parser_SyntaxStack_back___closed__2;
    v___x_3050_ = lean_unsigned_to_nat(4);
    v___x_3051_ = lean_unsigned_to_nat(305);
    v___x_3052_ = l_Lean_Parser_SyntaxStack_back___closed__1;
    v___x_3053_ = l_Lean_Parser_SyntaxStack_back___closed__0;
    v___x_3054_ = l_mkPanicMessageWithDecl(
        v___x_3053_,
        v___x_3052_,
        v___x_3051_,
        v___x_3050_,
        v___x_3049_,
    );
    return v___x_3054_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_back(
    mut v_stack_3055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: u8 = 0;
    v___x_3056_ = lean_unsigned_to_nat(0);
    v___x_3057_ = l_Lean_Parser_SyntaxStack_size(v_stack_3055_);
    v___x_3058_ = lean_nat_dec_lt(v___x_3056_, v___x_3057_);
    lean_dec(v___x_3057_);
    if v___x_3058_ == 0 {
        let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
        v___x_3059_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_back___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_back___closed__3_once),
            _init_l_Lean_Parser_SyntaxStack_back___closed__3,
        );
        v___x_3060_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_3059_);
        return v___x_3060_;
    } else {
        let mut v_raw_3061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
        v_raw_3061_ = lean_ctor_get(v_stack_3055_, 0);
        v___x_3062_ = lean_box(0);
        v___x_3063_ = lean_array_get_size(v_raw_3061_);
        v___x_3064_ = lean_unsigned_to_nat(1);
        v___x_3065_ = lean_nat_sub(v___x_3063_, v___x_3064_);
        v___x_3066_ = lean_array_get_borrowed(v___x_3062_, v_raw_3061_, v___x_3065_);
        lean_dec(v___x_3065_);
        lean_inc(v___x_3066_);
        return v___x_3066_;
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_back___boxed(
    mut v_stack_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3068_: *mut LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Lean_Parser_SyntaxStack_back(v_stack_3067_);
    lean_dec_ref(v_stack_3067_);
    return v_res_3068_;
}
pub unsafe fn _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2() -> *mut LeanObject {
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    v___x_3071_ = l_Lean_Parser_SyntaxStack_get_x21___closed__1;
    v___x_3072_ = lean_unsigned_to_nat(4);
    v___x_3073_ = lean_unsigned_to_nat(311);
    v___x_3074_ = l_Lean_Parser_SyntaxStack_get_x21___closed__0;
    v___x_3075_ = l_Lean_Parser_SyntaxStack_back___closed__0;
    v___x_3076_ = l_mkPanicMessageWithDecl(
        v___x_3075_,
        v___x_3074_,
        v___x_3073_,
        v___x_3072_,
        v___x_3071_,
    );
    return v___x_3076_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_get_x21(
    mut v_stack_3077_: *mut LeanObject,
    mut v_i_3078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: u8 = 0;
    v___x_3079_ = l_Lean_Parser_SyntaxStack_size(v_stack_3077_);
    v___x_3080_ = lean_nat_dec_lt(v_i_3078_, v___x_3079_);
    lean_dec(v___x_3079_);
    if v___x_3080_ == 0 {
        let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
        v___x_3081_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_get_x21___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_get_x21___closed__2_once),
            _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2,
        );
        v___x_3082_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_3081_);
        return v___x_3082_;
    } else {
        let mut v_raw_3083_: *mut LeanObject = core::ptr::null_mut();
        let mut v_drop_3084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
        v_raw_3083_ = lean_ctor_get(v_stack_3077_, 0);
        v_drop_3084_ = lean_ctor_get(v_stack_3077_, 1);
        v___x_3085_ = lean_box(0);
        v___x_3086_ = lean_nat_add(v_drop_3084_, v_i_3078_);
        v___x_3087_ = lean_array_get_borrowed(v___x_3085_, v_raw_3083_, v___x_3086_);
        lean_dec(v___x_3086_);
        lean_inc(v___x_3087_);
        return v___x_3087_;
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_get_x21___boxed(
    mut v_stack_3088_: *mut LeanObject,
    mut v_i_3089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3090_: *mut LeanObject = core::ptr::null_mut();
    v_res_3090_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_3088_, v_i_3089_);
    lean_dec(v_i_3089_);
    lean_dec_ref(v_stack_3088_);
    return v_res_3090_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_extract(
    mut v_stack_3091_: *mut LeanObject,
    mut v_start_3092_: *mut LeanObject,
    mut v_stop_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_raw_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    v_raw_3094_ = lean_ctor_get(v_stack_3091_, 0);
    v_drop_3095_ = lean_ctor_get(v_stack_3091_, 1);
    v___x_3096_ = lean_nat_add(v_drop_3095_, v_start_3092_);
    v___x_3097_ = lean_nat_add(v_drop_3095_, v_stop_3093_);
    v___x_3098_ = l_Array_extract___redArg(v_raw_3094_, v___x_3096_, v___x_3097_);
    return v___x_3098_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_extract___boxed(
    mut v_stack_3099_: *mut LeanObject,
    mut v_start_3100_: *mut LeanObject,
    mut v_stop_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3102_: *mut LeanObject = core::ptr::null_mut();
    v_res_3102_ = l_Lean_Parser_SyntaxStack_extract(v_stack_3099_, v_start_3100_, v_stop_3101_);
    lean_dec(v_stop_3101_);
    lean_dec(v_start_3100_);
    lean_dec_ref(v_stack_3099_);
    return v_res_3102_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(
    mut v_stack_3103_: *mut LeanObject,
    mut v_stxs_3104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_raw_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3105_ = lean_ctor_get(v_stack_3103_, 0);
                v_drop_3106_ = lean_ctor_get(v_stack_3103_, 1);
                v_isSharedCheck_3114_ = (!lean_is_exclusive(v_stack_3103_)) as u8;
                if v_isSharedCheck_3114_ == 0 {
                    v___x_3108_ = v_stack_3103_;
                    v_isShared_3109_ = v_isSharedCheck_3114_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_drop_3106_);
                    lean_inc(v_raw_3105_);
                    lean_dec(v_stack_3103_);
                    v___x_3108_ = lean_box(0);
                    v_isShared_3109_ = v_isSharedCheck_3114_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3110_ = l_Array_append___redArg(v_raw_3105_, v_stxs_3104_);
                if v_isShared_3109_ == 0 {
                    lean_ctor_set(v___x_3108_, 0, v___x_3110_);
                    v___x_3112_ = v___x_3108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_drop_3106_);
                    v___x_3112_ = v_reuseFailAlloc_3113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(
    mut v_stack_3115_: *mut LeanObject,
    mut v_stxs_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3117_: *mut LeanObject = core::ptr::null_mut();
    v_res_3117_ =
        l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_3115_, v_stxs_3116_);
    lean_dec_ref(v_stxs_3116_);
    return v_res_3117_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(
    mut v_stack_3118_: *mut LeanObject,
    mut v_stxs_3119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_raw_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3120_ = lean_ctor_get(v_stack_3118_, 0);
                v_drop_3121_ = lean_ctor_get(v_stack_3118_, 1);
                v_isSharedCheck_3129_ = (!lean_is_exclusive(v_stack_3118_)) as u8;
                if v_isSharedCheck_3129_ == 0 {
                    v___x_3123_ = v_stack_3118_;
                    v_isShared_3124_ = v_isSharedCheck_3129_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_drop_3121_);
                    lean_inc(v_raw_3120_);
                    lean_dec(v_stack_3118_);
                    v___x_3123_ = lean_box(0);
                    v_isShared_3124_ = v_isSharedCheck_3129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3125_ = l_Array_append___redArg(v_raw_3120_, v_stxs_3119_);
                if v_isShared_3124_ == 0 {
                    lean_ctor_set(v___x_3123_, 0, v___x_3125_);
                    v___x_3127_ = v___x_3123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
                    lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_drop_3121_);
                    v___x_3127_ = v_reuseFailAlloc_3128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(
    mut v_stack_3130_: *mut LeanObject,
    mut v_stxs_3131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3132_: *mut LeanObject = core::ptr::null_mut();
    v_res_3132_ =
        l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_3130_, v_stxs_3131_);
    lean_dec_ref(v_stxs_3131_);
    return v_res_3132_;
}
pub unsafe fn l_Lean_Parser_ParserState_hasError(mut v_s_3135_: *mut LeanObject) -> u8 {
    let mut v_errorMsg_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    v_errorMsg_3136_ = lean_ctor_get(v_s_3135_, 4);
    lean_inc(v_errorMsg_3136_);
    lean_dec_ref(v_s_3135_);
    v___x_3137_ = l_Lean_Parser_instBEqError___closed__0;
    v___x_3138_ = lean_box(0);
    v___x_3139_ = l_Option_instBEq_beq___redArg(v___x_3137_, v_errorMsg_3136_, v___x_3138_);
    if v___x_3139_ == 0 {
        let mut v___x_3140_: u8 = 0;
        v___x_3140_ = 1;
        return v___x_3140_;
    } else {
        let mut v___x_3141_: u8 = 0;
        v___x_3141_ = 0;
        return v___x_3141_;
    }
}
pub unsafe fn l_Lean_Parser_ParserState_hasError___boxed(
    mut v_s_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3143_: u8 = 0;
    let mut v_r_3144_: *mut LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Lean_Parser_ParserState_hasError(v_s_3142_);
    v_r_3144_ = lean_box((v_res_3143_) as usize);
    return v_r_3144_;
}
pub unsafe fn l_Lean_Parser_ParserState_stackSize(
    mut v_s_3145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    v_stxStack_3146_ = lean_ctor_get(v_s_3145_, 0);
    v___x_3147_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3146_);
    return v___x_3147_;
}
pub unsafe fn l_Lean_Parser_ParserState_stackSize___boxed(
    mut v_s_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3149_: *mut LeanObject = core::ptr::null_mut();
    v_res_3149_ = l_Lean_Parser_ParserState_stackSize(v_s_3148_);
    lean_dec_ref(v_s_3148_);
    return v_res_3149_;
}
pub unsafe fn l_Lean_Parser_ParserState_restore(
    mut v_s_3150_: *mut LeanObject,
    mut v_iniStackSz_3151_: *mut LeanObject,
    mut v_iniPos_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v_unused_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3153_ = lean_ctor_get(v_s_3150_, 0);
                v_lhsPrec_3154_ = lean_ctor_get(v_s_3150_, 1);
                v_cache_3155_ = lean_ctor_get(v_s_3150_, 3);
                v_recoveredErrors_3156_ = lean_ctor_get(v_s_3150_, 5);
                v_isSharedCheck_3165_ = (!lean_is_exclusive(v_s_3150_)) as u8;
                if v_isSharedCheck_3165_ == 0 {
                    v_unused_3166_ = lean_ctor_get(v_s_3150_, 4);
                    lean_dec(v_unused_3166_);
                    v_unused_3167_ = lean_ctor_get(v_s_3150_, 2);
                    lean_dec(v_unused_3167_);
                    v___x_3158_ = v_s_3150_;
                    v_isShared_3159_ = v_isSharedCheck_3165_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3156_);
                    lean_inc(v_cache_3155_);
                    lean_inc(v_lhsPrec_3154_);
                    lean_inc(v_stxStack_3153_);
                    lean_dec(v_s_3150_);
                    v___x_3158_ = lean_box(0);
                    v_isShared_3159_ = v_isSharedCheck_3165_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3160_ =
                    l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3153_, v_iniStackSz_3151_);
                v___x_3161_ = lean_box(0);
                if v_isShared_3159_ == 0 {
                    lean_ctor_set(v___x_3158_, 4, v___x_3161_);
                    lean_ctor_set(v___x_3158_, 2, v_iniPos_3152_);
                    lean_ctor_set(v___x_3158_, 0, v___x_3160_);
                    v___x_3163_ = v___x_3158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3160_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_lhsPrec_3154_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_iniPos_3152_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_cache_3155_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 4, v___x_3161_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 5, v_recoveredErrors_3156_);
                    v___x_3163_ = v_reuseFailAlloc_3164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_restore___boxed(
    mut v_s_3168_: *mut LeanObject,
    mut v_iniStackSz_3169_: *mut LeanObject,
    mut v_iniPos_3170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3171_: *mut LeanObject = core::ptr::null_mut();
    v_res_3171_ = l_Lean_Parser_ParserState_restore(v_s_3168_, v_iniStackSz_3169_, v_iniPos_3170_);
    lean_dec(v_iniStackSz_3169_);
    return v_res_3171_;
}
pub unsafe fn l_Lean_Parser_ParserState_setPos(
    mut v_s_3172_: *mut LeanObject,
    mut v_pos_3173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_unused_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3174_ = lean_ctor_get(v_s_3172_, 0);
                v_lhsPrec_3175_ = lean_ctor_get(v_s_3172_, 1);
                v_cache_3176_ = lean_ctor_get(v_s_3172_, 3);
                v_errorMsg_3177_ = lean_ctor_get(v_s_3172_, 4);
                v_recoveredErrors_3178_ = lean_ctor_get(v_s_3172_, 5);
                v_isSharedCheck_3185_ = (!lean_is_exclusive(v_s_3172_)) as u8;
                if v_isSharedCheck_3185_ == 0 {
                    v_unused_3186_ = lean_ctor_get(v_s_3172_, 2);
                    lean_dec(v_unused_3186_);
                    v___x_3180_ = v_s_3172_;
                    v_isShared_3181_ = v_isSharedCheck_3185_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3178_);
                    lean_inc(v_errorMsg_3177_);
                    lean_inc(v_cache_3176_);
                    lean_inc(v_lhsPrec_3175_);
                    lean_inc(v_stxStack_3174_);
                    lean_dec(v_s_3172_);
                    v___x_3180_ = lean_box(0);
                    v_isShared_3181_ = v_isSharedCheck_3185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3181_ == 0 {
                    lean_ctor_set(v___x_3180_, 2, v_pos_3173_);
                    v___x_3183_ = v___x_3180_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_stxStack_3174_);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_lhsPrec_3175_);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_pos_3173_);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_cache_3176_);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_errorMsg_3177_);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 5, v_recoveredErrors_3178_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_setCache(
    mut v_s_3187_: *mut LeanObject,
    mut v_cache_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_unused_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3189_ = lean_ctor_get(v_s_3187_, 0);
                v_lhsPrec_3190_ = lean_ctor_get(v_s_3187_, 1);
                v_pos_3191_ = lean_ctor_get(v_s_3187_, 2);
                v_errorMsg_3192_ = lean_ctor_get(v_s_3187_, 4);
                v_recoveredErrors_3193_ = lean_ctor_get(v_s_3187_, 5);
                v_isSharedCheck_3200_ = (!lean_is_exclusive(v_s_3187_)) as u8;
                if v_isSharedCheck_3200_ == 0 {
                    v_unused_3201_ = lean_ctor_get(v_s_3187_, 3);
                    lean_dec(v_unused_3201_);
                    v___x_3195_ = v_s_3187_;
                    v_isShared_3196_ = v_isSharedCheck_3200_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3193_);
                    lean_inc(v_errorMsg_3192_);
                    lean_inc(v_pos_3191_);
                    lean_inc(v_lhsPrec_3190_);
                    lean_inc(v_stxStack_3189_);
                    lean_dec(v_s_3187_);
                    v___x_3195_ = lean_box(0);
                    v_isShared_3196_ = v_isSharedCheck_3200_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3196_ == 0 {
                    lean_ctor_set(v___x_3195_, 3, v_cache_3188_);
                    v___x_3198_ = v___x_3195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_stxStack_3189_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_lhsPrec_3190_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_pos_3191_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 3, v_cache_3188_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_errorMsg_3192_);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 5, v_recoveredErrors_3193_);
                    v___x_3198_ = v_reuseFailAlloc_3199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_pushSyntax(
    mut v_s_3202_: *mut LeanObject,
    mut v_n_3203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3204_ = lean_ctor_get(v_s_3202_, 0);
                v_lhsPrec_3205_ = lean_ctor_get(v_s_3202_, 1);
                v_pos_3206_ = lean_ctor_get(v_s_3202_, 2);
                v_cache_3207_ = lean_ctor_get(v_s_3202_, 3);
                v_errorMsg_3208_ = lean_ctor_get(v_s_3202_, 4);
                v_recoveredErrors_3209_ = lean_ctor_get(v_s_3202_, 5);
                v_isSharedCheck_3217_ = (!lean_is_exclusive(v_s_3202_)) as u8;
                if v_isSharedCheck_3217_ == 0 {
                    v___x_3211_ = v_s_3202_;
                    v_isShared_3212_ = v_isSharedCheck_3217_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3209_);
                    lean_inc(v_errorMsg_3208_);
                    lean_inc(v_cache_3207_);
                    lean_inc(v_pos_3206_);
                    lean_inc(v_lhsPrec_3205_);
                    lean_inc(v_stxStack_3204_);
                    lean_dec(v_s_3202_);
                    v___x_3211_ = lean_box(0);
                    v_isShared_3212_ = v_isSharedCheck_3217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3213_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_3204_, v_n_3203_);
                if v_isShared_3212_ == 0 {
                    lean_ctor_set(v___x_3211_, 0, v___x_3213_);
                    v___x_3215_ = v___x_3211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
                    lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_lhsPrec_3205_);
                    lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_pos_3206_);
                    lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_cache_3207_);
                    lean_ctor_set(v_reuseFailAlloc_3216_, 4, v_errorMsg_3208_);
                    lean_ctor_set(v_reuseFailAlloc_3216_, 5, v_recoveredErrors_3209_);
                    v___x_3215_ = v_reuseFailAlloc_3216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_popSyntax(
    mut v_s_3218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3219_ = lean_ctor_get(v_s_3218_, 0);
                v_lhsPrec_3220_ = lean_ctor_get(v_s_3218_, 1);
                v_pos_3221_ = lean_ctor_get(v_s_3218_, 2);
                v_cache_3222_ = lean_ctor_get(v_s_3218_, 3);
                v_errorMsg_3223_ = lean_ctor_get(v_s_3218_, 4);
                v_recoveredErrors_3224_ = lean_ctor_get(v_s_3218_, 5);
                v_isSharedCheck_3232_ = (!lean_is_exclusive(v_s_3218_)) as u8;
                if v_isSharedCheck_3232_ == 0 {
                    v___x_3226_ = v_s_3218_;
                    v_isShared_3227_ = v_isSharedCheck_3232_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3224_);
                    lean_inc(v_errorMsg_3223_);
                    lean_inc(v_cache_3222_);
                    lean_inc(v_pos_3221_);
                    lean_inc(v_lhsPrec_3220_);
                    lean_inc(v_stxStack_3219_);
                    lean_dec(v_s_3218_);
                    v___x_3226_ = lean_box(0);
                    v_isShared_3227_ = v_isSharedCheck_3232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3228_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_3219_);
                if v_isShared_3227_ == 0 {
                    lean_ctor_set(v___x_3226_, 0, v___x_3228_);
                    v___x_3230_ = v___x_3226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_lhsPrec_3220_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_pos_3221_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_cache_3222_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 4, v_errorMsg_3223_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 5, v_recoveredErrors_3224_);
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_shrinkStack(
    mut v_s_3233_: *mut LeanObject,
    mut v_iniStackSz_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3235_ = lean_ctor_get(v_s_3233_, 0);
                v_lhsPrec_3236_ = lean_ctor_get(v_s_3233_, 1);
                v_pos_3237_ = lean_ctor_get(v_s_3233_, 2);
                v_cache_3238_ = lean_ctor_get(v_s_3233_, 3);
                v_errorMsg_3239_ = lean_ctor_get(v_s_3233_, 4);
                v_recoveredErrors_3240_ = lean_ctor_get(v_s_3233_, 5);
                v_isSharedCheck_3248_ = (!lean_is_exclusive(v_s_3233_)) as u8;
                if v_isSharedCheck_3248_ == 0 {
                    v___x_3242_ = v_s_3233_;
                    v_isShared_3243_ = v_isSharedCheck_3248_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3240_);
                    lean_inc(v_errorMsg_3239_);
                    lean_inc(v_cache_3238_);
                    lean_inc(v_pos_3237_);
                    lean_inc(v_lhsPrec_3236_);
                    lean_inc(v_stxStack_3235_);
                    lean_dec(v_s_3233_);
                    v___x_3242_ = lean_box(0);
                    v_isShared_3243_ = v_isSharedCheck_3248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3244_ =
                    l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3235_, v_iniStackSz_3234_);
                if v_isShared_3243_ == 0 {
                    lean_ctor_set(v___x_3242_, 0, v___x_3244_);
                    v___x_3246_ = v___x_3242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_lhsPrec_3236_);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_pos_3237_);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_cache_3238_);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_errorMsg_3239_);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 5, v_recoveredErrors_3240_);
                    v___x_3246_ = v_reuseFailAlloc_3247_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_shrinkStack___boxed(
    mut v_s_3249_: *mut LeanObject,
    mut v_iniStackSz_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3251_: *mut LeanObject = core::ptr::null_mut();
    v_res_3251_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3249_, v_iniStackSz_3250_);
    lean_dec(v_iniStackSz_3250_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_Parser_ParserState_next(
    mut v_s_3252_: *mut LeanObject,
    mut v_c_3253_: *mut LeanObject,
    mut v_pos_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v_inputString_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut v_unused_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3255_ = lean_ctor_get(v_c_3253_, 0);
                v_stxStack_3256_ = lean_ctor_get(v_s_3252_, 0);
                v_lhsPrec_3257_ = lean_ctor_get(v_s_3252_, 1);
                v_cache_3258_ = lean_ctor_get(v_s_3252_, 3);
                v_errorMsg_3259_ = lean_ctor_get(v_s_3252_, 4);
                v_recoveredErrors_3260_ = lean_ctor_get(v_s_3252_, 5);
                v_isSharedCheck_3269_ = (!lean_is_exclusive(v_s_3252_)) as u8;
                if v_isSharedCheck_3269_ == 0 {
                    v_unused_3270_ = lean_ctor_get(v_s_3252_, 2);
                    lean_dec(v_unused_3270_);
                    v___x_3262_ = v_s_3252_;
                    v_isShared_3263_ = v_isSharedCheck_3269_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3260_);
                    lean_inc(v_errorMsg_3259_);
                    lean_inc(v_cache_3258_);
                    lean_inc(v_lhsPrec_3257_);
                    lean_inc(v_stxStack_3256_);
                    lean_dec(v_s_3252_);
                    v___x_3262_ = lean_box(0);
                    v_isShared_3263_ = v_isSharedCheck_3269_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputString_3264_ = lean_ctor_get(v_toInputContext_3255_, 0);
                v___x_3265_ = lean_string_utf8_next(v_inputString_3264_, v_pos_3254_);
                if v_isShared_3263_ == 0 {
                    lean_ctor_set(v___x_3262_, 2, v___x_3265_);
                    v___x_3267_ = v___x_3262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_stxStack_3256_);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_lhsPrec_3257_);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 2, v___x_3265_);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 3, v_cache_3258_);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 4, v_errorMsg_3259_);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 5, v_recoveredErrors_3260_);
                    v___x_3267_ = v_reuseFailAlloc_3268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_next___boxed(
    mut v_s_3271_: *mut LeanObject,
    mut v_c_3272_: *mut LeanObject,
    mut v_pos_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3274_: *mut LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Lean_Parser_ParserState_next(v_s_3271_, v_c_3272_, v_pos_3273_);
    lean_dec(v_pos_3273_);
    lean_dec_ref(v_c_3272_);
    return v_res_3274_;
}
pub unsafe fn l_Lean_Parser_ParserState_next_x27___redArg(
    mut v_s_3275_: *mut LeanObject,
    mut v_c_3276_: *mut LeanObject,
    mut v_pos_3277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v_inputString_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_unused_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3278_ = lean_ctor_get(v_c_3276_, 0);
                v_stxStack_3279_ = lean_ctor_get(v_s_3275_, 0);
                v_lhsPrec_3280_ = lean_ctor_get(v_s_3275_, 1);
                v_cache_3281_ = lean_ctor_get(v_s_3275_, 3);
                v_errorMsg_3282_ = lean_ctor_get(v_s_3275_, 4);
                v_recoveredErrors_3283_ = lean_ctor_get(v_s_3275_, 5);
                v_isSharedCheck_3292_ = (!lean_is_exclusive(v_s_3275_)) as u8;
                if v_isSharedCheck_3292_ == 0 {
                    v_unused_3293_ = lean_ctor_get(v_s_3275_, 2);
                    lean_dec(v_unused_3293_);
                    v___x_3285_ = v_s_3275_;
                    v_isShared_3286_ = v_isSharedCheck_3292_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3283_);
                    lean_inc(v_errorMsg_3282_);
                    lean_inc(v_cache_3281_);
                    lean_inc(v_lhsPrec_3280_);
                    lean_inc(v_stxStack_3279_);
                    lean_dec(v_s_3275_);
                    v___x_3285_ = lean_box(0);
                    v_isShared_3286_ = v_isSharedCheck_3292_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputString_3287_ = lean_ctor_get(v_toInputContext_3278_, 0);
                v___x_3288_ = lean_string_utf8_next_fast(v_inputString_3287_, v_pos_3277_);
                if v_isShared_3286_ == 0 {
                    lean_ctor_set(v___x_3285_, 2, v___x_3288_);
                    v___x_3290_ = v___x_3285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_stxStack_3279_);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_lhsPrec_3280_);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 2, v___x_3288_);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 3, v_cache_3281_);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 4, v_errorMsg_3282_);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 5, v_recoveredErrors_3283_);
                    v___x_3290_ = v_reuseFailAlloc_3291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_next_x27___redArg___boxed(
    mut v_s_3294_: *mut LeanObject,
    mut v_c_3295_: *mut LeanObject,
    mut v_pos_3296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3297_: *mut LeanObject = core::ptr::null_mut();
    v_res_3297_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3294_, v_c_3295_, v_pos_3296_);
    lean_dec(v_pos_3296_);
    lean_dec_ref(v_c_3295_);
    return v_res_3297_;
}
pub unsafe fn l_Lean_Parser_ParserState_next_x27(
    mut v_s_3298_: *mut LeanObject,
    mut v_c_3299_: *mut LeanObject,
    mut v_pos_3300_: *mut LeanObject,
    mut v_h_3301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    v___x_3302_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3298_, v_c_3299_, v_pos_3300_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_Parser_ParserState_next_x27___boxed(
    mut v_s_3303_: *mut LeanObject,
    mut v_c_3304_: *mut LeanObject,
    mut v_pos_3305_: *mut LeanObject,
    mut v_h_3306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3307_: *mut LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Parser_ParserState_next_x27(v_s_3303_, v_c_3304_, v_pos_3305_, v_h_3306_);
    lean_dec(v_pos_3305_);
    lean_dec_ref(v_c_3304_);
    return v_res_3307_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(
    mut v_x_3308_: *mut LeanObject,
    mut v_x_3309_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3308_) == 0 {
        if lean_obj_tag(v_x_3309_) == 0 {
            let mut v___x_3310_: u8 = 0;
            v___x_3310_ = 1;
            return v___x_3310_;
        } else {
            let mut v___x_3311_: u8 = 0;
            lean_dec_ref_known(v_x_3309_, 1);
            v___x_3311_ = 0;
            return v___x_3311_;
        }
    } else {
        if lean_obj_tag(v_x_3309_) == 0 {
            let mut v___x_3312_: u8 = 0;
            lean_dec_ref_known(v_x_3308_, 1);
            v___x_3312_ = 0;
            return v___x_3312_;
        } else {
            let mut v_val_3313_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_3314_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3315_: u8 = 0;
            v_val_3313_ = lean_ctor_get(v_x_3308_, 0);
            lean_inc(v_val_3313_);
            lean_dec_ref_known(v_x_3308_, 1);
            v_val_3314_ = lean_ctor_get(v_x_3309_, 0);
            lean_inc(v_val_3314_);
            lean_dec_ref_known(v_x_3309_, 1);
            v___x_3315_ = l_Lean_Parser_instBEqError_beq(v_val_3313_, v_val_3314_);
            return v___x_3315_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(
    mut v_x_3316_: *mut LeanObject,
    mut v_x_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3318_: u8 = 0;
    let mut v_r_3319_: *mut LeanObject = core::ptr::null_mut();
    v_res_3318_ =
        l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_3316_, v_x_3317_);
    v_r_3319_ = lean_box((v_res_3318_) as usize);
    return v_r_3319_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkNode(
    mut v_s_3320_: *mut LeanObject,
    mut v_k_3321_: *mut LeanObject,
    mut v_iniStackSz_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stack_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stack_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: u8 = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stack_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3323_ = lean_ctor_get(v_s_3320_, 0);
                v_lhsPrec_3324_ = lean_ctor_get(v_s_3320_, 1);
                v_pos_3325_ = lean_ctor_get(v_s_3320_, 2);
                v_cache_3326_ = lean_ctor_get(v_s_3320_, 3);
                v_errorMsg_3327_ = lean_ctor_get(v_s_3320_, 4);
                v_recoveredErrors_3328_ = lean_ctor_get(v_s_3320_, 5);
                v_isSharedCheck_3349_ = (!lean_is_exclusive(v_s_3320_)) as u8;
                if v_isSharedCheck_3349_ == 0 {
                    v___x_3330_ = v_s_3320_;
                    v_isShared_3331_ = v_isSharedCheck_3349_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3328_);
                    lean_inc(v_errorMsg_3327_);
                    lean_inc(v_cache_3326_);
                    lean_inc(v_pos_3325_);
                    lean_inc(v_lhsPrec_3324_);
                    lean_inc(v_stxStack_3323_);
                    lean_dec(v_s_3320_);
                    v___x_3330_ = lean_box(0);
                    v_isShared_3331_ = v_isSharedCheck_3349_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3342_ = lean_box(0);
                lean_inc(v_errorMsg_3327_);
                v___x_3343_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(
                    v_errorMsg_3327_,
                    v___x_3342_,
                );
                if v___x_3343_ == 0 {
                    v___x_3344_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3323_);
                    v___x_3345_ = lean_nat_dec_eq(v___x_3344_, v_iniStackSz_3322_);
                    lean_dec(v___x_3344_);
                    if v___x_3345_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_3330_);
                        lean_dec(v_k_3321_);
                        v___x_3346_ = lean_box(0);
                        v_stack_3347_ =
                            l_Lean_Parser_SyntaxStack_push(v_stxStack_3323_, v___x_3346_);
                        v___x_3348_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v___x_3348_, 0, v_stack_3347_);
                        lean_ctor_set(v___x_3348_, 1, v_lhsPrec_3324_);
                        lean_ctor_set(v___x_3348_, 2, v_pos_3325_);
                        lean_ctor_set(v___x_3348_, 3, v_cache_3326_);
                        lean_ctor_set(v___x_3348_, 4, v_errorMsg_3327_);
                        lean_ctor_set(v___x_3348_, 5, v_recoveredErrors_3328_);
                        return v___x_3348_;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3333_ = lean_box(2);
                v___x_3334_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3323_);
                v___x_3335_ = l_Lean_Parser_SyntaxStack_extract(
                    v_stxStack_3323_,
                    v_iniStackSz_3322_,
                    v___x_3334_,
                );
                lean_dec(v___x_3334_);
                v_newNode_3336_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v_newNode_3336_, 0, v___x_3333_);
                lean_ctor_set(v_newNode_3336_, 1, v_k_3321_);
                lean_ctor_set(v_newNode_3336_, 2, v___x_3335_);
                v_stack_3337_ =
                    l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3323_, v_iniStackSz_3322_);
                v_stack_3338_ = l_Lean_Parser_SyntaxStack_push(v_stack_3337_, v_newNode_3336_);
                if v_isShared_3331_ == 0 {
                    lean_ctor_set(v___x_3330_, 0, v_stack_3338_);
                    v___x_3340_ = v___x_3330_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_stack_3338_);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_lhsPrec_3324_);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_pos_3325_);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_cache_3326_);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 4, v_errorMsg_3327_);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 5, v_recoveredErrors_3328_);
                    v___x_3340_ = v_reuseFailAlloc_3341_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkNode___boxed(
    mut v_s_3350_: *mut LeanObject,
    mut v_k_3351_: *mut LeanObject,
    mut v_iniStackSz_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3353_: *mut LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_Parser_ParserState_mkNode(v_s_3350_, v_k_3351_, v_iniStackSz_3352_);
    lean_dec(v_iniStackSz_3352_);
    return v_res_3353_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkTrailingNode(
    mut v_s_3354_: *mut LeanObject,
    mut v_k_3355_: *mut LeanObject,
    mut v_iniStackSz_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stack_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stack_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3357_ = lean_ctor_get(v_s_3354_, 0);
                v_lhsPrec_3358_ = lean_ctor_get(v_s_3354_, 1);
                v_pos_3359_ = lean_ctor_get(v_s_3354_, 2);
                v_cache_3360_ = lean_ctor_get(v_s_3354_, 3);
                v_errorMsg_3361_ = lean_ctor_get(v_s_3354_, 4);
                v_recoveredErrors_3362_ = lean_ctor_get(v_s_3354_, 5);
                v_isSharedCheck_3377_ = (!lean_is_exclusive(v_s_3354_)) as u8;
                if v_isSharedCheck_3377_ == 0 {
                    v___x_3364_ = v_s_3354_;
                    v_isShared_3365_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3362_);
                    lean_inc(v_errorMsg_3361_);
                    lean_inc(v_cache_3360_);
                    lean_inc(v_pos_3359_);
                    lean_inc(v_lhsPrec_3358_);
                    lean_inc(v_stxStack_3357_);
                    lean_dec(v_s_3354_);
                    v___x_3364_ = lean_box(0);
                    v_isShared_3365_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3366_ = lean_box(2);
                v___x_3367_ = lean_unsigned_to_nat(1);
                v___x_3368_ = lean_nat_sub(v_iniStackSz_3356_, v___x_3367_);
                v___x_3369_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3357_);
                v___x_3370_ =
                    l_Lean_Parser_SyntaxStack_extract(v_stxStack_3357_, v___x_3368_, v___x_3369_);
                lean_dec(v___x_3369_);
                v_newNode_3371_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v_newNode_3371_, 0, v___x_3366_);
                lean_ctor_set(v_newNode_3371_, 1, v_k_3355_);
                lean_ctor_set(v_newNode_3371_, 2, v___x_3370_);
                v_stack_3372_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3357_, v___x_3368_);
                lean_dec(v___x_3368_);
                v_stack_3373_ = l_Lean_Parser_SyntaxStack_push(v_stack_3372_, v_newNode_3371_);
                if v_isShared_3365_ == 0 {
                    lean_ctor_set(v___x_3364_, 0, v_stack_3373_);
                    v___x_3375_ = v___x_3364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_stack_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_lhsPrec_3358_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_pos_3359_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 3, v_cache_3360_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 4, v_errorMsg_3361_);
                    lean_ctor_set(v_reuseFailAlloc_3376_, 5, v_recoveredErrors_3362_);
                    v___x_3375_ = v_reuseFailAlloc_3376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkTrailingNode___boxed(
    mut v_s_3378_: *mut LeanObject,
    mut v_k_3379_: *mut LeanObject,
    mut v_iniStackSz_3380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3381_: *mut LeanObject = core::ptr::null_mut();
    v_res_3381_ =
        l_Lean_Parser_ParserState_mkTrailingNode(v_s_3378_, v_k_3379_, v_iniStackSz_3380_);
    lean_dec(v_iniStackSz_3380_);
    return v_res_3381_;
}
pub unsafe fn l_Lean_Parser_ParserState_allErrors(
    mut v_s_3384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_errorMsg_3385_: *mut LeanObject = core::ptr::null_mut();
    v_errorMsg_3385_ = lean_ctor_get(v_s_3384_, 4);
    if lean_obj_tag(v_errorMsg_3385_) == 0 {
        let mut v_recoveredErrors_3386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
        v_recoveredErrors_3386_ = lean_ctor_get(v_s_3384_, 5);
        lean_inc_ref(v_recoveredErrors_3386_);
        lean_dec_ref(v_s_3384_);
        v___x_3387_ = l_Lean_Parser_ParserState_allErrors___closed__0;
        v___x_3388_ = l_Array_append___redArg(v_recoveredErrors_3386_, v___x_3387_);
        return v___x_3388_;
    } else {
        let mut v_stxStack_3389_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pos_3390_: *mut LeanObject = core::ptr::null_mut();
        let mut v_recoveredErrors_3391_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_3392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_errorMsg_3385_);
        v_stxStack_3389_ = lean_ctor_get(v_s_3384_, 0);
        lean_inc_ref(v_stxStack_3389_);
        v_pos_3390_ = lean_ctor_get(v_s_3384_, 2);
        lean_inc(v_pos_3390_);
        v_recoveredErrors_3391_ = lean_ctor_get(v_s_3384_, 5);
        lean_inc_ref(v_recoveredErrors_3391_);
        lean_dec_ref(v_s_3384_);
        v_val_3392_ = lean_ctor_get(v_errorMsg_3385_, 0);
        lean_inc(v_val_3392_);
        lean_dec_ref_known(v_errorMsg_3385_, 1);
        v___x_3393_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3393_, 0, v_stxStack_3389_);
        lean_ctor_set(v___x_3393_, 1, v_val_3392_);
        v___x_3394_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3394_, 0, v_pos_3390_);
        lean_ctor_set(v___x_3394_, 1, v___x_3393_);
        v___x_3395_ = lean_unsigned_to_nat(1);
        v___x_3396_ = lean_mk_empty_array_with_capacity(v___x_3395_);
        v___x_3397_ = lean_array_push(v___x_3396_, v___x_3394_);
        v___x_3398_ = l_Array_append___redArg(v_recoveredErrors_3391_, v___x_3397_);
        lean_dec_ref(v___x_3397_);
        return v___x_3398_;
    }
}
pub unsafe fn l_Lean_Parser_ParserState_setError(
    mut v_s_3399_: *mut LeanObject,
    mut v_e_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3408_: u8 = 0;
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut v_unused_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3401_ = lean_ctor_get(v_s_3399_, 0);
                v_lhsPrec_3402_ = lean_ctor_get(v_s_3399_, 1);
                v_pos_3403_ = lean_ctor_get(v_s_3399_, 2);
                v_cache_3404_ = lean_ctor_get(v_s_3399_, 3);
                v_recoveredErrors_3405_ = lean_ctor_get(v_s_3399_, 5);
                v_isSharedCheck_3413_ = (!lean_is_exclusive(v_s_3399_)) as u8;
                if v_isSharedCheck_3413_ == 0 {
                    v_unused_3414_ = lean_ctor_get(v_s_3399_, 4);
                    lean_dec(v_unused_3414_);
                    v___x_3407_ = v_s_3399_;
                    v_isShared_3408_ = v_isSharedCheck_3413_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3405_);
                    lean_inc(v_cache_3404_);
                    lean_inc(v_pos_3403_);
                    lean_inc(v_lhsPrec_3402_);
                    lean_inc(v_stxStack_3401_);
                    lean_dec(v_s_3399_);
                    v___x_3407_ = lean_box(0);
                    v_isShared_3408_ = v_isSharedCheck_3413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3409_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3409_, 0, v_e_3400_);
                if v_isShared_3408_ == 0 {
                    lean_ctor_set(v___x_3407_, 4, v___x_3409_);
                    v___x_3411_ = v___x_3407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_stxStack_3401_);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_lhsPrec_3402_);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_pos_3403_);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_cache_3404_);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 4, v___x_3409_);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 5, v_recoveredErrors_3405_);
                    v___x_3411_ = v_reuseFailAlloc_3412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkError(
    mut v_s_3415_: *mut LeanObject,
    mut v_msg_3416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v_unused_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3417_ = lean_ctor_get(v_s_3415_, 0);
                v_lhsPrec_3418_ = lean_ctor_get(v_s_3415_, 1);
                v_pos_3419_ = lean_ctor_get(v_s_3415_, 2);
                v_cache_3420_ = lean_ctor_get(v_s_3415_, 3);
                v_recoveredErrors_3421_ = lean_ctor_get(v_s_3415_, 5);
                v_isSharedCheck_3435_ = (!lean_is_exclusive(v_s_3415_)) as u8;
                if v_isSharedCheck_3435_ == 0 {
                    v_unused_3436_ = lean_ctor_get(v_s_3415_, 4);
                    lean_dec(v_unused_3436_);
                    v___x_3423_ = v_s_3415_;
                    v_isShared_3424_ = v_isSharedCheck_3435_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3421_);
                    lean_inc(v_cache_3420_);
                    lean_inc(v_pos_3419_);
                    lean_inc(v_lhsPrec_3418_);
                    lean_inc(v_stxStack_3417_);
                    lean_dec(v_s_3415_);
                    v___x_3423_ = lean_box(0);
                    v_isShared_3424_ = v_isSharedCheck_3435_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3425_ = lean_box(0);
                v___x_3426_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_3427_ = lean_box(0);
                v___x_3428_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3428_, 0, v_msg_3416_);
                lean_ctor_set(v___x_3428_, 1, v___x_3427_);
                v___x_3429_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3429_, 0, v___x_3425_);
                lean_ctor_set(v___x_3429_, 1, v___x_3426_);
                lean_ctor_set(v___x_3429_, 2, v___x_3428_);
                v___x_3430_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3430_, 0, v___x_3429_);
                if v_isShared_3424_ == 0 {
                    lean_ctor_set(v___x_3423_, 4, v___x_3430_);
                    v___x_3432_ = v___x_3423_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_stxStack_3417_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_lhsPrec_3418_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_pos_3419_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_cache_3420_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 4, v___x_3430_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 5, v_recoveredErrors_3421_);
                    v___x_3432_ = v_reuseFailAlloc_3434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3433_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3432_, v___x_3425_);
                return v___x_3433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkUnexpectedError(
    mut v_s_3437_: *mut LeanObject,
    mut v_msg_3438_: *mut LeanObject,
    mut v_expected_3439_: *mut LeanObject,
    mut v_pushMissing_3440_: u8,
) -> *mut LeanObject {
    let mut v_stxStack_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut v_unused_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3441_ = lean_ctor_get(v_s_3437_, 0);
                v_lhsPrec_3442_ = lean_ctor_get(v_s_3437_, 1);
                v_pos_3443_ = lean_ctor_get(v_s_3437_, 2);
                v_cache_3444_ = lean_ctor_get(v_s_3437_, 3);
                v_recoveredErrors_3445_ = lean_ctor_get(v_s_3437_, 5);
                v_isSharedCheck_3456_ = (!lean_is_exclusive(v_s_3437_)) as u8;
                if v_isSharedCheck_3456_ == 0 {
                    v_unused_3457_ = lean_ctor_get(v_s_3437_, 4);
                    lean_dec(v_unused_3457_);
                    v___x_3447_ = v_s_3437_;
                    v_isShared_3448_ = v_isSharedCheck_3456_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3445_);
                    lean_inc(v_cache_3444_);
                    lean_inc(v_pos_3443_);
                    lean_inc(v_lhsPrec_3442_);
                    lean_inc(v_stxStack_3441_);
                    lean_dec(v_s_3437_);
                    v___x_3447_ = lean_box(0);
                    v_isShared_3448_ = v_isSharedCheck_3456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3449_ = lean_box(0);
                v___x_3450_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3450_, 0, v___x_3449_);
                lean_ctor_set(v___x_3450_, 1, v_msg_3438_);
                lean_ctor_set(v___x_3450_, 2, v_expected_3439_);
                v___x_3451_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3451_, 0, v___x_3450_);
                if v_isShared_3448_ == 0 {
                    lean_ctor_set(v___x_3447_, 4, v___x_3451_);
                    v_s_3453_ = v___x_3447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_stxStack_3441_);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_lhsPrec_3442_);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_pos_3443_);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 3, v_cache_3444_);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 4, v___x_3451_);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 5, v_recoveredErrors_3445_);
                    v_s_3453_ = v_reuseFailAlloc_3455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_pushMissing_3440_ == 0 {
                    return v_s_3453_;
                } else {
                    v___x_3454_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3453_, v___x_3449_);
                    return v___x_3454_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkUnexpectedError___boxed(
    mut v_s_3458_: *mut LeanObject,
    mut v_msg_3459_: *mut LeanObject,
    mut v_expected_3460_: *mut LeanObject,
    mut v_pushMissing_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pushMissing_boxed_3462_: u8 = 0;
    let mut v_res_3463_: *mut LeanObject = core::ptr::null_mut();
    v_pushMissing_boxed_3462_ = (lean_unbox(v_pushMissing_3461_) as u8);
    v_res_3463_ = l_Lean_Parser_ParserState_mkUnexpectedError(
        v_s_3458_,
        v_msg_3459_,
        v_expected_3460_,
        v_pushMissing_boxed_3462_,
    );
    return v_res_3463_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkEOIError(
    mut v_s_3465_: *mut LeanObject,
    mut v_expected_3466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    v___x_3467_ = l_Lean_Parser_ParserState_mkEOIError___closed__0;
    v___x_3468_ = 1;
    v___x_3469_ = l_Lean_Parser_ParserState_mkUnexpectedError(
        v_s_3465_,
        v___x_3467_,
        v_expected_3466_,
        v___x_3468_,
    );
    return v___x_3469_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkErrorsAt(
    mut v_s_3470_: *mut LeanObject,
    mut v_ex_3471_: *mut LeanObject,
    mut v_pos_3472_: *mut LeanObject,
    mut v_initStackSz_x3f_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v_unused_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_3494_ = l_Lean_Parser_ParserState_setPos(v_s_3470_, v_pos_3472_);
                if lean_obj_tag(v_initStackSz_x3f_3473_) == 1 {
                    v_val_3495_ = lean_ctor_get(v_initStackSz_x3f_3473_, 0);
                    v_s_3496_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3494_, v_val_3495_);
                    v_s_3475_ = v_s_3496_;
                    state = 1;
                    continue;
                } else {
                    v_s_3475_ = v_s_3494_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_stxStack_3476_ = lean_ctor_get(v_s_3475_, 0);
                v_lhsPrec_3477_ = lean_ctor_get(v_s_3475_, 1);
                v_pos_3478_ = lean_ctor_get(v_s_3475_, 2);
                v_cache_3479_ = lean_ctor_get(v_s_3475_, 3);
                v_recoveredErrors_3480_ = lean_ctor_get(v_s_3475_, 5);
                v_isSharedCheck_3492_ = (!lean_is_exclusive(v_s_3475_)) as u8;
                if v_isSharedCheck_3492_ == 0 {
                    v_unused_3493_ = lean_ctor_get(v_s_3475_, 4);
                    lean_dec(v_unused_3493_);
                    v___x_3482_ = v_s_3475_;
                    v_isShared_3483_ = v_isSharedCheck_3492_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3480_);
                    lean_inc(v_cache_3479_);
                    lean_inc(v_pos_3478_);
                    lean_inc(v_lhsPrec_3477_);
                    lean_inc(v_stxStack_3476_);
                    lean_dec(v_s_3475_);
                    v___x_3482_ = lean_box(0);
                    v_isShared_3483_ = v_isSharedCheck_3492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3484_ = lean_box(0);
                v___x_3485_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_3486_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3486_, 0, v___x_3484_);
                lean_ctor_set(v___x_3486_, 1, v___x_3485_);
                lean_ctor_set(v___x_3486_, 2, v_ex_3471_);
                v___x_3487_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3487_, 0, v___x_3486_);
                if v_isShared_3483_ == 0 {
                    lean_ctor_set(v___x_3482_, 4, v___x_3487_);
                    v_s_3489_ = v___x_3482_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_stxStack_3476_);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_lhsPrec_3477_);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_pos_3478_);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 3, v_cache_3479_);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 4, v___x_3487_);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 5, v_recoveredErrors_3480_);
                    v_s_3489_ = v_reuseFailAlloc_3491_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3490_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3489_, v___x_3484_);
                return v___x_3490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkErrorsAt___boxed(
    mut v_s_3497_: *mut LeanObject,
    mut v_ex_3498_: *mut LeanObject,
    mut v_pos_3499_: *mut LeanObject,
    mut v_initStackSz_x3f_3500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3501_: *mut LeanObject = core::ptr::null_mut();
    v_res_3501_ = l_Lean_Parser_ParserState_mkErrorsAt(
        v_s_3497_,
        v_ex_3498_,
        v_pos_3499_,
        v_initStackSz_x3f_3500_,
    );
    lean_dec(v_initStackSz_x3f_3500_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkErrorAt(
    mut v_s_3502_: *mut LeanObject,
    mut v_msg_3503_: *mut LeanObject,
    mut v_pos_3504_: *mut LeanObject,
    mut v_initStackSz_x3f_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v___x_3506_ = lean_box(0);
    v___x_3507_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3507_, 0, v_msg_3503_);
    lean_ctor_set(v___x_3507_, 1, v___x_3506_);
    v___x_3508_ = l_Lean_Parser_ParserState_mkErrorsAt(
        v_s_3502_,
        v___x_3507_,
        v_pos_3504_,
        v_initStackSz_x3f_3505_,
    );
    return v___x_3508_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkErrorAt___boxed(
    mut v_s_3509_: *mut LeanObject,
    mut v_msg_3510_: *mut LeanObject,
    mut v_pos_3511_: *mut LeanObject,
    mut v_initStackSz_x3f_3512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3513_: *mut LeanObject = core::ptr::null_mut();
    v_res_3513_ = l_Lean_Parser_ParserState_mkErrorAt(
        v_s_3509_,
        v_msg_3510_,
        v_pos_3511_,
        v_initStackSz_x3f_3512_,
    );
    lean_dec(v_initStackSz_x3f_3512_);
    return v_res_3513_;
}
pub unsafe fn l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(
    mut v_msg_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    v___x_3515_ = lean_unsigned_to_nat(0);
    v___x_3516_ = lean_panic_fn_borrowed(v___x_3515_, v_msg_3514_);
    return v___x_3516_;
}
pub unsafe fn _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3()
-> *mut LeanObject {
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2;
    v___x_3521_ = lean_unsigned_to_nat(14);
    v___x_3522_ = lean_unsigned_to_nat(22);
    v___x_3523_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1;
    v___x_3524_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0;
    v___x_3525_ = l_mkPanicMessageWithDecl(
        v___x_3524_,
        v___x_3523_,
        v___x_3522_,
        v___x_3521_,
        v___x_3520_,
    );
    return v___x_3525_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(
    mut v_s_3526_: *mut LeanObject,
    mut v_ex_3527_: *mut LeanObject,
    mut v_iniPos_3528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_unused_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3529_ = lean_ctor_get(v_s_3526_, 0);
                v_tk_3530_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3529_);
                v___x_3553_ = lean_unsigned_to_nat(0);
                v___x_3554_ = lean_nat_dec_lt(v___x_3553_, v_iniPos_3528_);
                if v___x_3554_ == 0 {
                    lean_dec(v_iniPos_3528_);
                    v___x_3555_ = l_Lean_Syntax_getPos_x3f(v_tk_3530_, v___x_3554_);
                    if lean_obj_tag(v___x_3555_) == 0 {
                        v___x_3556_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once
                            ),
                            _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3,
                        );
                        v___x_3557_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_3556_);
                        v___y_3532_ = v___x_3557_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3558_ = lean_ctor_get(v___x_3555_, 0);
                        lean_inc(v_val_3558_);
                        lean_dec_ref_known(v___x_3555_, 1);
                        v___y_3532_ = v_val_3558_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3532_ = v_iniPos_3528_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_s_3533_ = l_Lean_Parser_ParserState_setPos(v_s_3526_, v___y_3532_);
                v_stxStack_3534_ = lean_ctor_get(v_s_3533_, 0);
                v_lhsPrec_3535_ = lean_ctor_get(v_s_3533_, 1);
                v_pos_3536_ = lean_ctor_get(v_s_3533_, 2);
                v_cache_3537_ = lean_ctor_get(v_s_3533_, 3);
                v_recoveredErrors_3538_ = lean_ctor_get(v_s_3533_, 5);
                v_isSharedCheck_3551_ = (!lean_is_exclusive(v_s_3533_)) as u8;
                if v_isSharedCheck_3551_ == 0 {
                    v_unused_3552_ = lean_ctor_get(v_s_3533_, 4);
                    lean_dec(v_unused_3552_);
                    v___x_3540_ = v_s_3533_;
                    v_isShared_3541_ = v_isSharedCheck_3551_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3538_);
                    lean_inc(v_cache_3537_);
                    lean_inc(v_pos_3536_);
                    lean_inc(v_lhsPrec_3535_);
                    lean_inc(v_stxStack_3534_);
                    lean_dec(v_s_3533_);
                    v___x_3540_ = lean_box(0);
                    v_isShared_3541_ = v_isSharedCheck_3551_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3542_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_3543_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3543_, 0, v_tk_3530_);
                lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                lean_ctor_set(v___x_3543_, 2, v_ex_3527_);
                v___x_3544_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                if v_isShared_3541_ == 0 {
                    lean_ctor_set(v___x_3540_, 4, v___x_3544_);
                    v_s_3546_ = v___x_3540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_stxStack_3534_);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_lhsPrec_3535_);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_pos_3536_);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_cache_3537_);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 4, v___x_3544_);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 5, v_recoveredErrors_3538_);
                    v_s_3546_ = v_reuseFailAlloc_3550_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3547_ = l_Lean_Parser_ParserState_popSyntax(v_s_3546_);
                v___x_3548_ = lean_box(0);
                v___x_3549_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3547_, v___x_3548_);
                return v___x_3549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkUnexpectedTokenError(
    mut v_s_3559_: *mut LeanObject,
    mut v_msg_3560_: *mut LeanObject,
    mut v_iniPos_3561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    v___x_3562_ = lean_box(0);
    v___x_3563_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3563_, 0, v_msg_3560_);
    lean_ctor_set(v___x_3563_, 1, v___x_3562_);
    v___x_3564_ =
        l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3559_, v___x_3563_, v_iniPos_3561_);
    return v___x_3564_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
    mut v_s_3565_: *mut LeanObject,
    mut v_msg_3566_: *mut LeanObject,
    mut v_pos_3567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    v___x_3568_ = l_Lean_Parser_ParserState_setPos(v_s_3565_, v_pos_3567_);
    v___x_3569_ = lean_box(0);
    v___x_3570_ = 1;
    v___x_3571_ = l_Lean_Parser_ParserState_mkUnexpectedError(
        v___x_3568_,
        v_msg_3566_,
        v___x_3569_,
        v___x_3570_,
    );
    return v___x_3571_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(
    mut v_ctx_3573_: *mut LeanObject,
    mut v_as_3574_: *mut LeanObject,
    mut v_sz_3575_: usize,
    mut v_i_3576_: usize,
    mut v_b_3577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3578_: u8 = 0;
    let mut v_a_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errStr_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: usize = 0;
    let mut v___x_3593_: usize = 0;
    let mut v_errStr_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3578_ = lean_usize_dec_lt(v_i_3576_, v_sz_3575_);
                if v___x_3578_ == 0 {
                    lean_dec_ref(v_ctx_3573_);
                    return v_b_3577_;
                } else {
                    v_a_3579_ = lean_array_uget_borrowed(v_as_3574_, v_i_3576_);
                    v_snd_3580_ = lean_ctor_get(v_a_3579_, 1);
                    v_fst_3581_ = lean_ctor_get(v_a_3579_, 0);
                    v_snd_3582_ = lean_ctor_get(v_snd_3580_, 1);
                    v_errStr_3595_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                    v___x_3596_ = lean_string_dec_eq(v_b_3577_, v_errStr_3595_);
                    if v___x_3596_ == 0 {
                        v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0;
                        v___x_3598_ = lean_string_append(v_b_3577_, v___x_3597_);
                        v_errStr_3584_ = v___x_3598_;
                        state = 1;
                        continue;
                    } else {
                        v_errStr_3584_ = v_b_3577_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fileName_3585_ = lean_ctor_get(v_ctx_3573_, 1);
                v_fileMap_3586_ = lean_ctor_get(v_ctx_3573_, 2);
                lean_inc_ref(v_fileMap_3586_);
                v___x_3587_ = l_Lean_FileMap_toPosition(v_fileMap_3586_, v_fst_3581_);
                lean_inc(v_snd_3582_);
                v___x_3588_ = l_Lean_Parser_Error_toString(v_snd_3582_);
                v___x_3589_ = lean_box(0);
                lean_inc_ref(v_fileName_3585_);
                v___x_3590_ = l_Lean_mkErrorStringWithPos(
                    v_fileName_3585_,
                    v___x_3587_,
                    v___x_3588_,
                    v___x_3589_,
                    v___x_3589_,
                    v___x_3589_,
                );
                lean_dec_ref(v___x_3588_);
                v___x_3591_ = lean_string_append(v_errStr_3584_, v___x_3590_);
                lean_dec_ref(v___x_3590_);
                v___x_3592_ = 1usize;
                v___x_3593_ = lean_usize_add(v_i_3576_, v___x_3592_);
                v_i_3576_ = v___x_3593_;
                v_b_3577_ = v___x_3591_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(
    mut v_ctx_3599_: *mut LeanObject,
    mut v_as_3600_: *mut LeanObject,
    mut v_sz_3601_: *mut LeanObject,
    mut v_i_3602_: *mut LeanObject,
    mut v_b_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3604_: usize = 0;
    let mut v_i_boxed_3605_: usize = 0;
    let mut v_res_3606_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3604_ = lean_unbox_usize(v_sz_3601_);
    lean_dec(v_sz_3601_);
    v_i_boxed_3605_ = lean_unbox_usize(v_i_3602_);
    lean_dec(v_i_3602_);
    v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_3599_, v_as_3600_, v_sz_boxed_3604_, v_i_boxed_3605_, v_b_3603_);
    lean_dec_ref(v_as_3600_);
    return v_res_3606_;
}
pub unsafe fn l_Lean_Parser_ParserState_toErrorMsg(
    mut v_ctx_3607_: *mut LeanObject,
    mut v_s_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_errStr_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    v_errStr_3609_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
    v___x_3610_ = l_Lean_Parser_ParserState_allErrors(v_s_3608_);
    v_sz_3611_ = lean_array_size(v___x_3610_);
    v___x_3612_ = 0usize;
    v___x_3613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_3607_, v___x_3610_, v_sz_3611_, v___x_3612_, v_errStr_3609_);
    lean_dec_ref(v___x_3610_);
    return v___x_3613_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserFn___lam__0(
    mut v_x_3614_: *mut LeanObject,
    mut v_s_3615_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_3615_);
    return v_s_3615_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(
    mut v_x_3616_: *mut LeanObject,
    mut v_s_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3618_: *mut LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_3616_, v_s_3617_);
    lean_dec_ref(v_s_3617_);
    lean_dec_ref(v_x_3616_);
    return v_res_3618_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorIdx(mut v_x_3621_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_3621_) {
        0 => {
            let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
            v___x_3622_ = lean_unsigned_to_nat(0);
            return v___x_3622_;
        }
        1 => {
            let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
            v___x_3623_ = lean_unsigned_to_nat(1);
            return v___x_3623_;
        }
        2 => {
            let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
            v___x_3624_ = lean_unsigned_to_nat(2);
            return v___x_3624_;
        }
        _ => {
            let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
            v___x_3625_ = lean_unsigned_to_nat(3);
            return v___x_3625_;
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorIdx___boxed(
    mut v_x_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3627_: *mut LeanObject = core::ptr::null_mut();
    v_res_3627_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_3626_);
    lean_dec(v_x_3626_);
    return v_res_3627_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorElim___redArg(
    mut v_t_3628_: *mut LeanObject,
    mut v_k_3629_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_3628_) {
        2 => {
            let mut v_a_3630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
            v_a_3630_ = lean_ctor_get(v_t_3628_, 0);
            lean_inc(v_a_3630_);
            lean_dec_ref_known(v_t_3628_, 1);
            v___x_3631_ = lean_apply_1(v_k_3629_, v_a_3630_);
            return v___x_3631_;
        }
        3 => {
            let mut v_a_3632_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
            v_a_3632_ = lean_ctor_get(v_t_3628_, 0);
            lean_inc(v_a_3632_);
            lean_dec_ref_known(v_t_3628_, 1);
            v___x_3633_ = lean_apply_1(v_k_3629_, v_a_3632_);
            return v___x_3633_;
        }
        _ => {
            lean_dec(v_t_3628_);
            return v_k_3629_;
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorElim(
    mut v_motive_3634_: *mut LeanObject,
    mut v_ctorIdx_3635_: *mut LeanObject,
    mut v_t_3636_: *mut LeanObject,
    mut v_h_3637_: *mut LeanObject,
    mut v_k_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    v___x_3639_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3636_, v_k_3638_);
    return v___x_3639_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorElim___boxed(
    mut v_motive_3640_: *mut LeanObject,
    mut v_ctorIdx_3641_: *mut LeanObject,
    mut v_t_3642_: *mut LeanObject,
    mut v_h_3643_: *mut LeanObject,
    mut v_k_3644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3645_: *mut LeanObject = core::ptr::null_mut();
    v_res_3645_ = l_Lean_Parser_FirstTokens_ctorElim(
        v_motive_3640_,
        v_ctorIdx_3641_,
        v_t_3642_,
        v_h_3643_,
        v_k_3644_,
    );
    lean_dec(v_ctorIdx_3641_);
    return v_res_3645_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_epsilon_elim___redArg(
    mut v_t_3646_: *mut LeanObject,
    mut v_epsilon_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    v___x_3648_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3646_, v_epsilon_3647_);
    return v___x_3648_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_epsilon_elim(
    mut v_motive_3649_: *mut LeanObject,
    mut v_t_3650_: *mut LeanObject,
    mut v_h_3651_: *mut LeanObject,
    mut v_epsilon_3652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    v___x_3653_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3650_, v_epsilon_3652_);
    return v___x_3653_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_unknown_elim___redArg(
    mut v_t_3654_: *mut LeanObject,
    mut v_unknown_3655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3654_, v_unknown_3655_);
    return v___x_3656_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_unknown_elim(
    mut v_motive_3657_: *mut LeanObject,
    mut v_t_3658_: *mut LeanObject,
    mut v_h_3659_: *mut LeanObject,
    mut v_unknown_3660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    v___x_3661_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3658_, v_unknown_3660_);
    return v___x_3661_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_tokens_elim___redArg(
    mut v_t_3662_: *mut LeanObject,
    mut v_tokens_3663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    v___x_3664_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3662_, v_tokens_3663_);
    return v___x_3664_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_tokens_elim(
    mut v_motive_3665_: *mut LeanObject,
    mut v_t_3666_: *mut LeanObject,
    mut v_h_3667_: *mut LeanObject,
    mut v_tokens_3668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    v___x_3669_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3666_, v_tokens_3668_);
    return v___x_3669_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_optTokens_elim___redArg(
    mut v_t_3670_: *mut LeanObject,
    mut v_optTokens_3671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    v___x_3672_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3670_, v_optTokens_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_optTokens_elim(
    mut v_motive_3673_: *mut LeanObject,
    mut v_t_3674_: *mut LeanObject,
    mut v_h_3675_: *mut LeanObject,
    mut v_optTokens_3676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3677_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3674_, v_optTokens_3676_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedFirstTokens_default() -> *mut LeanObject {
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    v___x_3678_ = lean_box(0);
    return v___x_3678_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedFirstTokens() -> *mut LeanObject {
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    v___x_3679_ = lean_box(0);
    return v___x_3679_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_seq(
    mut v_x_3680_: *mut LeanObject,
    mut v_x_3681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_a_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3680_) {
                0 => {
                    return v_x_3681_;
                }
                3 => match lean_obj_tag(v_x_3681_) {
                    3 => {
                        v_a_3682_ = lean_ctor_get(v_x_3680_, 0);
                        lean_inc(v_a_3682_);
                        lean_dec_ref_known(v_x_3680_, 1);
                        v_a_3683_ = lean_ctor_get(v_x_3681_, 0);
                        v_isSharedCheck_3691_ = (!lean_is_exclusive(v_x_3681_)) as u8;
                        if v_isSharedCheck_3691_ == 0 {
                            v___x_3685_ = v_x_3681_;
                            v_isShared_3686_ = v_isSharedCheck_3691_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3683_);
                            lean_dec(v_x_3681_);
                            v___x_3685_ = lean_box(0);
                            v_isShared_3686_ = v_isSharedCheck_3691_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_a_3692_ = lean_ctor_get(v_x_3680_, 0);
                        lean_inc(v_a_3692_);
                        lean_dec_ref_known(v_x_3680_, 1);
                        v_a_3693_ = lean_ctor_get(v_x_3681_, 0);
                        v_isSharedCheck_3701_ = (!lean_is_exclusive(v_x_3681_)) as u8;
                        if v_isSharedCheck_3701_ == 0 {
                            v___x_3695_ = v_x_3681_;
                            v_isShared_3696_ = v_isSharedCheck_3701_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3693_);
                            lean_dec(v_x_3681_);
                            v___x_3695_ = lean_box(0);
                            v_isShared_3696_ = v_isSharedCheck_3701_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        lean_dec_ref_known(v_x_3680_, 1);
                        return v_x_3681_;
                    }
                    _ => {
                        lean_dec(v_x_3681_);
                        return v_x_3680_;
                    }
                },
                _ => {
                    lean_dec(v_x_3681_);
                    return v_x_3680_;
                }
            },
            1 => {
                v___x_3687_ = l_List_appendTR___redArg(v_a_3682_, v_a_3683_);
                if v_isShared_3686_ == 0 {
                    lean_ctor_set(v___x_3685_, 0, v___x_3687_);
                    v___x_3689_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3689_;
            }
            3 => {
                v___x_3697_ = l_List_appendTR___redArg(v_a_3692_, v_a_3693_);
                if v_isShared_3696_ == 0 {
                    lean_ctor_set(v___x_3695_, 0, v___x_3697_);
                    v___x_3699_ = v___x_3695_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
                    v___x_3699_ = v_reuseFailAlloc_3700_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_toOptional(
    mut v_x_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3702_) == 2 {
                    v_a_3703_ = lean_ctor_get(v_x_3702_, 0);
                    v_isSharedCheck_3710_ = (!lean_is_exclusive(v_x_3702_)) as u8;
                    if v_isSharedCheck_3710_ == 0 {
                        v___x_3705_ = v_x_3702_;
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3703_);
                        lean_dec(v_x_3702_);
                        v___x_3705_ = lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_3702_;
                }
            }
            1 => {
                if v_isShared_3706_ == 0 {
                    lean_ctor_set_tag(v___x_3705_, 3);
                    v___x_3708_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
                    v___x_3708_ = v_reuseFailAlloc_3709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_merge(
    mut v_x_3711_: *mut LeanObject,
    mut v_x_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_u2081_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_u2082_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v_a_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3711_) {
                0 => {
                    v___x_3718_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3712_);
                    return v___x_3718_;
                }
                2 => match lean_obj_tag(v_x_3712_) {
                    0 => {
                        v___x_3719_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3711_);
                        return v___x_3719_;
                    }
                    2 => {
                        v_a_3720_ = lean_ctor_get(v_x_3711_, 0);
                        lean_inc(v_a_3720_);
                        lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3721_ = lean_ctor_get(v_x_3712_, 0);
                        v_isSharedCheck_3729_ = (!lean_is_exclusive(v_x_3712_)) as u8;
                        if v_isSharedCheck_3729_ == 0 {
                            v___x_3723_ = v_x_3712_;
                            v_isShared_3724_ = v_isSharedCheck_3729_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3721_);
                            lean_dec(v_x_3712_);
                            v___x_3723_ = lean_box(0);
                            v_isShared_3724_ = v_isSharedCheck_3729_;
                            state = 2;
                            continue;
                        }
                    }
                    3 => {
                        v_a_3730_ = lean_ctor_get(v_x_3711_, 0);
                        lean_inc(v_a_3730_);
                        lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3731_ = lean_ctor_get(v_x_3712_, 0);
                        lean_inc(v_a_3731_);
                        lean_dec_ref_known(v_x_3712_, 1);
                        v_s_u2081_3714_ = v_a_3730_;
                        v_s_u2082_3715_ = v_a_3731_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        lean_dec_ref_known(v_x_3711_, 1);
                        lean_dec(v_x_3712_);
                        v___x_3732_ = lean_box(1);
                        return v___x_3732_;
                    }
                },
                3 => match lean_obj_tag(v_x_3712_) {
                    0 => {
                        v___x_3733_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3711_);
                        return v___x_3733_;
                    }
                    3 => {
                        v_a_3734_ = lean_ctor_get(v_x_3711_, 0);
                        lean_inc(v_a_3734_);
                        lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3735_ = lean_ctor_get(v_x_3712_, 0);
                        lean_inc(v_a_3735_);
                        lean_dec_ref_known(v_x_3712_, 1);
                        v_s_u2081_3714_ = v_a_3734_;
                        v_s_u2082_3715_ = v_a_3735_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v_a_3736_ = lean_ctor_get(v_x_3711_, 0);
                        lean_inc(v_a_3736_);
                        lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3737_ = lean_ctor_get(v_x_3712_, 0);
                        lean_inc(v_a_3737_);
                        lean_dec_ref_known(v_x_3712_, 1);
                        v_s_u2081_3714_ = v_a_3736_;
                        v_s_u2082_3715_ = v_a_3737_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        lean_dec_ref_known(v_x_3711_, 1);
                        lean_dec(v_x_3712_);
                        v___x_3738_ = lean_box(1);
                        return v___x_3738_;
                    }
                },
                _ => {
                    if lean_obj_tag(v_x_3712_) == 0 {
                        v___x_3739_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3711_);
                        return v___x_3739_;
                    } else {
                        lean_dec(v_x_3712_);
                        lean_dec(v_x_3711_);
                        v___x_3740_ = lean_box(1);
                        return v___x_3740_;
                    }
                }
            },
            1 => {
                v___x_3716_ = l_List_appendTR___redArg(v_s_u2081_3714_, v_s_u2082_3715_);
                v___x_3717_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3717_, 0, v___x_3716_);
                return v___x_3717_;
            }
            2 => {
                v___x_3725_ = l_List_appendTR___redArg(v_a_3720_, v_a_3721_);
                if v_isShared_3724_ == 0 {
                    lean_ctor_set(v___x_3723_, 0, v___x_3725_);
                    v___x_3727_ = v___x_3723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
                    v___x_3727_ = v_reuseFailAlloc_3728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(
    mut v_x_3741_: *mut LeanObject,
    mut v_x_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3742_) == 0 {
                    return v_x_3741_;
                } else {
                    v_head_3743_ = lean_ctor_get(v_x_3742_, 0);
                    v_tail_3744_ = lean_ctor_get(v_x_3742_, 1);
                    v___x_3745_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1;
                    v___x_3746_ = lean_string_append(v_x_3741_, v___x_3745_);
                    v___x_3747_ = lean_string_append(v___x_3746_, v_head_3743_);
                    v_x_3741_ = v___x_3747_;
                    v_x_3742_ = v_tail_3744_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(
    mut v_x_3749_: *mut LeanObject,
    mut v_x_3750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3751_: *mut LeanObject = core::ptr::null_mut();
    v_res_3751_ =
        l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(
            v_x_3749_, v_x_3750_,
        );
    lean_dec(v_x_3750_);
    return v_res_3751_;
}
pub unsafe fn l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(
    mut v_x_3755_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3755_) == 0 {
        let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
        v___x_3756_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0;
        return v___x_3756_;
    } else {
        let mut v_tail_3757_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3757_ = lean_ctor_get(v_x_3755_, 1);
        if lean_obj_tag(v_tail_3757_) == 0 {
            let mut v_head_3758_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
            v_head_3758_ = lean_ctor_get(v_x_3755_, 0);
            v___x_3759_ =
                l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1;
            v___x_3760_ = lean_string_append(v___x_3759_, v_head_3758_);
            v___x_3761_ =
                l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2;
            v___x_3762_ = lean_string_append(v___x_3760_, v___x_3761_);
            return v___x_3762_;
        } else {
            let mut v_head_3763_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3767_: u32 = 0;
            let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
            v_head_3763_ = lean_ctor_get(v_x_3755_, 0);
            v___x_3764_ =
                l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1;
            v___x_3765_ = lean_string_append(v___x_3764_, v_head_3763_);
            v___x_3766_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_3765_, v_tail_3757_);
            v___x_3767_ = 93;
            v___x_3768_ = lean_string_push(v___x_3766_, v___x_3767_);
            return v___x_3768_;
        }
    }
}
pub unsafe fn l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(
    mut v_x_3769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3770_: *mut LeanObject = core::ptr::null_mut();
    v_res_3770_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_3769_);
    lean_dec(v_x_3769_);
    return v_res_3770_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_toStr(mut v_x_3774_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_3774_) {
        0 => {
            let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
            v___x_3775_ = l_Lean_Parser_FirstTokens_toStr___closed__0;
            return v___x_3775_;
        }
        1 => {
            let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
            v___x_3776_ = l_Lean_Parser_FirstTokens_toStr___closed__1;
            return v___x_3776_;
        }
        2 => {
            let mut v_a_3777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
            v_a_3777_ = lean_ctor_get(v_x_3774_, 0);
            v___x_3778_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_3777_);
            return v___x_3778_;
        }
        _ => {
            let mut v_a_3779_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
            v_a_3779_ = lean_ctor_get(v_x_3774_, 0);
            v___x_3780_ = l_Lean_Parser_FirstTokens_toStr___closed__2;
            v___x_3781_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_3779_);
            v___x_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
            lean_dec_ref(v___x_3781_);
            return v___x_3782_;
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_toStr___boxed(
    mut v_x_3783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3784_: *mut LeanObject = core::ptr::null_mut();
    v_res_3784_ = l_Lean_Parser_FirstTokens_toStr(v_x_3783_);
    lean_dec(v_x_3783_);
    return v_res_3784_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__0(
    mut v___y_3787_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___y_3787_);
    return v___y_3787_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(
    mut v___y_3788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3789_: *mut LeanObject = core::ptr::null_mut();
    v_res_3789_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_3788_);
    lean_dec(v___y_3788_);
    return v_res_3789_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__1(
    mut v___y_3790_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_3790_);
    return v___y_3790_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(
    mut v___y_3791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3792_: *mut LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_3791_);
    lean_dec_ref(v___y_3791_);
    return v_res_3792_;
}
pub unsafe fn l_Lean_Parser_withFn(
    mut v_f_3806_: *mut LeanObject,
    mut v_p_3807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3808_ = lean_ctor_get(v_p_3807_, 0);
                v_fn_3809_ = lean_ctor_get(v_p_3807_, 1);
                v_isSharedCheck_3817_ = (!lean_is_exclusive(v_p_3807_)) as u8;
                if v_isSharedCheck_3817_ == 0 {
                    v___x_3811_ = v_p_3807_;
                    v_isShared_3812_ = v_isSharedCheck_3817_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fn_3809_);
                    lean_inc(v_info_3808_);
                    lean_dec(v_p_3807_);
                    v___x_3811_ = lean_box(0);
                    v_isShared_3812_ = v_isSharedCheck_3817_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3813_ = lean_apply_1(v_f_3806_, v_fn_3809_);
                if v_isShared_3812_ == 0 {
                    lean_ctor_set(v___x_3811_, 1, v___x_3813_);
                    v___x_3815_ = v___x_3811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_info_3808_);
                    lean_ctor_set(v_reuseFailAlloc_3816_, 1, v___x_3813_);
                    v___x_3815_ = v_reuseFailAlloc_3816_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_adaptCacheableContextFn(
    mut v_f_3818_: *mut LeanObject,
    mut v_p_3819_: *mut LeanObject,
    mut v_c_3820_: *mut LeanObject,
    mut v_s_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toParserModuleContext_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tokens_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3822_ = lean_ctor_get(v_c_3820_, 0);
                v_toParserModuleContext_3823_ = lean_ctor_get(v_c_3820_, 1);
                v_toCacheableParserContext_3824_ = lean_ctor_get(v_c_3820_, 2);
                v_tokens_3825_ = lean_ctor_get(v_c_3820_, 3);
                v_isSharedCheck_3834_ = (!lean_is_exclusive(v_c_3820_)) as u8;
                if v_isSharedCheck_3834_ == 0 {
                    v___x_3827_ = v_c_3820_;
                    v_isShared_3828_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tokens_3825_);
                    lean_inc(v_toCacheableParserContext_3824_);
                    lean_inc(v_toParserModuleContext_3823_);
                    lean_inc(v_toInputContext_3822_);
                    lean_dec(v_c_3820_);
                    v___x_3827_ = lean_box(0);
                    v_isShared_3828_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3829_ = lean_apply_1(v_f_3818_, v_toCacheableParserContext_3824_);
                if v_isShared_3828_ == 0 {
                    lean_ctor_set(v___x_3827_, 2, v___x_3829_);
                    v___x_3831_ = v___x_3827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_toInputContext_3822_);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_toParserModuleContext_3823_);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 2, v___x_3829_);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_tokens_3825_);
                    v___x_3831_ = v_reuseFailAlloc_3833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3832_ = lean_apply_2(v_p_3819_, v___x_3831_, v_s_3821_);
                return v___x_3832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext(
    mut v_f_3835_: *mut LeanObject,
    mut v_p_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3837_ = lean_ctor_get(v_p_3836_, 0);
                v_fn_3838_ = lean_ctor_get(v_p_3836_, 1);
                v_isSharedCheck_3846_ = (!lean_is_exclusive(v_p_3836_)) as u8;
                if v_isSharedCheck_3846_ == 0 {
                    v___x_3840_ = v_p_3836_;
                    v_isShared_3841_ = v_isSharedCheck_3846_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fn_3838_);
                    lean_inc(v_info_3837_);
                    lean_dec(v_p_3836_);
                    v___x_3840_ = lean_box(0);
                    v_isShared_3841_ = v_isSharedCheck_3846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3842_ = lean_alloc_closure(
                    l_Lean_Parser_adaptCacheableContextFn as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___x_3842_, 0, v_f_3835_);
                lean_closure_set(v___x_3842_, 1, v_fn_3838_);
                if v_isShared_3841_ == 0 {
                    lean_ctor_set(v___x_3840_, 1, v___x_3842_);
                    v___x_3844_ = v___x_3840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_info_3837_);
                    lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3842_);
                    v___x_3844_ = v_reuseFailAlloc_3845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(
    mut v_drop_3847_: *mut LeanObject,
    mut v_p_3848_: *mut LeanObject,
    mut v_c_3849_: *mut LeanObject,
    mut v_s_3850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stxStack_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v_raw_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drop_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3864_: u8 = 0;
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v_raw_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut v_unused_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3891_: u8 = 0;
    let mut v_reuseFailAlloc_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3894_: u8 = 0;
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3851_ = lean_ctor_get(v_s_3850_, 0);
                v_lhsPrec_3852_ = lean_ctor_get(v_s_3850_, 1);
                v_pos_3853_ = lean_ctor_get(v_s_3850_, 2);
                v_cache_3854_ = lean_ctor_get(v_s_3850_, 3);
                v_errorMsg_3855_ = lean_ctor_get(v_s_3850_, 4);
                v_recoveredErrors_3856_ = lean_ctor_get(v_s_3850_, 5);
                v_isSharedCheck_3895_ = (!lean_is_exclusive(v_s_3850_)) as u8;
                if v_isSharedCheck_3895_ == 0 {
                    v___x_3858_ = v_s_3850_;
                    v_isShared_3859_ = v_isSharedCheck_3895_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3856_);
                    lean_inc(v_errorMsg_3855_);
                    lean_inc(v_cache_3854_);
                    lean_inc(v_pos_3853_);
                    lean_inc(v_lhsPrec_3852_);
                    lean_inc(v_stxStack_3851_);
                    lean_dec(v_s_3850_);
                    v___x_3858_ = lean_box(0);
                    v_isShared_3859_ = v_isSharedCheck_3895_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_raw_3860_ = lean_ctor_get(v_stxStack_3851_, 0);
                v_drop_3861_ = lean_ctor_get(v_stxStack_3851_, 1);
                v_isSharedCheck_3894_ = (!lean_is_exclusive(v_stxStack_3851_)) as u8;
                if v_isSharedCheck_3894_ == 0 {
                    v___x_3863_ = v_stxStack_3851_;
                    v_isShared_3864_ = v_isSharedCheck_3894_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_drop_3861_);
                    lean_inc(v_raw_3860_);
                    lean_dec(v_stxStack_3851_);
                    v___x_3863_ = lean_box(0);
                    v_isShared_3864_ = v_isSharedCheck_3894_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3864_ == 0 {
                    lean_ctor_set(v___x_3863_, 1, v_drop_3847_);
                    v___x_3866_ = v___x_3863_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_raw_3860_);
                    lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_drop_3847_);
                    v___x_3866_ = v_reuseFailAlloc_3893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3859_ == 0 {
                    lean_ctor_set(v___x_3858_, 0, v___x_3866_);
                    v___x_3868_ = v___x_3858_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3866_);
                    lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_lhsPrec_3852_);
                    lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_pos_3853_);
                    lean_ctor_set(v_reuseFailAlloc_3892_, 3, v_cache_3854_);
                    lean_ctor_set(v_reuseFailAlloc_3892_, 4, v_errorMsg_3855_);
                    lean_ctor_set(v_reuseFailAlloc_3892_, 5, v_recoveredErrors_3856_);
                    v___x_3868_ = v_reuseFailAlloc_3892_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_s_3869_ = lean_apply_2(v_p_3848_, v_c_3849_, v___x_3868_);
                v_stxStack_3870_ = lean_ctor_get(v_s_3869_, 0);
                v_lhsPrec_3871_ = lean_ctor_get(v_s_3869_, 1);
                v_pos_3872_ = lean_ctor_get(v_s_3869_, 2);
                v_cache_3873_ = lean_ctor_get(v_s_3869_, 3);
                v_errorMsg_3874_ = lean_ctor_get(v_s_3869_, 4);
                v_recoveredErrors_3875_ = lean_ctor_get(v_s_3869_, 5);
                v_isSharedCheck_3891_ = (!lean_is_exclusive(v_s_3869_)) as u8;
                if v_isSharedCheck_3891_ == 0 {
                    v___x_3877_ = v_s_3869_;
                    v_isShared_3878_ = v_isSharedCheck_3891_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3875_);
                    lean_inc(v_errorMsg_3874_);
                    lean_inc(v_cache_3873_);
                    lean_inc(v_pos_3872_);
                    lean_inc(v_lhsPrec_3871_);
                    lean_inc(v_stxStack_3870_);
                    lean_dec(v_s_3869_);
                    v___x_3877_ = lean_box(0);
                    v_isShared_3878_ = v_isSharedCheck_3891_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_raw_3879_ = lean_ctor_get(v_stxStack_3870_, 0);
                v_isSharedCheck_3889_ = (!lean_is_exclusive(v_stxStack_3870_)) as u8;
                if v_isSharedCheck_3889_ == 0 {
                    v_unused_3890_ = lean_ctor_get(v_stxStack_3870_, 1);
                    lean_dec(v_unused_3890_);
                    v___x_3881_ = v_stxStack_3870_;
                    v_isShared_3882_ = v_isSharedCheck_3889_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_raw_3879_);
                    lean_dec(v_stxStack_3870_);
                    v___x_3881_ = lean_box(0);
                    v_isShared_3882_ = v_isSharedCheck_3889_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3882_ == 0 {
                    lean_ctor_set(v___x_3881_, 1, v_drop_3861_);
                    v___x_3884_ = v___x_3881_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_raw_3879_);
                    lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_drop_3861_);
                    v___x_3884_ = v_reuseFailAlloc_3888_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3878_ == 0 {
                    lean_ctor_set(v___x_3877_, 0, v___x_3884_);
                    v___x_3886_ = v___x_3877_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_lhsPrec_3871_);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_pos_3872_);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 3, v_cache_3873_);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 4, v_errorMsg_3874_);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 5, v_recoveredErrors_3875_);
                    v___x_3886_ = v_reuseFailAlloc_3887_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_withResetCacheFn___lam__0(
    mut v_p_3896_: *mut LeanObject,
    mut v_c_3897_: *mut LeanObject,
    mut v_s_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cache_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v_tokenCache_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parserCache_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_x27_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v_tokenCache_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut v_unused_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3940_: u8 = 0;
    let mut v_reuseFailAlloc_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cache_3899_ = lean_ctor_get(v_s_3898_, 3);
                v_stxStack_3900_ = lean_ctor_get(v_s_3898_, 0);
                v_lhsPrec_3901_ = lean_ctor_get(v_s_3898_, 1);
                v_pos_3902_ = lean_ctor_get(v_s_3898_, 2);
                v_errorMsg_3903_ = lean_ctor_get(v_s_3898_, 4);
                v_recoveredErrors_3904_ = lean_ctor_get(v_s_3898_, 5);
                v_isSharedCheck_3944_ = (!lean_is_exclusive(v_s_3898_)) as u8;
                if v_isSharedCheck_3944_ == 0 {
                    v___x_3906_ = v_s_3898_;
                    v_isShared_3907_ = v_isSharedCheck_3944_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3904_);
                    lean_inc(v_errorMsg_3903_);
                    lean_inc(v_cache_3899_);
                    lean_inc(v_pos_3902_);
                    lean_inc(v_lhsPrec_3901_);
                    lean_inc(v_stxStack_3900_);
                    lean_dec(v_s_3898_);
                    v___x_3906_ = lean_box(0);
                    v_isShared_3907_ = v_isSharedCheck_3944_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tokenCache_3908_ = lean_ctor_get(v_cache_3899_, 0);
                v_parserCache_3909_ = lean_ctor_get(v_cache_3899_, 1);
                v_isSharedCheck_3943_ = (!lean_is_exclusive(v_cache_3899_)) as u8;
                if v_isSharedCheck_3943_ == 0 {
                    v___x_3911_ = v_cache_3899_;
                    v_isShared_3912_ = v_isSharedCheck_3943_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_parserCache_3909_);
                    lean_inc(v_tokenCache_3908_);
                    lean_dec(v_cache_3899_);
                    v___x_3911_ = lean_box(0);
                    v_isShared_3912_ = v_isSharedCheck_3943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3913_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2_once),
                    _init_l_Lean_Parser_initCacheForInput___closed__2,
                );
                if v_isShared_3912_ == 0 {
                    lean_ctor_set(v___x_3911_, 1, v___x_3913_);
                    v___x_3915_ = v___x_3911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_tokenCache_3908_);
                    lean_ctor_set(v_reuseFailAlloc_3942_, 1, v___x_3913_);
                    v___x_3915_ = v_reuseFailAlloc_3942_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3907_ == 0 {
                    lean_ctor_set(v___x_3906_, 3, v___x_3915_);
                    v___x_3917_ = v___x_3906_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_stxStack_3900_);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_lhsPrec_3901_);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_pos_3902_);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 3, v___x_3915_);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_errorMsg_3903_);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 5, v_recoveredErrors_3904_);
                    v___x_3917_ = v_reuseFailAlloc_3941_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_s_x27_3918_ = lean_apply_2(v_p_3896_, v_c_3897_, v___x_3917_);
                v_cache_3919_ = lean_ctor_get(v_s_x27_3918_, 3);
                v_stxStack_3920_ = lean_ctor_get(v_s_x27_3918_, 0);
                v_lhsPrec_3921_ = lean_ctor_get(v_s_x27_3918_, 1);
                v_pos_3922_ = lean_ctor_get(v_s_x27_3918_, 2);
                v_errorMsg_3923_ = lean_ctor_get(v_s_x27_3918_, 4);
                v_recoveredErrors_3924_ = lean_ctor_get(v_s_x27_3918_, 5);
                v_isSharedCheck_3940_ = (!lean_is_exclusive(v_s_x27_3918_)) as u8;
                if v_isSharedCheck_3940_ == 0 {
                    v___x_3926_ = v_s_x27_3918_;
                    v_isShared_3927_ = v_isSharedCheck_3940_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_3924_);
                    lean_inc(v_errorMsg_3923_);
                    lean_inc(v_cache_3919_);
                    lean_inc(v_pos_3922_);
                    lean_inc(v_lhsPrec_3921_);
                    lean_inc(v_stxStack_3920_);
                    lean_dec(v_s_x27_3918_);
                    v___x_3926_ = lean_box(0);
                    v_isShared_3927_ = v_isSharedCheck_3940_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_tokenCache_3928_ = lean_ctor_get(v_cache_3919_, 0);
                v_isSharedCheck_3938_ = (!lean_is_exclusive(v_cache_3919_)) as u8;
                if v_isSharedCheck_3938_ == 0 {
                    v_unused_3939_ = lean_ctor_get(v_cache_3919_, 1);
                    lean_dec(v_unused_3939_);
                    v___x_3930_ = v_cache_3919_;
                    v_isShared_3931_ = v_isSharedCheck_3938_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_tokenCache_3928_);
                    lean_dec(v_cache_3919_);
                    v___x_3930_ = lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3938_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3931_ == 0 {
                    lean_ctor_set(v___x_3930_, 1, v_parserCache_3909_);
                    v___x_3933_ = v___x_3930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_tokenCache_3928_);
                    lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_parserCache_3909_);
                    v___x_3933_ = v_reuseFailAlloc_3937_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3927_ == 0 {
                    lean_ctor_set(v___x_3926_, 3, v___x_3933_);
                    v___x_3935_ = v___x_3926_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_stxStack_3920_);
                    lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_lhsPrec_3921_);
                    lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_pos_3922_);
                    lean_ctor_set(v_reuseFailAlloc_3936_, 3, v___x_3933_);
                    lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_errorMsg_3923_);
                    lean_ctor_set(v_reuseFailAlloc_3936_, 5, v_recoveredErrors_3924_);
                    v___x_3935_ = v_reuseFailAlloc_3936_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_withResetCacheFn(
    mut v_p_3945_: *mut LeanObject,
    mut v_a_3946_: *mut LeanObject,
    mut v_a_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    v___f_3948_ = lean_alloc_closure(
        l_Lean_Parser_withResetCacheFn___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3948_, 0, v_p_3945_);
    v___x_3949_ = lean_unsigned_to_nat(0);
    v___x_3950_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(
        v___x_3949_,
        v___f_3948_,
        v_a_3946_,
        v_a_3947_,
    );
    return v___x_3950_;
}
pub unsafe fn l_Lean_Parser_withResetCache(mut v_p_3951_: *mut LeanObject) -> *mut LeanObject {
    let mut v_info_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3952_ = lean_ctor_get(v_p_3951_, 0);
                v_fn_3953_ = lean_ctor_get(v_p_3951_, 1);
                v_isSharedCheck_3961_ = (!lean_is_exclusive(v_p_3951_)) as u8;
                if v_isSharedCheck_3961_ == 0 {
                    v___x_3955_ = v_p_3951_;
                    v_isShared_3956_ = v_isSharedCheck_3961_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fn_3953_);
                    lean_inc(v_info_3952_);
                    lean_dec(v_p_3951_);
                    v___x_3955_ = lean_box(0);
                    v_isShared_3956_ = v_isSharedCheck_3961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3957_ = lean_alloc_closure(
                    l_Lean_Parser_withResetCacheFn as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___x_3957_, 0, v_fn_3953_);
                if v_isShared_3956_ == 0 {
                    lean_ctor_set(v___x_3955_, 1, v___x_3957_);
                    v___x_3959_ = v___x_3955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_info_3952_);
                    lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3957_);
                    v___x_3959_ = v_reuseFailAlloc_3960_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_adaptUncacheableContextFn___lam__0(
    mut v_f_3962_: *mut LeanObject,
    mut v_p_3963_: *mut LeanObject,
    mut v_c_3964_: *mut LeanObject,
    mut v_s_3965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    v___x_3966_ = lean_apply_1(v_f_3962_, v_c_3964_);
    v___x_3967_ = lean_apply_2(v_p_3963_, v___x_3966_, v_s_3965_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_Parser_adaptUncacheableContextFn(
    mut v_f_3968_: *mut LeanObject,
    mut v_p_3969_: *mut LeanObject,
    mut v_a_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    v___f_3972_ = lean_alloc_closure(
        l_Lean_Parser_adaptUncacheableContextFn___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3972_, 0, v_f_3968_);
    lean_closure_set(v___f_3972_, 1, v_p_3969_);
    v___x_3973_ = l_Lean_Parser_withResetCacheFn(v___f_3972_, v_a_3970_, v_a_3971_);
    return v___x_3973_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(
    mut v_a_3974_: *mut LeanObject,
    mut v_x_3975_: *mut LeanObject,
) -> u8 {
    let mut v___x_3976_: u8 = 0;
    let mut v_key_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3975_) == 0 {
                    v___x_3976_ = 0;
                    return v___x_3976_;
                } else {
                    v_key_3977_ = lean_ctor_get(v_x_3975_, 0);
                    v_tail_3978_ = lean_ctor_get(v_x_3975_, 2);
                    v___x_3979_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_3977_, v_a_3974_);
                    if v___x_3979_ == 0 {
                        v_x_3975_ = v_tail_3978_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3979_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(
    mut v_a_3981_: *mut LeanObject,
    mut v_x_3982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3983_: u8 = 0;
    let mut v_r_3984_: *mut LeanObject = core::ptr::null_mut();
    v_res_3983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_3981_, v_x_3982_);
    lean_dec(v_x_3982_);
    lean_dec_ref(v_a_3981_);
    v_r_3984_ = lean_box((v_res_3983_) as usize);
    return v_r_3984_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_3985_: *mut LeanObject,
    mut v_x_3986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3992_: u8 = 0;
    let mut v_parserName_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: u64 = 0;
    let mut v___y_3998_: u64 = 0;
    let mut v___x_3999_: u64 = 0;
    let mut v___x_4000_: u64 = 0;
    let mut v___x_4001_: u64 = 0;
    let mut v_fold_4002_: u64 = 0;
    let mut v___x_4003_: u64 = 0;
    let mut v___x_4004_: u64 = 0;
    let mut v___x_4005_: u64 = 0;
    let mut v___x_4006_: usize = 0;
    let mut v___x_4007_: usize = 0;
    let mut v___x_4008_: usize = 0;
    let mut v___x_4009_: usize = 0;
    let mut v___x_4010_: usize = 0;
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u64 = 0;
    let mut v_hash_4018_: u64 = 0;
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3986_) == 0 {
                    return v_x_3985_;
                } else {
                    v_key_3987_ = lean_ctor_get(v_x_3986_, 0);
                    v_value_3988_ = lean_ctor_get(v_x_3986_, 1);
                    v_tail_3989_ = lean_ctor_get(v_x_3986_, 2);
                    v_isSharedCheck_4019_ = (!lean_is_exclusive(v_x_3986_)) as u8;
                    if v_isSharedCheck_4019_ == 0 {
                        v___x_3991_ = v_x_3986_;
                        v_isShared_3992_ = v_isSharedCheck_4019_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3989_);
                        lean_inc(v_value_3988_);
                        lean_inc(v_key_3987_);
                        lean_dec(v_x_3986_);
                        v___x_3991_ = lean_box(0);
                        v_isShared_3992_ = v_isSharedCheck_4019_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_parserName_3993_ = lean_ctor_get(v_key_3987_, 1);
                v_pos_3994_ = lean_ctor_get(v_key_3987_, 2);
                v___x_3995_ = lean_array_get_size(v_x_3985_);
                v___x_3996_ = l_String_instHashableRaw_hash(v_pos_3994_);
                if lean_obj_tag(v_parserName_3993_) == 0 {
                    v___x_4017_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_3998_ = v___x_4017_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4018_ = lean_ctor_get_uint64(
                        v_parserName_3993_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3998_ = v_hash_4018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3999_ = lean_uint64_mix_hash(v___x_3996_, v___y_3998_);
                v___x_4000_ = 32u64;
                v___x_4001_ = lean_uint64_shift_right(v___x_3999_, v___x_4000_);
                v_fold_4002_ = lean_uint64_xor(v___x_3999_, v___x_4001_);
                v___x_4003_ = 16u64;
                v___x_4004_ = lean_uint64_shift_right(v_fold_4002_, v___x_4003_);
                v___x_4005_ = lean_uint64_xor(v_fold_4002_, v___x_4004_);
                v___x_4006_ = lean_uint64_to_usize(v___x_4005_);
                v___x_4007_ = lean_usize_of_nat(v___x_3995_);
                v___x_4008_ = 1usize;
                v___x_4009_ = lean_usize_sub(v___x_4007_, v___x_4008_);
                v___x_4010_ = lean_usize_land(v___x_4006_, v___x_4009_);
                v___x_4011_ = lean_array_uget_borrowed(v_x_3985_, v___x_4010_);
                lean_inc(v___x_4011_);
                if v_isShared_3992_ == 0 {
                    lean_ctor_set(v___x_3991_, 2, v___x_4011_);
                    v___x_4013_ = v___x_3991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_key_3987_);
                    lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_value_3988_);
                    lean_ctor_set(v_reuseFailAlloc_4016_, 2, v___x_4011_);
                    v___x_4013_ = v_reuseFailAlloc_4016_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4014_ = lean_array_uset(v_x_3985_, v___x_4010_, v___x_4013_);
                v_x_3985_ = v___x_4014_;
                v_x_3986_ = v_tail_3989_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(
    mut v_i_4020_: *mut LeanObject,
    mut v_source_4021_: *mut LeanObject,
    mut v_target_4022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: u8 = 0;
    let mut v_es_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4023_ = lean_array_get_size(v_source_4021_);
                v___x_4024_ = lean_nat_dec_lt(v_i_4020_, v___x_4023_);
                if v___x_4024_ == 0 {
                    lean_dec_ref(v_source_4021_);
                    lean_dec(v_i_4020_);
                    return v_target_4022_;
                } else {
                    v_es_4025_ = lean_array_fget(v_source_4021_, v_i_4020_);
                    v___x_4026_ = lean_box(0);
                    v_source_4027_ = lean_array_fset(v_source_4021_, v_i_4020_, v___x_4026_);
                    v_target_4028_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_4022_, v_es_4025_);
                    v___x_4029_ = lean_unsigned_to_nat(1);
                    v___x_4030_ = lean_nat_add(v_i_4020_, v___x_4029_);
                    lean_dec(v_i_4020_);
                    v_i_4020_ = v___x_4030_;
                    v_source_4021_ = v_source_4027_;
                    v_target_4022_ = v_target_4028_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(
    mut v_data_4032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    v___x_4033_ = lean_array_get_size(v_data_4032_);
    v___x_4034_ = lean_unsigned_to_nat(2);
    v_nbuckets_4035_ = lean_nat_mul(v___x_4033_, v___x_4034_);
    v___x_4036_ = lean_unsigned_to_nat(0);
    v___x_4037_ = lean_box(0);
    v___x_4038_ = lean_mk_array(v_nbuckets_4035_, v___x_4037_);
    v___x_4039_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_4036_, v_data_4032_, v___x_4038_);
    return v___x_4039_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(
    mut v_a_4040_: *mut LeanObject,
    mut v_b_4041_: *mut LeanObject,
    mut v_x_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4042_) == 0 {
                    lean_dec(v_b_4041_);
                    lean_dec_ref(v_a_4040_);
                    return v_x_4042_;
                } else {
                    v_key_4043_ = lean_ctor_get(v_x_4042_, 0);
                    v_value_4044_ = lean_ctor_get(v_x_4042_, 1);
                    v_tail_4045_ = lean_ctor_get(v_x_4042_, 2);
                    v_isSharedCheck_4057_ = (!lean_is_exclusive(v_x_4042_)) as u8;
                    if v_isSharedCheck_4057_ == 0 {
                        v___x_4047_ = v_x_4042_;
                        v_isShared_4048_ = v_isSharedCheck_4057_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4045_);
                        lean_inc(v_value_4044_);
                        lean_inc(v_key_4043_);
                        lean_dec(v_x_4042_);
                        v___x_4047_ = lean_box(0);
                        v_isShared_4048_ = v_isSharedCheck_4057_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4049_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_4043_, v_a_4040_);
                if v___x_4049_ == 0 {
                    v___x_4050_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_4040_, v_b_4041_, v_tail_4045_);
                    if v_isShared_4048_ == 0 {
                        lean_ctor_set(v___x_4047_, 2, v___x_4050_);
                        v___x_4052_ = v___x_4047_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_key_4043_);
                        lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_value_4044_);
                        lean_ctor_set(v_reuseFailAlloc_4053_, 2, v___x_4050_);
                        v___x_4052_ = v_reuseFailAlloc_4053_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_4044_);
                    lean_dec(v_key_4043_);
                    if v_isShared_4048_ == 0 {
                        lean_ctor_set(v___x_4047_, 1, v_b_4041_);
                        lean_ctor_set(v___x_4047_, 0, v_a_4040_);
                        v___x_4055_ = v___x_4047_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4040_);
                        lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_b_4041_);
                        lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_tail_4045_);
                        v___x_4055_ = v_reuseFailAlloc_4056_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4052_;
            }
            3 => {
                return v___x_4055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(
    mut v_m_4058_: *mut LeanObject,
    mut v_a_4059_: *mut LeanObject,
    mut v_b_4060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v_parserName_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u64 = 0;
    let mut v___y_4071_: u64 = 0;
    let mut v___x_4072_: u64 = 0;
    let mut v___x_4073_: u64 = 0;
    let mut v___x_4074_: u64 = 0;
    let mut v_fold_4075_: u64 = 0;
    let mut v___x_4076_: u64 = 0;
    let mut v___x_4077_: u64 = 0;
    let mut v___x_4078_: u64 = 0;
    let mut v___x_4079_: usize = 0;
    let mut v___x_4080_: usize = 0;
    let mut v___x_4081_: usize = 0;
    let mut v___x_4082_: usize = 0;
    let mut v___x_4083_: usize = 0;
    let mut v_bkt_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v_val_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u64 = 0;
    let mut v_hash_4111_: u64 = 0;
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4061_ = lean_ctor_get(v_m_4058_, 0);
                v_buckets_4062_ = lean_ctor_get(v_m_4058_, 1);
                v_isSharedCheck_4112_ = (!lean_is_exclusive(v_m_4058_)) as u8;
                if v_isSharedCheck_4112_ == 0 {
                    v___x_4064_ = v_m_4058_;
                    v_isShared_4065_ = v_isSharedCheck_4112_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_4062_);
                    lean_inc(v_size_4061_);
                    lean_dec(v_m_4058_);
                    v___x_4064_ = lean_box(0);
                    v_isShared_4065_ = v_isSharedCheck_4112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_parserName_4066_ = lean_ctor_get(v_a_4059_, 1);
                v_pos_4067_ = lean_ctor_get(v_a_4059_, 2);
                v___x_4068_ = lean_array_get_size(v_buckets_4062_);
                v___x_4069_ = l_String_instHashableRaw_hash(v_pos_4067_);
                if lean_obj_tag(v_parserName_4066_) == 0 {
                    v___x_4110_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4071_ = v___x_4110_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4111_ = lean_ctor_get_uint64(
                        v_parserName_4066_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4071_ = v_hash_4111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4072_ = lean_uint64_mix_hash(v___x_4069_, v___y_4071_);
                v___x_4073_ = 32u64;
                v___x_4074_ = lean_uint64_shift_right(v___x_4072_, v___x_4073_);
                v_fold_4075_ = lean_uint64_xor(v___x_4072_, v___x_4074_);
                v___x_4076_ = 16u64;
                v___x_4077_ = lean_uint64_shift_right(v_fold_4075_, v___x_4076_);
                v___x_4078_ = lean_uint64_xor(v_fold_4075_, v___x_4077_);
                v___x_4079_ = lean_uint64_to_usize(v___x_4078_);
                v___x_4080_ = lean_usize_of_nat(v___x_4068_);
                v___x_4081_ = 1usize;
                v___x_4082_ = lean_usize_sub(v___x_4080_, v___x_4081_);
                v___x_4083_ = lean_usize_land(v___x_4079_, v___x_4082_);
                v_bkt_4084_ = lean_array_uget_borrowed(v_buckets_4062_, v___x_4083_);
                v___x_4085_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_4059_, v_bkt_4084_);
                if v___x_4085_ == 0 {
                    v___x_4086_ = lean_unsigned_to_nat(1);
                    v_size_x27_4087_ = lean_nat_add(v_size_4061_, v___x_4086_);
                    lean_dec(v_size_4061_);
                    lean_inc(v_bkt_4084_);
                    v___x_4088_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4088_, 0, v_a_4059_);
                    lean_ctor_set(v___x_4088_, 1, v_b_4060_);
                    lean_ctor_set(v___x_4088_, 2, v_bkt_4084_);
                    v_buckets_x27_4089_ =
                        lean_array_uset(v_buckets_4062_, v___x_4083_, v___x_4088_);
                    v___x_4090_ = lean_unsigned_to_nat(4);
                    v___x_4091_ = lean_nat_mul(v_size_x27_4087_, v___x_4090_);
                    v___x_4092_ = lean_unsigned_to_nat(3);
                    v___x_4093_ = lean_nat_div(v___x_4091_, v___x_4092_);
                    lean_dec(v___x_4091_);
                    v___x_4094_ = lean_array_get_size(v_buckets_x27_4089_);
                    v___x_4095_ = lean_nat_dec_le(v___x_4093_, v___x_4094_);
                    lean_dec(v___x_4093_);
                    if v___x_4095_ == 0 {
                        v_val_4096_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_4089_);
                        if v_isShared_4065_ == 0 {
                            lean_ctor_set(v___x_4064_, 1, v_val_4096_);
                            lean_ctor_set(v___x_4064_, 0, v_size_x27_4087_);
                            v___x_4098_ = v___x_4064_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_size_x27_4087_);
                            lean_ctor_set(v_reuseFailAlloc_4099_, 1, v_val_4096_);
                            v___x_4098_ = v_reuseFailAlloc_4099_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4065_ == 0 {
                            lean_ctor_set(v___x_4064_, 1, v_buckets_x27_4089_);
                            lean_ctor_set(v___x_4064_, 0, v_size_x27_4087_);
                            v___x_4101_ = v___x_4064_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_size_x27_4087_);
                            lean_ctor_set(v_reuseFailAlloc_4102_, 1, v_buckets_x27_4089_);
                            v___x_4101_ = v_reuseFailAlloc_4102_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_4084_);
                    v___x_4103_ = lean_box(0);
                    v_buckets_x27_4104_ =
                        lean_array_uset(v_buckets_4062_, v___x_4083_, v___x_4103_);
                    v___x_4105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_4059_, v_b_4060_, v_bkt_4084_);
                    v___x_4106_ = lean_array_uset(v_buckets_x27_4104_, v___x_4083_, v___x_4105_);
                    if v_isShared_4065_ == 0 {
                        lean_ctor_set(v___x_4064_, 1, v___x_4106_);
                        v___x_4108_ = v___x_4064_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_size_4061_);
                        lean_ctor_set(v_reuseFailAlloc_4109_, 1, v___x_4106_);
                        v___x_4108_ = v_reuseFailAlloc_4109_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4098_;
            }
            4 => {
                return v___x_4101_;
            }
            5 => {
                return v___x_4108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(
    mut v_a_4113_: *mut LeanObject,
    mut v_x_4114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4114_) == 0 {
                    v___x_4115_ = lean_box(0);
                    return v___x_4115_;
                } else {
                    v_key_4116_ = lean_ctor_get(v_x_4114_, 0);
                    v_value_4117_ = lean_ctor_get(v_x_4114_, 1);
                    v_tail_4118_ = lean_ctor_get(v_x_4114_, 2);
                    v___x_4119_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_4116_, v_a_4113_);
                    if v___x_4119_ == 0 {
                        v_x_4114_ = v_tail_4118_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4117_);
                        v___x_4121_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4121_, 0, v_value_4117_);
                        return v___x_4121_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(
    mut v_a_4122_: *mut LeanObject,
    mut v_x_4123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4124_: *mut LeanObject = core::ptr::null_mut();
    v_res_4124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_4122_, v_x_4123_);
    lean_dec(v_x_4123_);
    lean_dec_ref(v_a_4122_);
    return v_res_4124_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(
    mut v_m_4125_: *mut LeanObject,
    mut v_a_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parserName_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: u64 = 0;
    let mut v___y_4133_: u64 = 0;
    let mut v___x_4134_: u64 = 0;
    let mut v___x_4135_: u64 = 0;
    let mut v___x_4136_: u64 = 0;
    let mut v_fold_4137_: u64 = 0;
    let mut v___x_4138_: u64 = 0;
    let mut v___x_4139_: u64 = 0;
    let mut v___x_4140_: u64 = 0;
    let mut v___x_4141_: usize = 0;
    let mut v___x_4142_: usize = 0;
    let mut v___x_4143_: usize = 0;
    let mut v___x_4144_: usize = 0;
    let mut v___x_4145_: usize = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: u64 = 0;
    let mut v_hash_4149_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4127_ = lean_ctor_get(v_m_4125_, 1);
                v_parserName_4128_ = lean_ctor_get(v_a_4126_, 1);
                v_pos_4129_ = lean_ctor_get(v_a_4126_, 2);
                v___x_4130_ = lean_array_get_size(v_buckets_4127_);
                v___x_4131_ = l_String_instHashableRaw_hash(v_pos_4129_);
                if lean_obj_tag(v_parserName_4128_) == 0 {
                    v___x_4148_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4133_ = v___x_4148_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4149_ = lean_ctor_get_uint64(
                        v_parserName_4128_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4133_ = v_hash_4149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4134_ = lean_uint64_mix_hash(v___x_4131_, v___y_4133_);
                v___x_4135_ = 32u64;
                v___x_4136_ = lean_uint64_shift_right(v___x_4134_, v___x_4135_);
                v_fold_4137_ = lean_uint64_xor(v___x_4134_, v___x_4136_);
                v___x_4138_ = 16u64;
                v___x_4139_ = lean_uint64_shift_right(v_fold_4137_, v___x_4138_);
                v___x_4140_ = lean_uint64_xor(v_fold_4137_, v___x_4139_);
                v___x_4141_ = lean_uint64_to_usize(v___x_4140_);
                v___x_4142_ = lean_usize_of_nat(v___x_4130_);
                v___x_4143_ = 1usize;
                v___x_4144_ = lean_usize_sub(v___x_4142_, v___x_4143_);
                v___x_4145_ = lean_usize_land(v___x_4141_, v___x_4144_);
                v___x_4146_ = lean_array_uget_borrowed(v_buckets_4127_, v___x_4145_);
                v___x_4147_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_4126_, v___x_4146_);
                return v___x_4147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(
    mut v_m_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4152_: *mut LeanObject = core::ptr::null_mut();
    v_res_4152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_4150_, v_a_4151_);
    lean_dec_ref(v_a_4151_);
    lean_dec_ref(v_m_4150_);
    return v_res_4152_;
}
pub unsafe fn l_Lean_Parser_withCacheFn(
    mut v_parserName_4153_: *mut LeanObject,
    mut v_p_4154_: *mut LeanObject,
    mut v_c_4155_: *mut LeanObject,
    mut v_s_4156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cache_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v_parserCache_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newPos_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_raw_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initStackSz_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stxStack_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v_tokenCache_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parserCache_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4197_: u8 = 0;
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4207_: u8 = 0;
    let mut v_isSharedCheck_4208_: u8 = 0;
    let mut v_reuseFailAlloc_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut v_unused_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cache_4157_ = lean_ctor_get(v_s_4156_, 3);
                lean_inc_ref(v_cache_4157_);
                v_toCacheableParserContext_4158_ = lean_ctor_get(v_c_4155_, 2);
                v_stxStack_4159_ = lean_ctor_get(v_s_4156_, 0);
                v_pos_4160_ = lean_ctor_get(v_s_4156_, 2);
                v_recoveredErrors_4161_ = lean_ctor_get(v_s_4156_, 5);
                v_isSharedCheck_4210_ = (!lean_is_exclusive(v_s_4156_)) as u8;
                if v_isSharedCheck_4210_ == 0 {
                    v_unused_4211_ = lean_ctor_get(v_s_4156_, 4);
                    lean_dec(v_unused_4211_);
                    v_unused_4212_ = lean_ctor_get(v_s_4156_, 3);
                    lean_dec(v_unused_4212_);
                    v_unused_4213_ = lean_ctor_get(v_s_4156_, 1);
                    lean_dec(v_unused_4213_);
                    v___x_4163_ = v_s_4156_;
                    v_isShared_4164_ = v_isSharedCheck_4210_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_4161_);
                    lean_inc(v_pos_4160_);
                    lean_inc(v_stxStack_4159_);
                    lean_dec(v_s_4156_);
                    v___x_4163_ = lean_box(0);
                    v_isShared_4164_ = v_isSharedCheck_4210_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_parserCache_4165_ = lean_ctor_get(v_cache_4157_, 1);
                lean_inc(v_pos_4160_);
                lean_inc_ref(v_toCacheableParserContext_4158_);
                v_key_4166_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v_key_4166_, 0, v_toCacheableParserContext_4158_);
                lean_ctor_set(v_key_4166_, 1, v_parserName_4153_);
                lean_ctor_set(v_key_4166_, 2, v_pos_4160_);
                v___x_4167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_4165_, v_key_4166_);
                if lean_obj_tag(v___x_4167_) == 1 {
                    lean_dec_ref_known(v_key_4166_, 3);
                    lean_dec(v_pos_4160_);
                    lean_dec_ref(v_c_4155_);
                    lean_dec_ref(v_p_4154_);
                    v_val_4168_ = lean_ctor_get(v___x_4167_, 0);
                    lean_inc(v_val_4168_);
                    lean_dec_ref_known(v___x_4167_, 1);
                    v_stx_4169_ = lean_ctor_get(v_val_4168_, 0);
                    lean_inc(v_stx_4169_);
                    v_lhsPrec_4170_ = lean_ctor_get(v_val_4168_, 1);
                    lean_inc(v_lhsPrec_4170_);
                    v_newPos_4171_ = lean_ctor_get(v_val_4168_, 2);
                    lean_inc(v_newPos_4171_);
                    v_errorMsg_4172_ = lean_ctor_get(v_val_4168_, 3);
                    lean_inc(v_errorMsg_4172_);
                    lean_dec(v_val_4168_);
                    v___x_4173_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_4159_, v_stx_4169_);
                    if v_isShared_4164_ == 0 {
                        lean_ctor_set(v___x_4163_, 4, v_errorMsg_4172_);
                        lean_ctor_set(v___x_4163_, 2, v_newPos_4171_);
                        lean_ctor_set(v___x_4163_, 1, v_lhsPrec_4170_);
                        lean_ctor_set(v___x_4163_, 0, v___x_4173_);
                        v___x_4175_ = v___x_4163_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
                        lean_ctor_set(v_reuseFailAlloc_4176_, 1, v_lhsPrec_4170_);
                        lean_ctor_set(v_reuseFailAlloc_4176_, 2, v_newPos_4171_);
                        lean_ctor_set(v_reuseFailAlloc_4176_, 3, v_cache_4157_);
                        lean_ctor_set(v_reuseFailAlloc_4176_, 4, v_errorMsg_4172_);
                        lean_ctor_set(v_reuseFailAlloc_4176_, 5, v_recoveredErrors_4161_);
                        v___x_4175_ = v_reuseFailAlloc_4176_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4167_);
                    v_raw_4177_ = lean_ctor_get(v_stxStack_4159_, 0);
                    v_initStackSz_4178_ = lean_array_get_size(v_raw_4177_);
                    v___x_4179_ = lean_unsigned_to_nat(0);
                    v___x_4180_ = lean_box(0);
                    if v_isShared_4164_ == 0 {
                        lean_ctor_set(v___x_4163_, 4, v___x_4180_);
                        lean_ctor_set(v___x_4163_, 1, v___x_4179_);
                        v___x_4182_ = v___x_4163_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_stxStack_4159_);
                        lean_ctor_set(v_reuseFailAlloc_4209_, 1, v___x_4179_);
                        lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_pos_4160_);
                        lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_cache_4157_);
                        lean_ctor_set(v_reuseFailAlloc_4209_, 4, v___x_4180_);
                        lean_ctor_set(v_reuseFailAlloc_4209_, 5, v_recoveredErrors_4161_);
                        v___x_4182_ = v_reuseFailAlloc_4209_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4175_;
            }
            3 => {
                v_s_4183_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(
                    v_initStackSz_4178_,
                    v_p_4154_,
                    v_c_4155_,
                    v___x_4182_,
                );
                v_cache_4184_ = lean_ctor_get(v_s_4183_, 3);
                v_stxStack_4185_ = lean_ctor_get(v_s_4183_, 0);
                v_lhsPrec_4186_ = lean_ctor_get(v_s_4183_, 1);
                v_pos_4187_ = lean_ctor_get(v_s_4183_, 2);
                v_errorMsg_4188_ = lean_ctor_get(v_s_4183_, 4);
                v_recoveredErrors_4189_ = lean_ctor_get(v_s_4183_, 5);
                v_isSharedCheck_4208_ = (!lean_is_exclusive(v_s_4183_)) as u8;
                if v_isSharedCheck_4208_ == 0 {
                    v___x_4191_ = v_s_4183_;
                    v_isShared_4192_ = v_isSharedCheck_4208_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_recoveredErrors_4189_);
                    lean_inc(v_errorMsg_4188_);
                    lean_inc(v_cache_4184_);
                    lean_inc(v_pos_4187_);
                    lean_inc(v_lhsPrec_4186_);
                    lean_inc(v_stxStack_4185_);
                    lean_dec(v_s_4183_);
                    v___x_4191_ = lean_box(0);
                    v_isShared_4192_ = v_isSharedCheck_4208_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_tokenCache_4193_ = lean_ctor_get(v_cache_4184_, 0);
                v_parserCache_4194_ = lean_ctor_get(v_cache_4184_, 1);
                v_isSharedCheck_4207_ = (!lean_is_exclusive(v_cache_4184_)) as u8;
                if v_isSharedCheck_4207_ == 0 {
                    v___x_4196_ = v_cache_4184_;
                    v_isShared_4197_ = v_isSharedCheck_4207_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_parserCache_4194_);
                    lean_inc(v_tokenCache_4193_);
                    lean_dec(v_cache_4184_);
                    v___x_4196_ = lean_box(0);
                    v_isShared_4197_ = v_isSharedCheck_4207_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4198_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4185_);
                lean_inc(v_errorMsg_4188_);
                lean_inc(v_pos_4187_);
                lean_inc(v_lhsPrec_4186_);
                v___x_4199_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4199_, 0, v___x_4198_);
                lean_ctor_set(v___x_4199_, 1, v_lhsPrec_4186_);
                lean_ctor_set(v___x_4199_, 2, v_pos_4187_);
                lean_ctor_set(v___x_4199_, 3, v_errorMsg_4188_);
                v___x_4200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_4194_, v_key_4166_, v___x_4199_);
                if v_isShared_4197_ == 0 {
                    lean_ctor_set(v___x_4196_, 1, v___x_4200_);
                    v___x_4202_ = v___x_4196_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_tokenCache_4193_);
                    lean_ctor_set(v_reuseFailAlloc_4206_, 1, v___x_4200_);
                    v___x_4202_ = v_reuseFailAlloc_4206_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4192_ == 0 {
                    lean_ctor_set(v___x_4191_, 3, v___x_4202_);
                    v___x_4204_ = v___x_4191_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_stxStack_4185_);
                    lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_lhsPrec_4186_);
                    lean_ctor_set(v_reuseFailAlloc_4205_, 2, v_pos_4187_);
                    lean_ctor_set(v_reuseFailAlloc_4205_, 3, v___x_4202_);
                    lean_ctor_set(v_reuseFailAlloc_4205_, 4, v_errorMsg_4188_);
                    lean_ctor_set(v_reuseFailAlloc_4205_, 5, v_recoveredErrors_4189_);
                    v___x_4204_ = v_reuseFailAlloc_4205_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(
    mut v_00_u03b2_4214_: *mut LeanObject,
    mut v_m_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_4215_, v_a_4216_);
    return v___x_4217_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(
    mut v_00_u03b2_4218_: *mut LeanObject,
    mut v_m_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4221_: *mut LeanObject = core::ptr::null_mut();
    v_res_4221_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(
            v_00_u03b2_4218_,
            v_m_4219_,
            v_a_4220_,
        );
    lean_dec_ref(v_a_4220_);
    lean_dec_ref(v_m_4219_);
    return v_res_4221_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(
    mut v_00_u03b2_4222_: *mut LeanObject,
    mut v_m_4223_: *mut LeanObject,
    mut v_a_4224_: *mut LeanObject,
    mut v_b_4225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    v___x_4226_ =
        l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(
            v_m_4223_, v_a_4224_, v_b_4225_,
        );
    return v___x_4226_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(
    mut v_00_u03b2_4227_: *mut LeanObject,
    mut v_a_4228_: *mut LeanObject,
    mut v_x_4229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_4228_, v_x_4229_);
    return v___x_4230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(
    mut v_00_u03b2_4231_: *mut LeanObject,
    mut v_a_4232_: *mut LeanObject,
    mut v_x_4233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4234_: *mut LeanObject = core::ptr::null_mut();
    v_res_4234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_4231_, v_a_4232_, v_x_4233_);
    lean_dec(v_x_4233_);
    lean_dec_ref(v_a_4232_);
    return v_res_4234_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(
    mut v_00_u03b2_4235_: *mut LeanObject,
    mut v_a_4236_: *mut LeanObject,
    mut v_x_4237_: *mut LeanObject,
) -> u8 {
    let mut v___x_4238_: u8 = 0;
    v___x_4238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_4236_, v_x_4237_);
    return v___x_4238_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(
    mut v_00_u03b2_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_x_4241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4242_: u8 = 0;
    let mut v_r_4243_: *mut LeanObject = core::ptr::null_mut();
    v_res_4242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_4239_, v_a_4240_, v_x_4241_);
    lean_dec(v_x_4241_);
    lean_dec_ref(v_a_4240_);
    v_r_4243_ = lean_box((v_res_4242_) as usize);
    return v_r_4243_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(
    mut v_00_u03b2_4244_: *mut LeanObject,
    mut v_data_4245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    v___x_4246_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_4245_);
    return v___x_4246_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(
    mut v_00_u03b2_4247_: *mut LeanObject,
    mut v_a_4248_: *mut LeanObject,
    mut v_b_4249_: *mut LeanObject,
    mut v_x_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    v___x_4251_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_4248_, v_b_4249_, v_x_4250_);
    return v___x_4251_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4252_: *mut LeanObject,
    mut v_i_4253_: *mut LeanObject,
    mut v_source_4254_: *mut LeanObject,
    mut v_target_4255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    v___x_4256_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_4253_, v_source_4254_, v_target_4255_);
    return v___x_4256_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_4257_: *mut LeanObject,
    mut v_x_4258_: *mut LeanObject,
    mut v_x_4259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    v___x_4260_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_4258_, v_x_4259_);
    return v___x_4260_;
}
pub unsafe fn l_Lean_Parser_withCache(
    mut v_parserName_4261_: *mut LeanObject,
    mut v_p_4262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4267_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_4263_ = lean_ctor_get(v_p_4262_, 0);
                v_fn_4264_ = lean_ctor_get(v_p_4262_, 1);
                v_isSharedCheck_4272_ = (!lean_is_exclusive(v_p_4262_)) as u8;
                if v_isSharedCheck_4272_ == 0 {
                    v___x_4266_ = v_p_4262_;
                    v_isShared_4267_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fn_4264_);
                    lean_inc(v_info_4263_);
                    lean_dec(v_p_4262_);
                    v___x_4266_ = lean_box(0);
                    v_isShared_4267_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4268_ =
                    lean_alloc_closure(l_Lean_Parser_withCacheFn as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___x_4268_, 0, v_parserName_4261_);
                lean_closure_set(v___x_4268_, 1, v_fn_4264_);
                if v_isShared_4267_ == 0 {
                    lean_ctor_set(v___x_4266_, 1, v___x_4268_);
                    v___x_4270_ = v___x_4266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_info_4263_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 1, v___x_4268_);
                    v___x_4270_ = v_reuseFailAlloc_4271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1()
-> *mut LeanObject {
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    v___x_4280_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1;
    v___x_4281_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2;
    v___x_4282_ = l_Lean_addBuiltinDocString(v___x_4280_, v___x_4281_);
    return v___x_4282_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(
    mut v_a_4283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4284_: *mut LeanObject = core::ptr::null_mut();
    v_res_4284_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
    return v_res_4284_;
}
pub unsafe fn l_Lean_Parser_ParserFn_run(
    mut v_p_4289_: *mut LeanObject,
    mut v_ictx_4290_: *mut LeanObject,
    mut v_pmctx_4291_: *mut LeanObject,
    mut v_tokens_4292_: *mut LeanObject,
    mut v_s_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_Parser_ParserFn_run___closed__0;
    v___x_4295_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4295_, 0, v_ictx_4290_);
    lean_ctor_set(v___x_4295_, 1, v_pmctx_4291_);
    lean_ctor_set(v___x_4295_, 2, v___x_4294_);
    lean_ctor_set(v___x_4295_, 3, v_tokens_4292_);
    v___x_4296_ = lean_apply_2(v_p_4289_, v___x_4295_, v_s_4293_);
    return v___x_4296_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
    lean_mark_persistent(l_Lean_Parser_maxPrec);
    l_Lean_Parser_argPrec = _init_l_Lean_Parser_argPrec();
    lean_mark_persistent(l_Lean_Parser_argPrec);
    l_Lean_Parser_leadPrec = _init_l_Lean_Parser_leadPrec();
    lean_mark_persistent(l_Lean_Parser_leadPrec);
    l_Lean_Parser_minPrec = _init_l_Lean_Parser_minPrec();
    lean_mark_persistent(l_Lean_Parser_minPrec);
    l_Lean_Parser_instInhabitedInputContext = _init_l_Lean_Parser_instInhabitedInputContext();
    lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext);
    l_Lean_Parser_instInhabitedFirstTokens_default =
        _init_l_Lean_Parser_instInhabitedFirstTokens_default();
    lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens_default);
    l_Lean_Parser_instInhabitedFirstTokens = _init_l_Lean_Parser_instInhabitedFirstTokens();
    lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens);
    res = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_InputContext_endPos__valid___autoParam =
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam();
    lean_mark_persistent(l_Lean_Parser_InputContext_endPos__valid___autoParam);
    l_Lean_Parser_InputContext_mk___auto__1 = _init_l_Lean_Parser_InputContext_mk___auto__1();
    lean_mark_persistent(l_Lean_Parser_InputContext_mk___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_DocString_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Parser_Types(builtin);
}
