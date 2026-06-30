// Lean compiler output
// Module: Lean.Parser.Types
// Imports: Lean.Data.Trie Lean.DocString.Extension Init.Data.String.OrderInstances
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_pop, lean_array_push,
    lean_array_size, lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_append, lean_string_dec_eq, lean_string_dec_lt,
    lean_string_push, lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next, lean_string_utf8_next_fast,
    lean_string_utf8_prev, lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
    l_Array_extract___redArg, l_Char_utf8Size, l_Lean_Syntax_getPos_x3f, l_Lean_mkAtom,
    l_String_decEq___boxed,
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
pub static mut l_Lean_Parser_maxPrec: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_argPrec: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_leadPrec: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_minPrec: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value:
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
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value)
            as *mut leanh::LeanObject,
        12783917532758215986 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value)
            as *mut leanh::LeanObject,
        3488656302031949961 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_InputContext_endPos__valid___autoParam: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_instInhabitedInputContext___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_instInhabitedInputContext___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedInputContext___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_instInhabitedInputContext___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_instInhabitedInputContext___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_instInhabitedInputContext___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_instInhabitedInputContext___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_instInhabitedInputContext: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_InputContext_mk___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_instBEqCacheableParserContext___closed__0_value:
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
    m_fun: l_Lean_Parser_instBEqCacheableParserContext_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instBEqCacheableParserContext___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqCacheableParserContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instBEqCacheableParserContext: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqCacheableParserContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instCoeParserContextInputContext___closed__0_value:
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
    m_fun: l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instCoeParserContextInputContext___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instCoeParserContextInputContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instCoeParserContextInputContext: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instCoeParserContextInputContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instInhabitedError_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_instInhabitedInputContext___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_instInhabitedError_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedError_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedError_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedError_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedError: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedError_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instBEqError___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_instBEqError_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_instBEqError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqError___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instBEqError: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqError___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0_value:
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
    m_fun: l_String_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Error_toString___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Error_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Error_toString___closed__1_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Error_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_toString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Error_instToString___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Error_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Error_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_Error_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Error_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instBEqParserCacheKey___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Parser_instBEqParserCacheKey_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instBEqParserCacheKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqParserCacheKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instBEqParserCacheKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instBEqParserCacheKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instHashableParserCacheKey___closed__0_value:
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
    m_fun: l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instHashableParserCacheKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instHashableParserCacheKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instHashableParserCacheKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instHashableParserCacheKey___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_initCacheForInput___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_initCacheForInput___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_initCacheForInput___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_initCacheForInput___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_initCacheForInput___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_initCacheForInput___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_SyntaxStack_empty___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Parser_SyntaxStack_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_SyntaxStack_empty___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_SyntaxStack_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_SyntaxStack_empty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_SyntaxStack_back___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_SyntaxStack_back___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_back___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_SyntaxStack_back___closed__1_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_SyntaxStack_back___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_back___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_SyntaxStack_back___closed__2_value: leanh::LeanStringObject<42> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_SyntaxStack_back___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_back___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_SyntaxStack_back___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_SyntaxStack_back___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_SyntaxStack_get_x21___closed__0_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_get_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_SyntaxStack_get_x21___closed__1_value: leanh::LeanStringObject<42> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_get_x21___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_SyntaxStack_get_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value:
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
    m_fun: l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_SyntaxStack_instHAppendArraySyntax: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_ParserState_allErrors___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Parser_ParserState_allErrors___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_allErrors___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_ParserState_mkEOIError___closed__0_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105,
        110, 112, 117, 116, 0,
    ],
};
static mut l_Lean_Parser_ParserState_mkEOIError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkEOIError___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0_value:
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
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1_value:
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
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2_value:
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
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_instInhabitedParserFn___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Parser_instInhabitedParserFn___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instInhabitedParserFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedParserFn: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedFirstTokens_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_instInhabitedFirstTokens: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1_value:
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
    m_data: [91, 0],
};
static mut l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2_value:
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
    m_data: [93, 0],
};
static mut l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_FirstTokens_toStr___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_FirstTokens_toStr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_toStr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_FirstTokens_toStr___closed__1_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_FirstTokens_toStr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_toStr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_FirstTokens_toStr___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_FirstTokens_toStr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_toStr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_FirstTokens_instToString___closed__0_value:
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
    m_fun: l_Lean_Parser_FirstTokens_toStr___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_FirstTokens_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_FirstTokens_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_FirstTokens_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value:
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
    m_fun: l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instInhabitedParserInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value:
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
    m_fun: l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_instInhabitedParserInfo_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_instInhabitedParserInfo_default___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedParserInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedParserInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_instInhabitedParser_default___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_instInhabitedParserFn___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_instInhabitedParser_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParser_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedParser_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParser_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedParser: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedParser_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [119, 105, 116, 104, 67, 97, 99, 104, 101, 0]};
static mut l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value) as *mut leanh::LeanObject,13015283372816199961 as *mut leanh::LeanObject] };
static mut l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value: leanh::LeanStringObject<542> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 542, m_capacity: 542, m_length: 541, m_data: [82, 117, 110, 32, 96, 112, 96, 32, 97, 110, 100, 32, 114, 101, 99, 111, 114, 100, 32, 114, 101, 115, 117, 108, 116, 32, 105, 110, 32, 112, 97, 114, 115, 101, 114, 32, 99, 97, 99, 104, 101, 32, 102, 111, 114, 32, 97, 110, 121, 32, 102, 117, 114, 116, 104, 101, 114, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 116, 104, 105, 115, 32, 96, 112, 97, 114, 115, 101, 114, 78, 97, 109, 101, 96, 44, 32, 112, 97, 114, 115, 101, 114, 32, 99, 111, 110, 116, 101, 120, 116, 44, 32, 97, 110, 100, 32, 112, 97, 114, 115, 101, 114, 32, 115, 116, 97, 116, 101, 46, 10, 96, 112, 96, 32, 99, 97, 110, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 32, 115, 121, 110, 116, 97, 120, 32, 115, 116, 97, 99, 107, 32, 101, 108, 101, 109, 101, 110, 116, 115, 32, 112, 117, 115, 104, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 116, 104, 101, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 32, 105, 110, 32, 111, 114, 100, 101, 114, 32, 116, 111, 32, 109, 97, 107, 101, 32, 99, 97, 99, 104, 105, 110, 103, 32, 105, 110, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 111, 102, 32, 112, 97, 114, 115, 101, 114, 32, 104, 105, 115, 116, 111, 114, 121, 46, 10, 65, 115, 32, 116, 104, 105, 115, 32, 101, 120, 99, 108, 117, 100, 101, 115, 32, 116, 114, 97, 105, 108, 105, 110, 103, 32, 112, 97, 114, 115, 101, 114, 115, 32, 102, 114, 111, 109, 32, 98, 101, 105, 110, 103, 32, 99, 97, 99, 104, 101, 100, 44, 32, 119, 101, 32, 97, 108, 115, 111, 32, 114, 101, 115, 101, 116, 32, 96, 108, 104, 115, 80, 114, 101, 99, 96, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 110, 111, 116, 32, 114, 101, 97, 100, 32, 98, 117, 116, 32, 115, 101, 116, 32, 98, 121, 32, 108, 101, 97, 100, 105, 110, 103, 32, 112, 97, 114, 115, 101, 114, 115, 44, 32, 116, 111, 32, 48, 10, 105, 110, 32, 111, 114, 100, 101, 114, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 99, 97, 99, 104, 101, 32, 104, 105, 116, 115, 46, 32, 70, 105, 110, 97, 108, 108, 121, 44, 32, 96, 101, 114, 114, 111, 114, 77, 115, 103, 96, 32, 105, 115, 32, 97, 108, 115, 111, 32, 114, 101, 115, 101, 116, 32, 116, 111, 32, 96, 110, 111, 110, 101, 96, 32, 97, 115, 32, 97, 32, 108, 101, 97, 100, 105, 110, 103, 32, 112, 97, 114, 115, 101, 114, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 99, 97, 108, 108, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 10, 112, 108, 97, 99, 101, 32, 105, 102, 32, 116, 104, 101, 114, 101, 32, 119, 97, 115, 32, 97, 110, 32, 101, 114, 114, 111, 114, 46, 10, 0]};
static mut l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_ParserFn_run___closed__0_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 8) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_ParserFn_run___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_ParserFn_run___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Parser_mkAtom(
    mut v_info_2149_: *mut leanh::LeanObject,
    mut v_val_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2151_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2151_, 0, v_info_2149_);
    leanh::lean_ctor_set(v___x_2151_, 1, v_val_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Lean_Parser_mkIdent(
    mut v_info_2152_: *mut leanh::LeanObject,
    mut v_rawVal_2153_: *mut leanh::LeanObject,
    mut v_val_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2155_ = leanh::lean_box(0);
    v___x_2156_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2156_, 0, v_info_2152_);
    leanh::lean_ctor_set(v___x_2156_, 1, v_rawVal_2153_);
    leanh::lean_ctor_set(v___x_2156_, 2, v_val_2154_);
    leanh::lean_ctor_set(v___x_2156_, 3, v___x_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Lean_Parser_getNext(
    mut v_input_2157_: *mut leanh::LeanObject,
    mut v_pos_2158_: *mut leanh::LeanObject,
) -> u32 {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u32 = 0;
    v___x_2159_ = lean_string_utf8_next(v_input_2157_, v_pos_2158_);
    v___x_2160_ = lean_string_utf8_get(v_input_2157_, v___x_2159_);
    leanh::lean_dec(v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn l_Lean_Parser_getNext___boxed(
    mut v_input_2161_: *mut leanh::LeanObject,
    mut v_pos_2162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2163_: u32 = 0;
    let mut v_r_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2163_ = l_Lean_Parser_getNext(v_input_2161_, v_pos_2162_);
    leanh::lean_dec(v_pos_2162_);
    leanh::lean_dec_ref(v_input_2161_);
    v_r_2164_ = leanh::lean_box_uint32(v_res_2163_);
    return v_r_2164_;
}
pub unsafe fn _init_l_Lean_Parser_maxPrec() -> *mut leanh::LeanObject {
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = leanh::lean_unsigned_to_nat(1024);
    return v___x_2165_;
}
pub unsafe fn _init_l_Lean_Parser_argPrec() -> *mut leanh::LeanObject {
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2166_ = leanh::lean_unsigned_to_nat(1023);
    return v___x_2166_;
}
pub unsafe fn _init_l_Lean_Parser_leadPrec() -> *mut leanh::LeanObject {
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2167_ = leanh::lean_unsigned_to_nat(1022);
    return v___x_2167_;
}
pub unsafe fn _init_l_Lean_Parser_minPrec() -> *mut leanh::LeanObject {
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = leanh::lean_unsigned_to_nat(10);
    return v___x_2168_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2169_: *mut leanh::LeanObject,
    mut v_x_2170_: *mut leanh::LeanObject,
    mut v_x_2171_: *mut leanh::LeanObject,
    mut v_x_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2173_ = leanh::lean_ctor_get(v_x_2169_, 0);
                v_vs_2174_ = leanh::lean_ctor_get(v_x_2169_, 1);
                v_isSharedCheck_2198_ = (!leanh::lean_is_exclusive(v_x_2169_)) as u8;
                if v_isSharedCheck_2198_ == 0 {
                    v___x_2176_ = v_x_2169_;
                    v_isShared_2177_ = v_isSharedCheck_2198_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2174_);
                    leanh::lean_inc(v_ks_2173_);
                    leanh::lean_dec(v_x_2169_);
                    v___x_2176_ = leanh::lean_box(0);
                    v_isShared_2177_ = v_isSharedCheck_2198_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2178_ = lean_array_get_size(v_ks_2173_);
                v___x_2179_ = lean_nat_dec_lt(v_x_2170_, v___x_2178_);
                if v___x_2179_ == 0 {
                    leanh::lean_dec(v_x_2170_);
                    v___x_2180_ = lean_array_push(v_ks_2173_, v_x_2171_);
                    v___x_2181_ = lean_array_push(v_vs_2174_, v_x_2172_);
                    if v_isShared_2177_ == 0 {
                        leanh::lean_ctor_set(v___x_2176_, 1, v___x_2181_);
                        leanh::lean_ctor_set(v___x_2176_, 0, v___x_2180_);
                        v___x_2183_ = v___x_2176_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2184_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2180_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_2181_);
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
                            v_reuseFailAlloc_2192_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_ks_2173_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_vs_2174_);
                            v___x_2188_ = v_reuseFailAlloc_2192_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2193_ = lean_array_fset(v_ks_2173_, v_x_2170_, v_x_2171_);
                        v___x_2194_ = lean_array_fset(v_vs_2174_, v_x_2170_, v_x_2172_);
                        leanh::lean_dec(v_x_2170_);
                        if v_isShared_2177_ == 0 {
                            leanh::lean_ctor_set(v___x_2176_, 1, v___x_2194_);
                            leanh::lean_ctor_set(v___x_2176_, 0, v___x_2193_);
                            v___x_2196_ = v___x_2176_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2197_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2193_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2194_);
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
                v___x_2189_ = leanh::lean_unsigned_to_nat(1);
                v___x_2190_ = lean_nat_add(v_x_2170_, v___x_2189_);
                leanh::lean_dec(v_x_2170_);
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
    mut v_n_2199_: *mut leanh::LeanObject,
    mut v_k_2200_: *mut leanh::LeanObject,
    mut v_v_2201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2202_ = leanh::lean_unsigned_to_nat(0);
    v___x_2203_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2199_, v___x_2202_, v_k_2200_, v_v_2201_);
    return v___x_2203_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: u64 = 0;
    v___x_2204_ = leanh::lean_unsigned_to_nat(1723);
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
    v___x_2210_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0);
    v___x_2211_ = lean_usize_sub(v___x_2210_, v___x_2209_);
    return v___x_2211_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2212_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2212_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(
    mut v_x_2213_: *mut leanh::LeanObject,
    mut v_x_2214_: usize,
    mut v_x_2215_: usize,
    mut v_x_2216_: *mut leanh::LeanObject,
    mut v_x_2217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: usize = 0;
    let mut v___x_2220_: usize = 0;
    let mut v___x_2221_: usize = 0;
    let mut v___x_2222_: usize = 0;
    let mut v_j_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v_v_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_node_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v___x_2254_: usize = 0;
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_unused_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: u8 = 0;
    let mut v_ks_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: usize = 0;
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut v_reuseFailAlloc_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2213_) == 0 {
                    v_es_2218_ = leanh::lean_ctor_get(v_x_2213_, 0);
                    v___x_2219_ = 5usize;
                    v___x_2220_ = 1usize;
                    v___x_2221_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1);
                    v___x_2222_ = lean_usize_land(v_x_2214_, v___x_2221_);
                    v_j_2223_ = lean_usize_to_nat(v___x_2222_);
                    v___x_2224_ = lean_array_get_size(v_es_2218_);
                    v___x_2225_ = lean_nat_dec_lt(v_j_2223_, v___x_2224_);
                    if v___x_2225_ == 0 {
                        leanh::lean_dec(v_j_2223_);
                        leanh::lean_dec(v_x_2217_);
                        leanh::lean_dec(v_x_2216_);
                        return v_x_2213_;
                    } else {
                        leanh::lean_inc_ref(v_es_2218_);
                        v_isSharedCheck_2262_ = (!leanh::lean_is_exclusive(v_x_2213_)) as u8;
                        if v_isSharedCheck_2262_ == 0 {
                            v_unused_2263_ = leanh::lean_ctor_get(v_x_2213_, 0);
                            leanh::lean_dec(v_unused_2263_);
                            v___x_2227_ = v_x_2213_;
                            v_isShared_2228_ = v_isSharedCheck_2262_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2213_);
                            v___x_2227_ = leanh::lean_box(0);
                            v_isShared_2228_ = v_isSharedCheck_2262_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2264_ = leanh::lean_ctor_get(v_x_2213_, 0);
                    v_vs_2265_ = leanh::lean_ctor_get(v_x_2213_, 1);
                    v_isSharedCheck_2285_ = (!leanh::lean_is_exclusive(v_x_2213_)) as u8;
                    if v_isSharedCheck_2285_ == 0 {
                        v___x_2267_ = v_x_2213_;
                        v_isShared_2268_ = v_isSharedCheck_2285_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2265_);
                        leanh::lean_inc(v_ks_2264_);
                        leanh::lean_dec(v_x_2213_);
                        v___x_2267_ = leanh::lean_box(0);
                        v_isShared_2268_ = v_isSharedCheck_2285_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2229_ = lean_array_fget(v_es_2218_, v_j_2223_);
                v___x_2230_ = leanh::lean_box(0);
                v_xs_x27_2231_ = lean_array_fset(v_es_2218_, v_j_2223_, v___x_2230_);
                match leanh::lean_obj_tag(v_v_2229_) {
                    0 => {
                        v_key_2238_ = leanh::lean_ctor_get(v_v_2229_, 0);
                        v_val_2239_ = leanh::lean_ctor_get(v_v_2229_, 1);
                        v_isSharedCheck_2249_ = (!leanh::lean_is_exclusive(v_v_2229_)) as u8;
                        if v_isSharedCheck_2249_ == 0 {
                            v___x_2241_ = v_v_2229_;
                            v_isShared_2242_ = v_isSharedCheck_2249_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2239_);
                            leanh::lean_inc(v_key_2238_);
                            leanh::lean_dec(v_v_2229_);
                            v___x_2241_ = leanh::lean_box(0);
                            v_isShared_2242_ = v_isSharedCheck_2249_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2250_ = leanh::lean_ctor_get(v_v_2229_, 0);
                        v_isSharedCheck_2260_ = (!leanh::lean_is_exclusive(v_v_2229_)) as u8;
                        if v_isSharedCheck_2260_ == 0 {
                            v___x_2252_ = v_v_2229_;
                            v_isShared_2253_ = v_isSharedCheck_2260_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2250_);
                            leanh::lean_dec(v_v_2229_);
                            v___x_2252_ = leanh::lean_box(0);
                            v_isShared_2253_ = v_isSharedCheck_2260_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2261_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2261_, 0, v_x_2216_);
                        leanh::lean_ctor_set(v___x_2261_, 1, v_x_2217_);
                        v___y_2233_ = v___x_2261_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2234_ = lean_array_fset(v_xs_x27_2231_, v_j_2223_, v___y_2233_);
                leanh::lean_dec(v_j_2223_);
                if v_isShared_2228_ == 0 {
                    leanh::lean_ctor_set(v___x_2227_, 0, v___x_2234_);
                    v___x_2236_ = v___x_2227_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
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
                    leanh::lean_del_object(v___x_2241_);
                    v___x_2244_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2238_,
                        v_val_2239_,
                        v_x_2216_,
                        v_x_2217_,
                    );
                    v___x_2245_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
                    v___y_2233_ = v___x_2245_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2239_);
                    leanh::lean_dec(v_key_2238_);
                    if v_isShared_2242_ == 0 {
                        leanh::lean_ctor_set(v___x_2241_, 1, v_x_2217_);
                        leanh::lean_ctor_set(v___x_2241_, 0, v_x_2216_);
                        v___x_2247_ = v___x_2241_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2248_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_x_2216_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_x_2217_);
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
                    leanh::lean_ctor_set(v___x_2252_, 0, v___x_2256_);
                    v___x_2258_ = v___x_2252_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
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
                    v_reuseFailAlloc_2284_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_ks_2264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_vs_2265_);
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
                    v___x_2282_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2283_ = lean_nat_dec_lt(v___x_2281_, v___x_2282_);
                    leanh::lean_dec(v___x_2281_);
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
                    v_ks_2274_ = leanh::lean_ctor_get(v_newNode_2271_, 0);
                    leanh::lean_inc_ref(v_ks_2274_);
                    v_vs_2275_ = leanh::lean_ctor_get(v_newNode_2271_, 1);
                    leanh::lean_inc_ref(v_vs_2275_);
                    leanh::lean_dec_ref(v_newNode_2271_);
                    v___x_2276_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2);
                    v___x_2278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_x_2215_, v_ks_2274_, v_vs_2275_, v___x_2276_, v___x_2277_);
                    leanh::lean_dec_ref(v_vs_2275_);
                    leanh::lean_dec_ref(v_ks_2274_);
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
    mut v_keys_2287_: *mut leanh::LeanObject,
    mut v_vals_2288_: *mut leanh::LeanObject,
    mut v_i_2289_: *mut leanh::LeanObject,
    mut v_entries_2290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v_k_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: u64 = 0;
    let mut v_h_2297_: usize = 0;
    let mut v___x_2298_: usize = 0;
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: usize = 0;
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: usize = 0;
    let mut v_h_2303_: usize = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: u64 = 0;
    let mut v_hash_2308_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2291_ = lean_array_get_size(v_keys_2287_);
                v___x_2292_ = lean_nat_dec_lt(v_i_2289_, v___x_2291_);
                if v___x_2292_ == 0 {
                    leanh::lean_dec(v_i_2289_);
                    return v_entries_2290_;
                } else {
                    v_k_2293_ = lean_array_fget_borrowed(v_keys_2287_, v_i_2289_);
                    v_v_2294_ = lean_array_fget_borrowed(v_vals_2288_, v_i_2289_);
                    if leanh::lean_obj_tag(v_k_2293_) == 0 {
                        v___x_2307_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_2296_ = v___x_2307_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2308_ = leanh::lean_ctor_get_uint64(
                            v_k_2293_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                v___x_2299_ = leanh::lean_unsigned_to_nat(1);
                v___x_2300_ = 1usize;
                v___x_2301_ = lean_usize_sub(v_depth_2286_, v___x_2300_);
                v___x_2302_ = lean_usize_mul(v___x_2298_, v___x_2301_);
                v_h_2303_ = lean_usize_shift_right(v_h_2297_, v___x_2302_);
                v___x_2304_ = lean_nat_add(v_i_2289_, v___x_2299_);
                leanh::lean_dec(v_i_2289_);
                leanh::lean_inc(v_v_2294_);
                leanh::lean_inc(v_k_2293_);
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
    mut v_depth_2309_: *mut leanh::LeanObject,
    mut v_keys_2310_: *mut leanh::LeanObject,
    mut v_vals_2311_: *mut leanh::LeanObject,
    mut v_i_2312_: *mut leanh::LeanObject,
    mut v_entries_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2314_: usize = 0;
    let mut v_res_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2314_ = leanh::lean_unbox_usize(v_depth_2309_);
    leanh::lean_dec(v_depth_2309_);
    v_res_2315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2314_, v_keys_2310_, v_vals_2311_, v_i_2312_, v_entries_2313_);
    leanh::lean_dec_ref(v_vals_2311_);
    leanh::lean_dec_ref(v_keys_2310_);
    return v_res_2315_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_2316_: *mut leanh::LeanObject,
    mut v_x_2317_: *mut leanh::LeanObject,
    mut v_x_2318_: *mut leanh::LeanObject,
    mut v_x_2319_: *mut leanh::LeanObject,
    mut v_x_2320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_371__boxed_2321_: usize = 0;
    let mut v_x_372__boxed_2322_: usize = 0;
    let mut v_res_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_371__boxed_2321_ = leanh::lean_unbox_usize(v_x_2317_);
    leanh::lean_dec(v_x_2317_);
    v_x_372__boxed_2322_ = leanh::lean_unbox_usize(v_x_2318_);
    leanh::lean_dec(v_x_2318_);
    v_res_2323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_2316_, v_x_371__boxed_2321_, v_x_372__boxed_2322_, v_x_2319_, v_x_2320_);
    return v_res_2323_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(
    mut v_x_2324_: *mut leanh::LeanObject,
    mut v_x_2325_: *mut leanh::LeanObject,
    mut v_x_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2328_: u64 = 0;
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u64 = 0;
    let mut v_hash_2333_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2325_) == 0 {
                    v___x_2332_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2328_ = v___x_2332_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2333_ = leanh::lean_ctor_get_uint64(
                        v_x_2325_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_s_2334_: *mut leanh::LeanObject,
    mut v_k_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = leanh::lean_box(0);
    v___x_2337_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_s_2334_, v_k_2335_, v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(
    mut v_00_u03b2_2338_: *mut leanh::LeanObject,
    mut v_x_2339_: *mut leanh::LeanObject,
    mut v_x_2340_: *mut leanh::LeanObject,
    mut v_x_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
    return v___x_2342_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(
    mut v_00_u03b2_2343_: *mut leanh::LeanObject,
    mut v_x_2344_: *mut leanh::LeanObject,
    mut v_x_2345_: usize,
    mut v_x_2346_: usize,
    mut v_x_2347_: *mut leanh::LeanObject,
    mut v_x_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_, v_x_2348_);
    return v___x_2349_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_2350_: *mut leanh::LeanObject,
    mut v_x_2351_: *mut leanh::LeanObject,
    mut v_x_2352_: *mut leanh::LeanObject,
    mut v_x_2353_: *mut leanh::LeanObject,
    mut v_x_2354_: *mut leanh::LeanObject,
    mut v_x_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_570__boxed_2356_: usize = 0;
    let mut v_x_571__boxed_2357_: usize = 0;
    let mut v_res_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_570__boxed_2356_ = leanh::lean_unbox_usize(v_x_2352_);
    leanh::lean_dec(v_x_2352_);
    v_x_571__boxed_2357_ = leanh::lean_unbox_usize(v_x_2353_);
    leanh::lean_dec(v_x_2353_);
    v_res_2358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_2350_, v_x_2351_, v_x_570__boxed_2356_, v_x_571__boxed_2357_, v_x_2354_, v_x_2355_);
    return v_res_2358_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2359_: *mut leanh::LeanObject,
    mut v_n_2360_: *mut leanh::LeanObject,
    mut v_k_2361_: *mut leanh::LeanObject,
    mut v_v_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v_n_2360_, v_k_2361_, v_v_2362_);
    return v___x_2363_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2364_: *mut leanh::LeanObject,
    mut v_depth_2365_: usize,
    mut v_keys_2366_: *mut leanh::LeanObject,
    mut v_vals_2367_: *mut leanh::LeanObject,
    mut v_heq_2368_: *mut leanh::LeanObject,
    mut v_i_2369_: *mut leanh::LeanObject,
    mut v_entries_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_2365_, v_keys_2366_, v_vals_2367_, v_i_2369_, v_entries_2370_);
    return v___x_2371_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2372_: *mut leanh::LeanObject,
    mut v_depth_2373_: *mut leanh::LeanObject,
    mut v_keys_2374_: *mut leanh::LeanObject,
    mut v_vals_2375_: *mut leanh::LeanObject,
    mut v_heq_2376_: *mut leanh::LeanObject,
    mut v_i_2377_: *mut leanh::LeanObject,
    mut v_entries_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2379_: usize = 0;
    let mut v_res_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2379_ = leanh::lean_unbox_usize(v_depth_2373_);
    leanh::lean_dec(v_depth_2373_);
    v_res_2380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(v_00_u03b2_2372_, v_depth_boxed_2379_, v_keys_2374_, v_vals_2375_, v_heq_2376_, v_i_2377_, v_entries_2378_);
    leanh::lean_dec_ref(v_vals_2375_);
    leanh::lean_dec_ref(v_keys_2374_);
    return v_res_2380_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2381_: *mut leanh::LeanObject,
    mut v_x_2382_: *mut leanh::LeanObject,
    mut v_x_2383_: *mut leanh::LeanObject,
    mut v_x_2384_: *mut leanh::LeanObject,
    mut v_x_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2382_, v_x_2383_, v_x_2384_, v_x_2385_);
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10;
    v___x_2414_ = l_Lean_mkAtom(v___x_2413_);
    return v___x_2414_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2415_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2428_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2429_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5;
    v___x_2430_ = lean_array_push(v___x_2429_, v___x_2428_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17,
    );
    v___x_2432_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15;
    v___x_2433_ = leanh::lean_box(2);
    v___x_2434_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2434_, 0, v___x_2433_);
    leanh::lean_ctor_set(v___x_2434_, 1, v___x_2432_);
    leanh::lean_ctor_set(v___x_2434_, 2, v___x_2431_);
    return v___x_2434_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18,
    );
    v___x_2436_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2439_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2442_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2445_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16;
    v___x_2448_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23,
    );
    v___x_2451_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11;
    v___x_2452_ = leanh::lean_box(2);
    v___x_2453_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2453_, 0, v___x_2452_);
    leanh::lean_ctor_set(v___x_2453_, 1, v___x_2451_);
    leanh::lean_ctor_set(v___x_2453_, 2, v___x_2450_);
    return v___x_2453_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2454_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25,
    );
    v___x_2458_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9;
    v___x_2459_ = leanh::lean_box(2);
    v___x_2460_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2460_, 0, v___x_2459_);
    leanh::lean_ctor_set(v___x_2460_, 1, v___x_2458_);
    leanh::lean_ctor_set(v___x_2460_, 2, v___x_2457_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27,
    );
    v___x_2465_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7;
    v___x_2466_ = leanh::lean_box(2);
    v___x_2467_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2467_, 0, v___x_2466_);
    leanh::lean_ctor_set(v___x_2467_, 1, v___x_2465_);
    leanh::lean_ctor_set(v___x_2467_, 2, v___x_2464_);
    return v___x_2467_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29,
    );
    v___x_2472_ = l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4;
    v___x_2473_ = leanh::lean_box(2);
    v___x_2474_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    leanh::lean_ctor_set(v___x_2474_, 1, v___x_2472_);
    leanh::lean_ctor_set(v___x_2474_, 2, v___x_2471_);
    return v___x_2474_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_endPos__valid___autoParam()
-> *mut leanh::LeanObject {
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30,
    );
    return v___x_2475_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedInputContext___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
    v___x_2478_ = lean_string_utf8_byte_size(v___x_2477_);
    return v___x_2478_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedInputContext___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__1_once),
        _init_l_Lean_Parser_instInhabitedInputContext___closed__1,
    );
    v___x_2480_ = l_Lean_instInhabitedFileMap_default;
    v___x_2481_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
    v___x_2482_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2482_, 0, v___x_2481_);
    leanh::lean_ctor_set(v___x_2482_, 1, v___x_2481_);
    leanh::lean_ctor_set(v___x_2482_, 2, v___x_2480_);
    leanh::lean_ctor_set(v___x_2482_, 3, v___x_2479_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedInputContext() -> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_instInhabitedInputContext___closed__2_once),
        _init_l_Lean_Parser_instInhabitedInputContext___closed__2,
    );
    return v___x_2483_;
}
pub unsafe fn _init_l_Lean_Parser_InputContext_mk___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once
        ),
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30,
    );
    return v___x_2484_;
}
pub unsafe fn l_Lean_Parser_InputContext_mk___redArg(
    mut v_input_2485_: *mut leanh::LeanObject,
    mut v_fileName_2486_: *mut leanh::LeanObject,
    mut v_endPos_2487_: *mut leanh::LeanObject,
    mut v_fileMap_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2489_, 0, v_input_2485_);
    leanh::lean_ctor_set(v___x_2489_, 1, v_fileName_2486_);
    leanh::lean_ctor_set(v___x_2489_, 2, v_fileMap_2488_);
    leanh::lean_ctor_set(v___x_2489_, 3, v_endPos_2487_);
    return v___x_2489_;
}
pub unsafe fn l_Lean_Parser_InputContext_mk(
    mut v_input_2490_: *mut leanh::LeanObject,
    mut v_fileName_2491_: *mut leanh::LeanObject,
    mut v_endPos_2492_: *mut leanh::LeanObject,
    mut v_endPos__valid_2493_: *mut leanh::LeanObject,
    mut v_fileMap_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2495_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2495_, 0, v_input_2490_);
    leanh::lean_ctor_set(v___x_2495_, 1, v_fileName_2491_);
    leanh::lean_ctor_set(v___x_2495_, 2, v_fileMap_2494_);
    leanh::lean_ctor_set(v___x_2495_, 3, v_endPos_2492_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Parser_InputContext_input(
    mut v_c_2496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputString_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inputString_2497_ = leanh::lean_ctor_get(v_c_2496_, 0);
    v_endPos_2498_ = leanh::lean_ctor_get(v_c_2496_, 3);
    v___x_2499_ = leanh::lean_unsigned_to_nat(0);
    v___x_2500_ = lean_string_utf8_extract(v_inputString_2497_, v___x_2499_, v_endPos_2498_);
    return v___x_2500_;
}
pub unsafe fn l_Lean_Parser_InputContext_input___boxed(
    mut v_c_2501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Lean_Parser_InputContext_input(v_c_2501_);
    leanh::lean_dec_ref(v_c_2501_);
    return v_res_2502_;
}
pub unsafe fn l_Lean_Parser_InputContext_atEnd(
    mut v_c_2503_: *mut leanh::LeanObject,
    mut v_p_2504_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_endPos_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: u8 = 0;
    v_endPos_2505_ = leanh::lean_ctor_get(v_c_2503_, 3);
    v___x_2506_ = lean_nat_dec_le(v_endPos_2505_, v_p_2504_);
    return v___x_2506_;
}
pub unsafe fn l_Lean_Parser_InputContext_atEnd___boxed(
    mut v_c_2507_: *mut leanh::LeanObject,
    mut v_p_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2509_: u8 = 0;
    let mut v_r_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Parser_InputContext_atEnd(v_c_2507_, v_p_2508_);
    leanh::lean_dec(v_p_2508_);
    leanh::lean_dec_ref(v_c_2507_);
    v_r_2510_ = leanh::lean_box((v_res_2509_) as usize);
    return v_r_2510_;
}
pub unsafe fn l_Lean_Parser_InputContext_get(
    mut v_c_2511_: *mut leanh::LeanObject,
    mut v_p_2512_: *mut leanh::LeanObject,
) -> u32 {
    let mut v_inputString_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u32 = 0;
    v_inputString_2513_ = leanh::lean_ctor_get(v_c_2511_, 0);
    v___x_2514_ = lean_string_utf8_get(v_inputString_2513_, v_p_2512_);
    return v___x_2514_;
}
pub unsafe fn l_Lean_Parser_InputContext_get___boxed(
    mut v_c_2515_: *mut leanh::LeanObject,
    mut v_p_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2517_: u32 = 0;
    let mut v_r_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2517_ = l_Lean_Parser_InputContext_get(v_c_2515_, v_p_2516_);
    leanh::lean_dec(v_p_2516_);
    leanh::lean_dec_ref(v_c_2515_);
    v_r_2518_ = leanh::lean_box_uint32(v_res_2517_);
    return v_r_2518_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_2519_: *mut leanh::LeanObject,
    mut v_x_2520_: *mut leanh::LeanObject,
    mut v_h__1_2521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2522_ = leanh::lean_apply_2(v_h__1_2521_, v_x_2519_, v_x_2520_);
    return v___x_2522_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_2523_: *mut leanh::LeanObject,
    mut v_x_2524_: *mut leanh::LeanObject,
    mut v_x_2525_: *mut leanh::LeanObject,
    mut v_h__1_2526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = leanh::lean_apply_2(v_h__1_2526_, v_x_2524_, v_x_2525_);
    return v___x_2527_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27___redArg(
    mut v_c_2528_: *mut leanh::LeanObject,
    mut v_p_2529_: *mut leanh::LeanObject,
) -> u32 {
    let mut v_inputString_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u32 = 0;
    v_inputString_2530_ = leanh::lean_ctor_get(v_c_2528_, 0);
    v___x_2531_ = lean_string_utf8_get_fast(v_inputString_2530_, v_p_2529_);
    return v___x_2531_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27___redArg___boxed(
    mut v_c_2532_: *mut leanh::LeanObject,
    mut v_p_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2534_: u32 = 0;
    let mut v_r_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_2532_, v_p_2533_);
    leanh::lean_dec(v_p_2533_);
    leanh::lean_dec_ref(v_c_2532_);
    v_r_2535_ = leanh::lean_box_uint32(v_res_2534_);
    return v_r_2535_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27(
    mut v_c_2536_: *mut leanh::LeanObject,
    mut v_p_2537_: *mut leanh::LeanObject,
    mut v_h_2538_: *mut leanh::LeanObject,
) -> u32 {
    let mut v_inputString_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u32 = 0;
    v_inputString_2539_ = leanh::lean_ctor_get(v_c_2536_, 0);
    v___x_2540_ = lean_string_utf8_get_fast(v_inputString_2539_, v_p_2537_);
    return v___x_2540_;
}
pub unsafe fn l_Lean_Parser_InputContext_get_x27___boxed(
    mut v_c_2541_: *mut leanh::LeanObject,
    mut v_p_2542_: *mut leanh::LeanObject,
    mut v_h_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2544_: u32 = 0;
    let mut v_r_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_Lean_Parser_InputContext_get_x27(v_c_2541_, v_p_2542_, v_h_2543_);
    leanh::lean_dec(v_p_2542_);
    leanh::lean_dec_ref(v_c_2541_);
    v_r_2545_ = leanh::lean_box_uint32(v_res_2544_);
    return v_r_2545_;
}
pub unsafe fn l_Lean_Parser_InputContext_next(
    mut v_c_2546_: *mut leanh::LeanObject,
    mut v_p_2547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputString_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inputString_2548_ = leanh::lean_ctor_get(v_c_2546_, 0);
    v___x_2549_ = lean_string_utf8_next(v_inputString_2548_, v_p_2547_);
    return v___x_2549_;
}
pub unsafe fn l_Lean_Parser_InputContext_next___boxed(
    mut v_c_2550_: *mut leanh::LeanObject,
    mut v_p_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2552_ = l_Lean_Parser_InputContext_next(v_c_2550_, v_p_2551_);
    leanh::lean_dec(v_p_2551_);
    leanh::lean_dec_ref(v_c_2550_);
    return v_res_2552_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27___redArg(
    mut v_c_2553_: *mut leanh::LeanObject,
    mut v_p_2554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputString_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inputString_2555_ = leanh::lean_ctor_get(v_c_2553_, 0);
    v___x_2556_ = lean_string_utf8_next_fast(v_inputString_2555_, v_p_2554_);
    return v___x_2556_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27___redArg___boxed(
    mut v_c_2557_: *mut leanh::LeanObject,
    mut v_p_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_2557_, v_p_2558_);
    leanh::lean_dec(v_p_2558_);
    leanh::lean_dec_ref(v_c_2557_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27(
    mut v_c_2560_: *mut leanh::LeanObject,
    mut v_p_2561_: *mut leanh::LeanObject,
    mut v_h_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputString_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inputString_2563_ = leanh::lean_ctor_get(v_c_2560_, 0);
    v___x_2564_ = lean_string_utf8_next_fast(v_inputString_2563_, v_p_2561_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_Parser_InputContext_next_x27___boxed(
    mut v_c_2565_: *mut leanh::LeanObject,
    mut v_p_2566_: *mut leanh::LeanObject,
    mut v_h_2567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lean_Parser_InputContext_next_x27(v_c_2565_, v_p_2566_, v_h_2567_);
    leanh::lean_dec(v_p_2566_);
    leanh::lean_dec_ref(v_c_2565_);
    return v_res_2568_;
}
pub unsafe fn l_Lean_Parser_InputContext_extract(
    mut v_c_2569_: *mut leanh::LeanObject,
    mut v_a_2570_: *mut leanh::LeanObject,
    mut v_a_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputString_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inputString_2572_ = leanh::lean_ctor_get(v_c_2569_, 0);
    v___x_2573_ = lean_string_utf8_extract(v_inputString_2572_, v_a_2570_, v_a_2571_);
    return v___x_2573_;
}
pub unsafe fn l_Lean_Parser_InputContext_extract___boxed(
    mut v_c_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
    mut v_a_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Lean_Parser_InputContext_extract(v_c_2574_, v_a_2575_, v_a_2576_);
    leanh::lean_dec(v_a_2576_);
    leanh::lean_dec(v_a_2575_);
    leanh::lean_dec_ref(v_c_2574_);
    return v_res_2577_;
}
pub unsafe fn l_Lean_Parser_InputContext_substring(
    mut v_c_2578_: *mut leanh::LeanObject,
    mut v_startPos_2579_: *mut leanh::LeanObject,
    mut v_stopPos_2580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputString_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    v_inputString_2581_ = leanh::lean_ctor_get(v_c_2578_, 0);
    v_endPos_2582_ = leanh::lean_ctor_get(v_c_2578_, 3);
    v___x_2583_ = lean_nat_dec_le(v_stopPos_2580_, v_endPos_2582_);
    if v___x_2583_ == 0 {
        let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stopPos_2580_);
        leanh::lean_inc(v_endPos_2582_);
        leanh::lean_inc_ref(v_inputString_2581_);
        v___x_2584_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2584_, 0, v_inputString_2581_);
        leanh::lean_ctor_set(v___x_2584_, 1, v_startPos_2579_);
        leanh::lean_ctor_set(v___x_2584_, 2, v_endPos_2582_);
        return v___x_2584_;
    } else {
        let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_inputString_2581_);
        v___x_2585_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2585_, 0, v_inputString_2581_);
        leanh::lean_ctor_set(v___x_2585_, 1, v_startPos_2579_);
        leanh::lean_ctor_set(v___x_2585_, 2, v_stopPos_2580_);
        return v___x_2585_;
    }
}
pub unsafe fn l_Lean_Parser_InputContext_substring___boxed(
    mut v_c_2586_: *mut leanh::LeanObject,
    mut v_startPos_2587_: *mut leanh::LeanObject,
    mut v_stopPos_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2589_ =
        l_Lean_Parser_InputContext_substring(v_c_2586_, v_startPos_2587_, v_stopPos_2588_);
    leanh::lean_dec_ref(v_c_2586_);
    return v_res_2589_;
}
pub unsafe fn l_Lean_Parser_InputContext_getNext(
    mut v_input_2590_: *mut leanh::LeanObject,
    mut v_pos_2591_: *mut leanh::LeanObject,
) -> u32 {
    let mut v_inputString_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u32 = 0;
    v_inputString_2592_ = leanh::lean_ctor_get(v_input_2590_, 0);
    v___x_2593_ = lean_string_utf8_next(v_inputString_2592_, v_pos_2591_);
    v___x_2594_ = lean_string_utf8_get(v_inputString_2592_, v___x_2593_);
    leanh::lean_dec(v___x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_Parser_InputContext_getNext___boxed(
    mut v_input_2595_: *mut leanh::LeanObject,
    mut v_pos_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2597_: u32 = 0;
    let mut v_r_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2597_ = l_Lean_Parser_InputContext_getNext(v_input_2595_, v_pos_2596_);
    leanh::lean_dec(v_pos_2596_);
    leanh::lean_dec_ref(v_input_2595_);
    v_r_2598_ = leanh::lean_box_uint32(v_res_2597_);
    return v_r_2598_;
}
pub unsafe fn l_Lean_Parser_InputContext_prev(
    mut v_c_2599_: *mut leanh::LeanObject,
    mut v_pos_2600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputString_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inputString_2601_ = leanh::lean_ctor_get(v_c_2599_, 0);
    v___x_2602_ = lean_string_utf8_prev(v_inputString_2601_, v_pos_2600_);
    return v___x_2602_;
}
pub unsafe fn l_Lean_Parser_InputContext_prev___boxed(
    mut v_c_2603_: *mut leanh::LeanObject,
    mut v_pos_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2605_ = l_Lean_Parser_InputContext_prev(v_c_2603_, v_pos_2604_);
    leanh::lean_dec(v_pos_2604_);
    leanh::lean_dec_ref(v_c_2603_);
    return v_res_2605_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(
    mut v_x_2606_: *mut leanh::LeanObject,
    mut v_x_2607_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2606_) == 0 {
        if leanh::lean_obj_tag(v_x_2607_) == 0 {
            let mut v___x_2608_: u8 = 0;
            v___x_2608_ = 1;
            return v___x_2608_;
        } else {
            let mut v___x_2609_: u8 = 0;
            v___x_2609_ = 0;
            return v___x_2609_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_2607_) == 0 {
            let mut v___x_2610_: u8 = 0;
            v___x_2610_ = 0;
            return v___x_2610_;
        } else {
            let mut v_val_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2613_: u8 = 0;
            v_val_2611_ = leanh::lean_ctor_get(v_x_2606_, 0);
            v_val_2612_ = leanh::lean_ctor_get(v_x_2607_, 0);
            v___x_2613_ = lean_nat_dec_eq(v_val_2611_, v_val_2612_);
            return v___x_2613_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0___boxed(
    mut v_x_2614_: *mut leanh::LeanObject,
    mut v_x_2615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2616_: u8 = 0;
    let mut v_r_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2616_ =
        l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(
            v_x_2614_, v_x_2615_,
        );
    leanh::lean_dec(v_x_2615_);
    leanh::lean_dec(v_x_2614_);
    v_r_2617_ = leanh::lean_box((v_res_2616_) as usize);
    return v_r_2617_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(
    mut v_x_2618_: *mut leanh::LeanObject,
    mut v_x_2619_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2618_) == 0 {
        if leanh::lean_obj_tag(v_x_2619_) == 0 {
            let mut v___x_2620_: u8 = 0;
            v___x_2620_ = 1;
            return v___x_2620_;
        } else {
            let mut v___x_2621_: u8 = 0;
            v___x_2621_ = 0;
            return v___x_2621_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_2619_) == 0 {
            let mut v___x_2622_: u8 = 0;
            v___x_2622_ = 0;
            return v___x_2622_;
        } else {
            let mut v_val_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2625_: u8 = 0;
            v_val_2623_ = leanh::lean_ctor_get(v_x_2618_, 0);
            v_val_2624_ = leanh::lean_ctor_get(v_x_2619_, 0);
            v___x_2625_ = lean_string_dec_eq(v_val_2623_, v_val_2624_);
            return v___x_2625_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___boxed(
    mut v_x_2626_: *mut leanh::LeanObject,
    mut v_x_2627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2628_: u8 = 0;
    let mut v_r_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2628_ =
        l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(
            v_x_2626_, v_x_2627_,
        );
    leanh::lean_dec(v_x_2627_);
    leanh::lean_dec(v_x_2626_);
    v_r_2629_ = leanh::lean_box((v_res_2628_) as usize);
    return v_r_2629_;
}
pub unsafe fn l_Lean_Parser_instBEqCacheableParserContext_beq(
    mut v_x_2630_: *mut leanh::LeanObject,
    mut v_x_2631_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_prec_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotDepth_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressInsideQuot_2634_: u8 = 0;
    let mut v_savedPos_x3f_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenTk_x3f_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotDepth_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressInsideQuot_2639_: u8 = 0;
    let mut v_savedPos_x3f_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenTk_x3f_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: u8 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: u8 = 0;
    let mut v___x_2646_: u8 = 0;
    let mut v___x_2647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_prec_2632_ = leanh::lean_ctor_get(v_x_2630_, 0);
                v_quotDepth_2633_ = leanh::lean_ctor_get(v_x_2630_, 1);
                v_suppressInsideQuot_2634_ = leanh::lean_ctor_get_uint8(
                    v_x_2630_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                v_savedPos_x3f_2635_ = leanh::lean_ctor_get(v_x_2630_, 2);
                v_forbiddenTk_x3f_2636_ = leanh::lean_ctor_get(v_x_2630_, 3);
                v_prec_2637_ = leanh::lean_ctor_get(v_x_2631_, 0);
                v_quotDepth_2638_ = leanh::lean_ctor_get(v_x_2631_, 1);
                v_suppressInsideQuot_2639_ = leanh::lean_ctor_get_uint8(
                    v_x_2631_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                v_savedPos_x3f_2640_ = leanh::lean_ctor_get(v_x_2631_, 2);
                v_forbiddenTk_x3f_2641_ = leanh::lean_ctor_get(v_x_2631_, 3);
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
    mut v_x_2648_: *mut leanh::LeanObject,
    mut v_x_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2650_: u8 = 0;
    let mut v_r_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2650_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_x_2648_, v_x_2649_);
    leanh::lean_dec_ref(v_x_2649_);
    leanh::lean_dec_ref(v_x_2648_);
    v_r_2651_ = leanh::lean_box((v_res_2650_) as usize);
    return v_r_2651_;
}
pub unsafe fn l_Lean_Parser_instCoeParserContextInputContext___lam__0(
    mut v_x_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toInputContext_2655_ = leanh::lean_ctor_get(v_x_2654_, 0);
    leanh::lean_inc_ref(v_toInputContext_2655_);
    return v_toInputContext_2655_;
}
pub unsafe fn l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(
    mut v_x_2656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_2656_);
    leanh::lean_dec_ref(v_x_2656_);
    return v_res_2657_;
}
pub unsafe fn l_Lean_Parser_ParserContext_setEndPos___redArg(
    mut v_c_2660_: *mut leanh::LeanObject,
    mut v_endPos_2661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toParserModuleContext_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tokens_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v_inputString_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2681_: u8 = 0;
    let mut v_unused_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2662_ = leanh::lean_ctor_get(v_c_2660_, 0);
                v_toParserModuleContext_2663_ = leanh::lean_ctor_get(v_c_2660_, 1);
                v_toCacheableParserContext_2664_ = leanh::lean_ctor_get(v_c_2660_, 2);
                v_tokens_2665_ = leanh::lean_ctor_get(v_c_2660_, 3);
                v_isSharedCheck_2683_ = (!leanh::lean_is_exclusive(v_c_2660_)) as u8;
                if v_isSharedCheck_2683_ == 0 {
                    v___x_2667_ = v_c_2660_;
                    v_isShared_2668_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tokens_2665_);
                    leanh::lean_inc(v_toCacheableParserContext_2664_);
                    leanh::lean_inc(v_toParserModuleContext_2663_);
                    leanh::lean_inc(v_toInputContext_2662_);
                    leanh::lean_dec(v_c_2660_);
                    v___x_2667_ = leanh::lean_box(0);
                    v_isShared_2668_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputString_2669_ = leanh::lean_ctor_get(v_toInputContext_2662_, 0);
                v_fileName_2670_ = leanh::lean_ctor_get(v_toInputContext_2662_, 1);
                v_fileMap_2671_ = leanh::lean_ctor_get(v_toInputContext_2662_, 2);
                v_isSharedCheck_2681_ =
                    (!leanh::lean_is_exclusive(v_toInputContext_2662_)) as u8;
                if v_isSharedCheck_2681_ == 0 {
                    v_unused_2682_ = leanh::lean_ctor_get(v_toInputContext_2662_, 3);
                    leanh::lean_dec(v_unused_2682_);
                    v___x_2673_ = v_toInputContext_2662_;
                    v_isShared_2674_ = v_isSharedCheck_2681_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fileMap_2671_);
                    leanh::lean_inc(v_fileName_2670_);
                    leanh::lean_inc(v_inputString_2669_);
                    leanh::lean_dec(v_toInputContext_2662_);
                    v___x_2673_ = leanh::lean_box(0);
                    v_isShared_2674_ = v_isSharedCheck_2681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2674_ == 0 {
                    leanh::lean_ctor_set(v___x_2673_, 3, v_endPos_2661_);
                    v___x_2676_ = v___x_2673_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2680_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_inputString_2669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_fileName_2670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_fileMap_2671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_endPos_2661_);
                    v___x_2676_ = v_reuseFailAlloc_2680_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2668_ == 0 {
                    leanh::lean_ctor_set(v___x_2667_, 0, v___x_2676_);
                    v___x_2678_ = v___x_2667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2679_,
                        1,
                        v_toParserModuleContext_2663_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2679_,
                        2,
                        v_toCacheableParserContext_2664_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_tokens_2665_);
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
    mut v_c_2684_: *mut leanh::LeanObject,
    mut v_endPos_2685_: *mut leanh::LeanObject,
    mut v_endPos__valid_2686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_2684_, v_endPos_2685_);
    return v___x_2687_;
}
pub unsafe fn l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(
    mut v_x_2694_: *mut leanh::LeanObject,
    mut v_x_2695_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2698_: u8 = 0;
    let mut v_head_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2694_) == 0 {
                    if leanh::lean_obj_tag(v_x_2695_) == 0 {
                        v___x_2696_ = 1;
                        return v___x_2696_;
                    } else {
                        v___x_2697_ = 0;
                        return v___x_2697_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_2695_) == 0 {
                        v___x_2698_ = 0;
                        return v___x_2698_;
                    } else {
                        v_head_2699_ = leanh::lean_ctor_get(v_x_2694_, 0);
                        v_tail_2700_ = leanh::lean_ctor_get(v_x_2694_, 1);
                        v_head_2701_ = leanh::lean_ctor_get(v_x_2695_, 0);
                        v_tail_2702_ = leanh::lean_ctor_get(v_x_2695_, 1);
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
    mut v_x_2705_: *mut leanh::LeanObject,
    mut v_x_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2707_: u8 = 0;
    let mut v_r_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_2705_, v_x_2706_);
    leanh::lean_dec(v_x_2706_);
    leanh::lean_dec(v_x_2705_);
    v_r_2708_ = leanh::lean_box((v_res_2707_) as usize);
    return v_r_2708_;
}
pub unsafe fn l_Lean_Parser_instBEqError_beq(
    mut v_x_2709_: *mut leanh::LeanObject,
    mut v_x_2710_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_unexpectedTk_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unexpected_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unexpectedTk_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unexpected_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    v_unexpectedTk_2711_ = leanh::lean_ctor_get(v_x_2709_, 0);
    leanh::lean_inc(v_unexpectedTk_2711_);
    v_unexpected_2712_ = leanh::lean_ctor_get(v_x_2709_, 1);
    leanh::lean_inc_ref(v_unexpected_2712_);
    v_expected_2713_ = leanh::lean_ctor_get(v_x_2709_, 2);
    leanh::lean_inc(v_expected_2713_);
    leanh::lean_dec_ref(v_x_2709_);
    v_unexpectedTk_2714_ = leanh::lean_ctor_get(v_x_2710_, 0);
    leanh::lean_inc(v_unexpectedTk_2714_);
    v_unexpected_2715_ = leanh::lean_ctor_get(v_x_2710_, 1);
    leanh::lean_inc_ref(v_unexpected_2715_);
    v_expected_2716_ = leanh::lean_ctor_get(v_x_2710_, 2);
    leanh::lean_inc(v_expected_2716_);
    leanh::lean_dec_ref(v_x_2710_);
    v___x_2717_ = l_Lean_Syntax_structEq(v_unexpectedTk_2711_, v_unexpectedTk_2714_);
    if v___x_2717_ == 0 {
        leanh::lean_dec(v_expected_2716_);
        leanh::lean_dec_ref(v_unexpected_2715_);
        leanh::lean_dec(v_expected_2713_);
        leanh::lean_dec_ref(v_unexpected_2712_);
        return v___x_2717_;
    } else {
        let mut v___x_2718_: u8 = 0;
        v___x_2718_ = lean_string_dec_eq(v_unexpected_2712_, v_unexpected_2715_);
        leanh::lean_dec_ref(v_unexpected_2715_);
        leanh::lean_dec_ref(v_unexpected_2712_);
        if v___x_2718_ == 0 {
            leanh::lean_dec(v_expected_2716_);
            leanh::lean_dec(v_expected_2713_);
            return v___x_2718_;
        } else {
            let mut v___x_2719_: u8 = 0;
            v___x_2719_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(
                v_expected_2713_,
                v_expected_2716_,
            );
            leanh::lean_dec(v_expected_2716_);
            leanh::lean_dec(v_expected_2713_);
            return v___x_2719_;
        }
    }
}
pub unsafe fn l_Lean_Parser_instBEqError_beq___boxed(
    mut v_x_2720_: *mut leanh::LeanObject,
    mut v_x_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2722_: u8 = 0;
    let mut v_r_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ = l_Lean_Parser_instBEqError_beq(v_x_2720_, v_x_2721_);
    v_r_2723_ = leanh::lean_box((v_res_2722_) as usize);
    return v_r_2723_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(
    mut v_x_2728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2728_) == 0 {
        let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2729_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
        return v___x_2729_;
    } else {
        let mut v_tail_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2730_ = leanh::lean_ctor_get(v_x_2728_, 1);
        if leanh::lean_obj_tag(v_tail_2730_) == 0 {
            let mut v_head_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_2731_ = leanh::lean_ctor_get(v_x_2728_, 0);
            leanh::lean_inc(v_head_2731_);
            leanh::lean_dec_ref_known(v_x_2728_, 2);
            return v_head_2731_;
        } else {
            let mut v_tail_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_2730_);
            v_tail_2732_ = leanh::lean_ctor_get(v_tail_2730_, 1);
            if leanh::lean_obj_tag(v_tail_2732_) == 0 {
                let mut v_head_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_head_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_head_2733_ = leanh::lean_ctor_get(v_x_2728_, 0);
                leanh::lean_inc(v_head_2733_);
                leanh::lean_dec_ref_known(v_x_2728_, 2);
                v_head_2734_ = leanh::lean_ctor_get(v_tail_2730_, 0);
                leanh::lean_inc(v_head_2734_);
                leanh::lean_dec_ref_known(v_tail_2730_, 2);
                v___x_2735_ =
                    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0;
                v___x_2736_ = lean_string_append(v_head_2733_, v___x_2735_);
                v___x_2737_ = lean_string_append(v___x_2736_, v_head_2734_);
                leanh::lean_dec(v_head_2734_);
                return v___x_2737_;
            } else {
                let mut v_head_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_head_2738_ = leanh::lean_ctor_get(v_x_2728_, 0);
                leanh::lean_inc(v_head_2738_);
                leanh::lean_dec_ref_known(v_x_2728_, 2);
                v___x_2739_ =
                    l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1;
                v___x_2740_ = lean_string_append(v_head_2738_, v___x_2739_);
                v___x_2741_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(
                    v_tail_2730_,
                );
                v___x_2742_ = lean_string_append(v___x_2740_, v___x_2741_);
                leanh::lean_dec_ref(v___x_2741_);
                return v___x_2742_;
            }
        }
    }
}
pub unsafe fn l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(
    mut v_as_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2745_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0;
    v___x_2746_ = l_List_eraseRepsBy___redArg(v___f_2745_, v_as_2744_);
    return v___x_2746_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(
    mut v_hi_2747_: *mut leanh::LeanObject,
    mut v_pivot_2748_: *mut leanh::LeanObject,
    mut v_as_2749_: *mut leanh::LeanObject,
    mut v_i_2750_: *mut leanh::LeanObject,
    mut v_k_2751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2752_ = lean_nat_dec_lt(v_k_2751_, v_hi_2747_);
                if v___x_2752_ == 0 {
                    leanh::lean_dec(v_k_2751_);
                    v___x_2753_ = lean_array_fswap(v_as_2749_, v_i_2750_, v_hi_2747_);
                    v___x_2754_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2754_, 0, v_i_2750_);
                    leanh::lean_ctor_set(v___x_2754_, 1, v___x_2753_);
                    return v___x_2754_;
                } else {
                    v___x_2755_ = lean_array_fget_borrowed(v_as_2749_, v_k_2751_);
                    v___x_2756_ = lean_string_dec_lt(v___x_2755_, v_pivot_2748_);
                    if v___x_2756_ == 0 {
                        v___x_2757_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2758_ = lean_nat_add(v_k_2751_, v___x_2757_);
                        leanh::lean_dec(v_k_2751_);
                        v_k_2751_ = v___x_2758_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2760_ = lean_array_fswap(v_as_2749_, v_i_2750_, v_k_2751_);
                        v___x_2761_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2762_ = lean_nat_add(v_i_2750_, v___x_2761_);
                        leanh::lean_dec(v_i_2750_);
                        v___x_2763_ = lean_nat_add(v_k_2751_, v___x_2761_);
                        leanh::lean_dec(v_k_2751_);
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
    mut v_hi_2765_: *mut leanh::LeanObject,
    mut v_pivot_2766_: *mut leanh::LeanObject,
    mut v_as_2767_: *mut leanh::LeanObject,
    mut v_i_2768_: *mut leanh::LeanObject,
    mut v_k_2769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_2765_, v_pivot_2766_, v_as_2767_, v_i_2768_, v_k_2769_);
    leanh::lean_dec_ref(v_pivot_2766_);
    leanh::lean_dec(v_hi_2765_);
    return v_res_2770_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(
    mut v_n_2771_: *mut leanh::LeanObject,
    mut v_as_2772_: *mut leanh::LeanObject,
    mut v_lo_2773_: *mut leanh::LeanObject,
    mut v_hi_2774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: u8 = 0;
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: u8 = 0;
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2786_ = lean_nat_dec_lt(v_lo_2773_, v_hi_2774_);
                if v___x_2786_ == 0 {
                    leanh::lean_dec(v_lo_2773_);
                    return v_as_2772_;
                } else {
                    v___x_2787_ = lean_nat_add(v_lo_2773_, v_hi_2774_);
                    v___x_2788_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2789_ = lean_nat_shiftr(v___x_2787_, v___x_2788_);
                    leanh::lean_dec(v___x_2787_);
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
                leanh::lean_inc_n(v_lo_2773_, 2);
                v___x_2778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_2774_, v_pivot_2777_, v___y_2776_, v_lo_2773_, v_lo_2773_);
                leanh::lean_dec(v_pivot_2777_);
                v_fst_2779_ = leanh::lean_ctor_get(v___x_2778_, 0);
                leanh::lean_inc(v_fst_2779_);
                v_snd_2780_ = leanh::lean_ctor_get(v___x_2778_, 1);
                leanh::lean_inc(v_snd_2780_);
                leanh::lean_dec_ref(v___x_2778_);
                v___x_2781_ = lean_nat_dec_le(v_hi_2774_, v_fst_2779_);
                if v___x_2781_ == 0 {
                    v___x_2782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_2771_, v_snd_2780_, v_lo_2773_, v_fst_2779_);
                    v___x_2783_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2784_ = lean_nat_add(v_fst_2779_, v___x_2783_);
                    leanh::lean_dec(v_fst_2779_);
                    v_as_2772_ = v___x_2782_;
                    v_lo_2773_ = v___x_2784_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2779_);
                    leanh::lean_dec(v_lo_2773_);
                    return v_snd_2780_;
                }
            }
            2 => {
                v___x_2792_ = lean_array_fget_borrowed(v___y_2791_, v_mid_2789_);
                v___x_2793_ = lean_array_fget_borrowed(v___y_2791_, v_hi_2774_);
                v___x_2794_ = lean_string_dec_lt(v___x_2792_, v___x_2793_);
                if v___x_2794_ == 0 {
                    leanh::lean_dec(v_mid_2789_);
                    v___y_2776_ = v___y_2791_;
                    state = 1;
                    continue;
                } else {
                    v___x_2795_ = lean_array_fswap(v___y_2791_, v_mid_2789_, v_hi_2774_);
                    leanh::lean_dec(v_mid_2789_);
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
    mut v_n_2806_: *mut leanh::LeanObject,
    mut v_as_2807_: *mut leanh::LeanObject,
    mut v_lo_2808_: *mut leanh::LeanObject,
    mut v_hi_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_2806_, v_as_2807_, v_lo_2808_, v_hi_2809_);
    leanh::lean_dec(v_hi_2809_);
    leanh::lean_dec(v_n_2806_);
    return v_res_2810_;
}
pub unsafe fn l_Lean_Parser_Error_toString(
    mut v_e_2813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: u8 = 0;
    let mut v_unexpected_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_unexpected_2846_ = leanh::lean_ctor_get(v_e_2813_, 1);
                leanh::lean_inc_ref(v_unexpected_2846_);
                v_expected_2847_ = leanh::lean_ctor_get(v_e_2813_, 2);
                leanh::lean_inc(v_expected_2847_);
                leanh::lean_dec_ref(v_e_2813_);
                v___x_2859_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_2860_ = lean_string_dec_eq(v_unexpected_2846_, v___x_2859_);
                if v___x_2860_ == 0 {
                    v___x_2861_ = leanh::lean_box(0);
                    v___x_2862_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2862_, 0, v_unexpected_2846_);
                    leanh::lean_ctor_set(v___x_2862_, 1, v___x_2861_);
                    v___y_2849_ = v___x_2862_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_unexpected_2846_);
                    v___x_2863_ = leanh::lean_box(0);
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
                leanh::lean_dec_ref(v___x_2827_);
                v___x_2829_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2829_, 0, v___x_2828_);
                leanh::lean_ctor_set(v___x_2829_, 1, v___y_2821_);
                v___y_2815_ = v___y_2822_;
                v___y_2816_ = v___x_2829_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2837_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_2835_, v___y_2831_, v___y_2834_, v___y_2836_);
                leanh::lean_dec(v___y_2836_);
                leanh::lean_dec(v___y_2835_);
                v___y_2821_ = v___y_2832_;
                v___y_2822_ = v___y_2833_;
                v___y_2823_ = v___x_2837_;
                state = 2;
                continue;
            }
            4 => {
                v___x_2845_ = lean_nat_dec_le(v___y_2844_, v___y_2839_);
                if v___x_2845_ == 0 {
                    leanh::lean_dec(v___y_2839_);
                    leanh::lean_inc(v___y_2844_);
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
                v___x_2850_ = leanh::lean_box(0);
                v___x_2851_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(
                    v_expected_2847_,
                    v___x_2850_,
                );
                if v___x_2851_ == 0 {
                    v___x_2852_ = lean_array_mk(v_expected_2847_);
                    v___x_2853_ = lean_array_get_size(v___x_2852_);
                    v___x_2854_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2855_ = lean_nat_dec_eq(v___x_2853_, v___x_2854_);
                    if v___x_2855_ == 0 {
                        v___x_2856_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2857_ = lean_nat_sub(v___x_2853_, v___x_2856_);
                        v___x_2858_ = lean_nat_dec_le(v___x_2854_, v___x_2857_);
                        if v___x_2858_ == 0 {
                            leanh::lean_inc(v___x_2857_);
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
                    leanh::lean_dec(v_expected_2847_);
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
    mut v_n_2864_: *mut leanh::LeanObject,
    mut v_as_2865_: *mut leanh::LeanObject,
    mut v_lo_2866_: *mut leanh::LeanObject,
    mut v_hi_2867_: *mut leanh::LeanObject,
    mut v_w_2868_: *mut leanh::LeanObject,
    mut v_hlo_2869_: *mut leanh::LeanObject,
    mut v_hhi_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_2864_, v_as_2865_, v_lo_2866_, v_hi_2867_);
    return v___x_2871_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(
    mut v_n_2872_: *mut leanh::LeanObject,
    mut v_as_2873_: *mut leanh::LeanObject,
    mut v_lo_2874_: *mut leanh::LeanObject,
    mut v_hi_2875_: *mut leanh::LeanObject,
    mut v_w_2876_: *mut leanh::LeanObject,
    mut v_hlo_2877_: *mut leanh::LeanObject,
    mut v_hhi_2878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_2872_, v_as_2873_, v_lo_2874_, v_hi_2875_, v_w_2876_, v_hlo_2877_, v_hhi_2878_);
    leanh::lean_dec(v_hi_2875_);
    leanh::lean_dec(v_n_2872_);
    return v_res_2879_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(
    mut v_n_2880_: *mut leanh::LeanObject,
    mut v_lo_2881_: *mut leanh::LeanObject,
    mut v_hi_2882_: *mut leanh::LeanObject,
    mut v_hhi_2883_: *mut leanh::LeanObject,
    mut v_pivot_2884_: *mut leanh::LeanObject,
    mut v_as_2885_: *mut leanh::LeanObject,
    mut v_i_2886_: *mut leanh::LeanObject,
    mut v_k_2887_: *mut leanh::LeanObject,
    mut v_ilo_2888_: *mut leanh::LeanObject,
    mut v_ik_2889_: *mut leanh::LeanObject,
    mut v_w_2890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_2882_, v_pivot_2884_, v_as_2885_, v_i_2886_, v_k_2887_);
    return v___x_2891_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(
    mut v_n_2892_: *mut leanh::LeanObject,
    mut v_lo_2893_: *mut leanh::LeanObject,
    mut v_hi_2894_: *mut leanh::LeanObject,
    mut v_hhi_2895_: *mut leanh::LeanObject,
    mut v_pivot_2896_: *mut leanh::LeanObject,
    mut v_as_2897_: *mut leanh::LeanObject,
    mut v_i_2898_: *mut leanh::LeanObject,
    mut v_k_2899_: *mut leanh::LeanObject,
    mut v_ilo_2900_: *mut leanh::LeanObject,
    mut v_ik_2901_: *mut leanh::LeanObject,
    mut v_w_2902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2903_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_2892_, v_lo_2893_, v_hi_2894_, v_hhi_2895_, v_pivot_2896_, v_as_2897_, v_i_2898_, v_k_2899_, v_ilo_2900_, v_ik_2901_, v_w_2902_);
    leanh::lean_dec_ref(v_pivot_2896_);
    leanh::lean_dec(v_hi_2894_);
    leanh::lean_dec(v_lo_2893_);
    leanh::lean_dec(v_n_2892_);
    return v_res_2903_;
}
pub unsafe fn l_Lean_Parser_Error_merge(
    mut v_e_u2081_2906_: *mut leanh::LeanObject,
    mut v_e_u2082_2907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unexpectedTk_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unexpected_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v_unused_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v_unexpected_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_unexpectedTk_2908_ = leanh::lean_ctor_get(v_e_u2082_2907_, 0);
                leanh::lean_inc(v_unexpectedTk_2908_);
                v_unexpected_2909_ = leanh::lean_ctor_get(v_e_u2082_2907_, 1);
                leanh::lean_inc_ref(v_unexpected_2909_);
                v_expected_2910_ = leanh::lean_ctor_get(v_e_u2082_2907_, 2);
                leanh::lean_inc(v_expected_2910_);
                leanh::lean_dec_ref(v_e_u2082_2907_);
                v___x_2924_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_2925_ = lean_string_dec_eq(v_unexpected_2909_, v___x_2924_);
                if v___x_2925_ == 0 {
                    v___y_2912_ = v_unexpected_2909_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_unexpected_2909_);
                    v_unexpected_2926_ = leanh::lean_ctor_get(v_e_u2081_2906_, 1);
                    leanh::lean_inc_ref(v_unexpected_2926_);
                    v___y_2912_ = v_unexpected_2926_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_expected_2913_ = leanh::lean_ctor_get(v_e_u2081_2906_, 2);
                v_isSharedCheck_2921_ = (!leanh::lean_is_exclusive(v_e_u2081_2906_)) as u8;
                if v_isSharedCheck_2921_ == 0 {
                    v_unused_2922_ = leanh::lean_ctor_get(v_e_u2081_2906_, 1);
                    leanh::lean_dec(v_unused_2922_);
                    v_unused_2923_ = leanh::lean_ctor_get(v_e_u2081_2906_, 0);
                    leanh::lean_dec(v_unused_2923_);
                    v___x_2915_ = v_e_u2081_2906_;
                    v_isShared_2916_ = v_isSharedCheck_2921_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_expected_2913_);
                    leanh::lean_dec(v_e_u2081_2906_);
                    v___x_2915_ = leanh::lean_box(0);
                    v_isShared_2916_ = v_isSharedCheck_2921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2917_ = l_List_appendTR___redArg(v_expected_2913_, v_expected_2910_);
                if v_isShared_2916_ == 0 {
                    leanh::lean_ctor_set(v___x_2915_, 2, v___x_2917_);
                    leanh::lean_ctor_set(v___x_2915_, 1, v___y_2912_);
                    leanh::lean_ctor_set(v___x_2915_, 0, v_unexpectedTk_2908_);
                    v___x_2919_ = v___x_2915_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_unexpectedTk_2908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___y_2912_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 2, v___x_2917_);
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
    mut v_x_2927_: *mut leanh::LeanObject,
    mut v_x_2928_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toCacheableParserContext_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserName_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserName_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: u8 = 0;
    v_toCacheableParserContext_2929_ = leanh::lean_ctor_get(v_x_2927_, 0);
    v_parserName_2930_ = leanh::lean_ctor_get(v_x_2927_, 1);
    v_pos_2931_ = leanh::lean_ctor_get(v_x_2927_, 2);
    v_toCacheableParserContext_2932_ = leanh::lean_ctor_get(v_x_2928_, 0);
    v_parserName_2933_ = leanh::lean_ctor_get(v_x_2928_, 1);
    v_pos_2934_ = leanh::lean_ctor_get(v_x_2928_, 2);
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
    mut v_x_2938_: *mut leanh::LeanObject,
    mut v_x_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2940_: u8 = 0;
    let mut v_r_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_2938_, v_x_2939_);
    leanh::lean_dec_ref(v_x_2939_);
    leanh::lean_dec_ref(v_x_2938_);
    v_r_2941_ = leanh::lean_box((v_res_2940_) as usize);
    return v_r_2941_;
}
pub unsafe fn l_Lean_Parser_instHashableParserCacheKey___lam__0(
    mut v_k_2944_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_parserName_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: u64 = 0;
    v_parserName_2945_ = leanh::lean_ctor_get(v_k_2944_, 1);
    v_pos_2946_ = leanh::lean_ctor_get(v_k_2944_, 2);
    v___x_2947_ = l_String_instHashableRaw_hash(v_pos_2946_);
    if leanh::lean_obj_tag(v_parserName_2945_) == 0 {
        let mut v___x_2948_: u64 = 0;
        let mut v___x_2949_: u64 = 0;
        v___x_2948_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
        v___x_2949_ = lean_uint64_mix_hash(v___x_2947_, v___x_2948_);
        return v___x_2949_;
    } else {
        let mut v_hash_2950_: u64 = 0;
        let mut v___x_2951_: u64 = 0;
        v_hash_2950_ = leanh::lean_ctor_get_uint64(
            v_parserName_2945_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        );
        v___x_2951_ = lean_uint64_mix_hash(v___x_2947_, v_hash_2950_);
        return v___x_2951_;
    }
}
pub unsafe fn l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(
    mut v_k_2952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2953_: u64 = 0;
    let mut v_r_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_2952_);
    leanh::lean_dec_ref(v_k_2952_);
    v_r_2954_ = leanh::lean_box_uint64(v_res_2953_);
    return v_r_2954_;
}
pub unsafe fn _init_l_Lean_Parser_initCacheForInput___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2957_: u32 = 0;
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2957_ = 32;
    v___x_2958_ = l_Char_utf8Size(v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn _init_l_Lean_Parser_initCacheForInput___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = leanh::lean_box(0);
    v___x_2960_ = leanh::lean_unsigned_to_nat(16);
    v___x_2961_ = lean_mk_array(v___x_2960_, v___x_2959_);
    return v___x_2961_;
}
pub unsafe fn _init_l_Lean_Parser_initCacheForInput___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2962_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__1_once),
        _init_l_Lean_Parser_initCacheForInput___closed__1,
    );
    v___x_2963_ = leanh::lean_unsigned_to_nat(0);
    v___x_2964_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2964_, 0, v___x_2963_);
    leanh::lean_ctor_set(v___x_2964_, 1, v___x_2962_);
    return v___x_2964_;
}
pub unsafe fn l_Lean_Parser_initCacheForInput(
    mut v_input_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2966_ = lean_string_utf8_byte_size(v_input_2965_);
    v___x_2967_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__0_once),
        _init_l_Lean_Parser_initCacheForInput___closed__0,
    );
    v___x_2968_ = lean_nat_add(v___x_2966_, v___x_2967_);
    v___x_2969_ = leanh::lean_unsigned_to_nat(0);
    v___x_2970_ = leanh::lean_box(0);
    v___x_2971_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2971_, 0, v___x_2968_);
    leanh::lean_ctor_set(v___x_2971_, 1, v___x_2969_);
    leanh::lean_ctor_set(v___x_2971_, 2, v___x_2970_);
    v___x_2972_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2_once),
        _init_l_Lean_Parser_initCacheForInput___closed__2,
    );
    v___x_2973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2973_, 0, v___x_2971_);
    leanh::lean_ctor_set(v___x_2973_, 1, v___x_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Lean_Parser_initCacheForInput___boxed(
    mut v_input_2974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2975_ = l_Lean_Parser_initCacheForInput(v_input_2974_);
    leanh::lean_dec_ref(v_input_2974_);
    return v_res_2975_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_toSubarray(
    mut v_stack_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_raw_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_raw_2977_ = leanh::lean_ctor_get(v_stack_2976_, 0);
    leanh::lean_inc_ref(v_raw_2977_);
    v_drop_2978_ = leanh::lean_ctor_get(v_stack_2976_, 1);
    leanh::lean_inc(v_drop_2978_);
    leanh::lean_dec_ref(v_stack_2976_);
    v___x_2979_ = lean_array_get_size(v_raw_2977_);
    v___x_2980_ = l_Array_toSubarray___redArg(v_raw_2977_, v_drop_2978_, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_size(
    mut v_stack_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_raw_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_raw_2988_ = leanh::lean_ctor_get(v_stack_2987_, 0);
    v_drop_2989_ = leanh::lean_ctor_get(v_stack_2987_, 1);
    v___x_2990_ = lean_array_get_size(v_raw_2988_);
    v___x_2991_ = lean_nat_sub(v___x_2990_, v_drop_2989_);
    return v___x_2991_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_size___boxed(
    mut v_stack_2992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Lean_Parser_SyntaxStack_size(v_stack_2992_);
    leanh::lean_dec_ref(v_stack_2992_);
    return v_res_2993_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_isEmpty(
    mut v_stack_2994_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    v___x_2995_ = l_Lean_Parser_SyntaxStack_size(v_stack_2994_);
    v___x_2996_ = leanh::lean_unsigned_to_nat(0);
    v___x_2997_ = lean_nat_dec_eq(v___x_2995_, v___x_2996_);
    leanh::lean_dec(v___x_2995_);
    return v___x_2997_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_isEmpty___boxed(
    mut v_stack_2998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2999_: u8 = 0;
    let mut v_r_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_2998_);
    leanh::lean_dec_ref(v_stack_2998_);
    v_r_3000_ = leanh::lean_box((v_res_2999_) as usize);
    return v_r_3000_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_shrink(
    mut v_stack_3001_: *mut leanh::LeanObject,
    mut v_n_3002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_raw_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3007_: u8 = 0;
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3003_ = leanh::lean_ctor_get(v_stack_3001_, 0);
                v_drop_3004_ = leanh::lean_ctor_get(v_stack_3001_, 1);
                v_isSharedCheck_3013_ = (!leanh::lean_is_exclusive(v_stack_3001_)) as u8;
                if v_isSharedCheck_3013_ == 0 {
                    v___x_3006_ = v_stack_3001_;
                    v_isShared_3007_ = v_isSharedCheck_3013_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_drop_3004_);
                    leanh::lean_inc(v_raw_3003_);
                    leanh::lean_dec(v_stack_3001_);
                    v___x_3006_ = leanh::lean_box(0);
                    v_isShared_3007_ = v_isSharedCheck_3013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3008_ = lean_nat_add(v_drop_3004_, v_n_3002_);
                v___x_3009_ = l_Array_shrink___redArg(v_raw_3003_, v___x_3008_);
                leanh::lean_dec(v___x_3008_);
                if v_isShared_3007_ == 0 {
                    leanh::lean_ctor_set(v___x_3006_, 0, v___x_3009_);
                    v___x_3011_ = v___x_3006_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_drop_3004_);
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
    mut v_stack_3014_: *mut leanh::LeanObject,
    mut v_n_3015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_3014_, v_n_3015_);
    leanh::lean_dec(v_n_3015_);
    return v_res_3016_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_push(
    mut v_stack_3017_: *mut leanh::LeanObject,
    mut v_a_3018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_raw_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3019_ = leanh::lean_ctor_get(v_stack_3017_, 0);
                v_drop_3020_ = leanh::lean_ctor_get(v_stack_3017_, 1);
                v_isSharedCheck_3028_ = (!leanh::lean_is_exclusive(v_stack_3017_)) as u8;
                if v_isSharedCheck_3028_ == 0 {
                    v___x_3022_ = v_stack_3017_;
                    v_isShared_3023_ = v_isSharedCheck_3028_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_drop_3020_);
                    leanh::lean_inc(v_raw_3019_);
                    leanh::lean_dec(v_stack_3017_);
                    v___x_3022_ = leanh::lean_box(0);
                    v_isShared_3023_ = v_isSharedCheck_3028_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3024_ = lean_array_push(v_raw_3019_, v_a_3018_);
                if v_isShared_3023_ == 0 {
                    leanh::lean_ctor_set(v___x_3022_, 0, v___x_3024_);
                    v___x_3026_ = v___x_3022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_drop_3020_);
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
pub unsafe fn l_Lean_Parser_SyntaxStack_pop(
    mut v_stack_3029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v_raw_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3030_ = leanh::lean_unsigned_to_nat(0);
                v___x_3031_ = l_Lean_Parser_SyntaxStack_size(v_stack_3029_);
                v___x_3032_ = lean_nat_dec_lt(v___x_3030_, v___x_3031_);
                leanh::lean_dec(v___x_3031_);
                if v___x_3032_ == 0 {
                    return v_stack_3029_;
                } else {
                    v_raw_3033_ = leanh::lean_ctor_get(v_stack_3029_, 0);
                    v_drop_3034_ = leanh::lean_ctor_get(v_stack_3029_, 1);
                    v_isSharedCheck_3042_ = (!leanh::lean_is_exclusive(v_stack_3029_)) as u8;
                    if v_isSharedCheck_3042_ == 0 {
                        v___x_3036_ = v_stack_3029_;
                        v_isShared_3037_ = v_isSharedCheck_3042_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_drop_3034_);
                        leanh::lean_inc(v_raw_3033_);
                        leanh::lean_dec(v_stack_3029_);
                        v___x_3036_ = leanh::lean_box(0);
                        v_isShared_3037_ = v_isSharedCheck_3042_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3038_ = lean_array_pop(v_raw_3033_);
                if v_isShared_3037_ == 0 {
                    leanh::lean_ctor_set(v___x_3036_, 0, v___x_3038_);
                    v___x_3040_ = v___x_3036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3041_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_drop_3034_);
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
    mut v_msg_3043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3044_ = leanh::lean_box(0);
    v___x_3045_ = lean_panic_fn_borrowed(v___x_3044_, v_msg_3043_);
    return v___x_3045_;
}
pub unsafe fn _init_l_Lean_Parser_SyntaxStack_back___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3049_ = l_Lean_Parser_SyntaxStack_back___closed__2;
    v___x_3050_ = leanh::lean_unsigned_to_nat(4);
    v___x_3051_ = leanh::lean_unsigned_to_nat(305);
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
    mut v_stack_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: u8 = 0;
    v___x_3056_ = leanh::lean_unsigned_to_nat(0);
    v___x_3057_ = l_Lean_Parser_SyntaxStack_size(v_stack_3055_);
    v___x_3058_ = lean_nat_dec_lt(v___x_3056_, v___x_3057_);
    leanh::lean_dec(v___x_3057_);
    if v___x_3058_ == 0 {
        let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3059_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_back___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_back___closed__3_once),
            _init_l_Lean_Parser_SyntaxStack_back___closed__3,
        );
        v___x_3060_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_3059_);
        return v___x_3060_;
    } else {
        let mut v_raw_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_raw_3061_ = leanh::lean_ctor_get(v_stack_3055_, 0);
        v___x_3062_ = leanh::lean_box(0);
        v___x_3063_ = lean_array_get_size(v_raw_3061_);
        v___x_3064_ = leanh::lean_unsigned_to_nat(1);
        v___x_3065_ = lean_nat_sub(v___x_3063_, v___x_3064_);
        v___x_3066_ = lean_array_get_borrowed(v___x_3062_, v_raw_3061_, v___x_3065_);
        leanh::lean_dec(v___x_3065_);
        leanh::lean_inc(v___x_3066_);
        return v___x_3066_;
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_back___boxed(
    mut v_stack_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Lean_Parser_SyntaxStack_back(v_stack_3067_);
    leanh::lean_dec_ref(v_stack_3067_);
    return v_res_3068_;
}
pub unsafe fn _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3071_ = l_Lean_Parser_SyntaxStack_get_x21___closed__1;
    v___x_3072_ = leanh::lean_unsigned_to_nat(4);
    v___x_3073_ = leanh::lean_unsigned_to_nat(311);
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
    mut v_stack_3077_: *mut leanh::LeanObject,
    mut v_i_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: u8 = 0;
    v___x_3079_ = l_Lean_Parser_SyntaxStack_size(v_stack_3077_);
    v___x_3080_ = lean_nat_dec_lt(v_i_3078_, v___x_3079_);
    leanh::lean_dec(v___x_3079_);
    if v___x_3080_ == 0 {
        let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3081_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_get_x21___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Parser_SyntaxStack_get_x21___closed__2_once),
            _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2,
        );
        v___x_3082_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_3081_);
        return v___x_3082_;
    } else {
        let mut v_raw_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_drop_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_raw_3083_ = leanh::lean_ctor_get(v_stack_3077_, 0);
        v_drop_3084_ = leanh::lean_ctor_get(v_stack_3077_, 1);
        v___x_3085_ = leanh::lean_box(0);
        v___x_3086_ = lean_nat_add(v_drop_3084_, v_i_3078_);
        v___x_3087_ = lean_array_get_borrowed(v___x_3085_, v_raw_3083_, v___x_3086_);
        leanh::lean_dec(v___x_3086_);
        leanh::lean_inc(v___x_3087_);
        return v___x_3087_;
    }
}
pub unsafe fn l_Lean_Parser_SyntaxStack_get_x21___boxed(
    mut v_stack_3088_: *mut leanh::LeanObject,
    mut v_i_3089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3090_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_3088_, v_i_3089_);
    leanh::lean_dec(v_i_3089_);
    leanh::lean_dec_ref(v_stack_3088_);
    return v_res_3090_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_extract(
    mut v_stack_3091_: *mut leanh::LeanObject,
    mut v_start_3092_: *mut leanh::LeanObject,
    mut v_stop_3093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_raw_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_raw_3094_ = leanh::lean_ctor_get(v_stack_3091_, 0);
    v_drop_3095_ = leanh::lean_ctor_get(v_stack_3091_, 1);
    v___x_3096_ = lean_nat_add(v_drop_3095_, v_start_3092_);
    v___x_3097_ = lean_nat_add(v_drop_3095_, v_stop_3093_);
    v___x_3098_ = l_Array_extract___redArg(v_raw_3094_, v___x_3096_, v___x_3097_);
    return v___x_3098_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_extract___boxed(
    mut v_stack_3099_: *mut leanh::LeanObject,
    mut v_start_3100_: *mut leanh::LeanObject,
    mut v_stop_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3102_ = l_Lean_Parser_SyntaxStack_extract(v_stack_3099_, v_start_3100_, v_stop_3101_);
    leanh::lean_dec(v_stop_3101_);
    leanh::lean_dec(v_start_3100_);
    leanh::lean_dec_ref(v_stack_3099_);
    return v_res_3102_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(
    mut v_stack_3103_: *mut leanh::LeanObject,
    mut v_stxs_3104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_raw_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3109_: u8 = 0;
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3105_ = leanh::lean_ctor_get(v_stack_3103_, 0);
                v_drop_3106_ = leanh::lean_ctor_get(v_stack_3103_, 1);
                v_isSharedCheck_3114_ = (!leanh::lean_is_exclusive(v_stack_3103_)) as u8;
                if v_isSharedCheck_3114_ == 0 {
                    v___x_3108_ = v_stack_3103_;
                    v_isShared_3109_ = v_isSharedCheck_3114_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_drop_3106_);
                    leanh::lean_inc(v_raw_3105_);
                    leanh::lean_dec(v_stack_3103_);
                    v___x_3108_ = leanh::lean_box(0);
                    v_isShared_3109_ = v_isSharedCheck_3114_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3110_ = l_Array_append___redArg(v_raw_3105_, v_stxs_3104_);
                if v_isShared_3109_ == 0 {
                    leanh::lean_ctor_set(v___x_3108_, 0, v___x_3110_);
                    v___x_3112_ = v___x_3108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_drop_3106_);
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
    mut v_stack_3115_: *mut leanh::LeanObject,
    mut v_stxs_3116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3117_ =
        l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_3115_, v_stxs_3116_);
    leanh::lean_dec_ref(v_stxs_3116_);
    return v_res_3117_;
}
pub unsafe fn l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(
    mut v_stack_3118_: *mut leanh::LeanObject,
    mut v_stxs_3119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_raw_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_raw_3120_ = leanh::lean_ctor_get(v_stack_3118_, 0);
                v_drop_3121_ = leanh::lean_ctor_get(v_stack_3118_, 1);
                v_isSharedCheck_3129_ = (!leanh::lean_is_exclusive(v_stack_3118_)) as u8;
                if v_isSharedCheck_3129_ == 0 {
                    v___x_3123_ = v_stack_3118_;
                    v_isShared_3124_ = v_isSharedCheck_3129_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_drop_3121_);
                    leanh::lean_inc(v_raw_3120_);
                    leanh::lean_dec(v_stack_3118_);
                    v___x_3123_ = leanh::lean_box(0);
                    v_isShared_3124_ = v_isSharedCheck_3129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3125_ = l_Array_append___redArg(v_raw_3120_, v_stxs_3119_);
                if v_isShared_3124_ == 0 {
                    leanh::lean_ctor_set(v___x_3123_, 0, v___x_3125_);
                    v___x_3127_ = v___x_3123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_drop_3121_);
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
    mut v_stack_3130_: *mut leanh::LeanObject,
    mut v_stxs_3131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3132_ =
        l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_3130_, v_stxs_3131_);
    leanh::lean_dec_ref(v_stxs_3131_);
    return v_res_3132_;
}
pub unsafe fn l_Lean_Parser_ParserState_hasError(
    mut v_s_3135_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_errorMsg_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    v_errorMsg_3136_ = leanh::lean_ctor_get(v_s_3135_, 4);
    leanh::lean_inc(v_errorMsg_3136_);
    leanh::lean_dec_ref(v_s_3135_);
    v___x_3137_ = l_Lean_Parser_instBEqError___closed__0;
    v___x_3138_ = leanh::lean_box(0);
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
    mut v_s_3142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3143_: u8 = 0;
    let mut v_r_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Lean_Parser_ParserState_hasError(v_s_3142_);
    v_r_3144_ = leanh::lean_box((v_res_3143_) as usize);
    return v_r_3144_;
}
pub unsafe fn l_Lean_Parser_ParserState_stackSize(
    mut v_s_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stxStack_3146_ = leanh::lean_ctor_get(v_s_3145_, 0);
    v___x_3147_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3146_);
    return v___x_3147_;
}
pub unsafe fn l_Lean_Parser_ParserState_stackSize___boxed(
    mut v_s_3148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3149_ = l_Lean_Parser_ParserState_stackSize(v_s_3148_);
    leanh::lean_dec_ref(v_s_3148_);
    return v_res_3149_;
}
pub unsafe fn l_Lean_Parser_ParserState_restore(
    mut v_s_3150_: *mut leanh::LeanObject,
    mut v_iniStackSz_3151_: *mut leanh::LeanObject,
    mut v_iniPos_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v_unused_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3153_ = leanh::lean_ctor_get(v_s_3150_, 0);
                v_lhsPrec_3154_ = leanh::lean_ctor_get(v_s_3150_, 1);
                v_cache_3155_ = leanh::lean_ctor_get(v_s_3150_, 3);
                v_recoveredErrors_3156_ = leanh::lean_ctor_get(v_s_3150_, 5);
                v_isSharedCheck_3165_ = (!leanh::lean_is_exclusive(v_s_3150_)) as u8;
                if v_isSharedCheck_3165_ == 0 {
                    v_unused_3166_ = leanh::lean_ctor_get(v_s_3150_, 4);
                    leanh::lean_dec(v_unused_3166_);
                    v_unused_3167_ = leanh::lean_ctor_get(v_s_3150_, 2);
                    leanh::lean_dec(v_unused_3167_);
                    v___x_3158_ = v_s_3150_;
                    v_isShared_3159_ = v_isSharedCheck_3165_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3156_);
                    leanh::lean_inc(v_cache_3155_);
                    leanh::lean_inc(v_lhsPrec_3154_);
                    leanh::lean_inc(v_stxStack_3153_);
                    leanh::lean_dec(v_s_3150_);
                    v___x_3158_ = leanh::lean_box(0);
                    v_isShared_3159_ = v_isSharedCheck_3165_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3160_ =
                    l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3153_, v_iniStackSz_3151_);
                v___x_3161_ = leanh::lean_box(0);
                if v_isShared_3159_ == 0 {
                    leanh::lean_ctor_set(v___x_3158_, 4, v___x_3161_);
                    leanh::lean_ctor_set(v___x_3158_, 2, v_iniPos_3152_);
                    leanh::lean_ctor_set(v___x_3158_, 0, v___x_3160_);
                    v___x_3163_ = v___x_3158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_lhsPrec_3154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_iniPos_3152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_cache_3155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 4, v___x_3161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 5, v_recoveredErrors_3156_);
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
    mut v_s_3168_: *mut leanh::LeanObject,
    mut v_iniStackSz_3169_: *mut leanh::LeanObject,
    mut v_iniPos_3170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3171_ = l_Lean_Parser_ParserState_restore(v_s_3168_, v_iniStackSz_3169_, v_iniPos_3170_);
    leanh::lean_dec(v_iniStackSz_3169_);
    return v_res_3171_;
}
pub unsafe fn l_Lean_Parser_ParserState_setPos(
    mut v_s_3172_: *mut leanh::LeanObject,
    mut v_pos_3173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_unused_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3174_ = leanh::lean_ctor_get(v_s_3172_, 0);
                v_lhsPrec_3175_ = leanh::lean_ctor_get(v_s_3172_, 1);
                v_cache_3176_ = leanh::lean_ctor_get(v_s_3172_, 3);
                v_errorMsg_3177_ = leanh::lean_ctor_get(v_s_3172_, 4);
                v_recoveredErrors_3178_ = leanh::lean_ctor_get(v_s_3172_, 5);
                v_isSharedCheck_3185_ = (!leanh::lean_is_exclusive(v_s_3172_)) as u8;
                if v_isSharedCheck_3185_ == 0 {
                    v_unused_3186_ = leanh::lean_ctor_get(v_s_3172_, 2);
                    leanh::lean_dec(v_unused_3186_);
                    v___x_3180_ = v_s_3172_;
                    v_isShared_3181_ = v_isSharedCheck_3185_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3178_);
                    leanh::lean_inc(v_errorMsg_3177_);
                    leanh::lean_inc(v_cache_3176_);
                    leanh::lean_inc(v_lhsPrec_3175_);
                    leanh::lean_inc(v_stxStack_3174_);
                    leanh::lean_dec(v_s_3172_);
                    v___x_3180_ = leanh::lean_box(0);
                    v_isShared_3181_ = v_isSharedCheck_3185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3181_ == 0 {
                    leanh::lean_ctor_set(v___x_3180_, 2, v_pos_3173_);
                    v___x_3183_ = v___x_3180_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_stxStack_3174_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_lhsPrec_3175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_pos_3173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_cache_3176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_errorMsg_3177_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 5, v_recoveredErrors_3178_);
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
    mut v_s_3187_: *mut leanh::LeanObject,
    mut v_cache_3188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_unused_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3189_ = leanh::lean_ctor_get(v_s_3187_, 0);
                v_lhsPrec_3190_ = leanh::lean_ctor_get(v_s_3187_, 1);
                v_pos_3191_ = leanh::lean_ctor_get(v_s_3187_, 2);
                v_errorMsg_3192_ = leanh::lean_ctor_get(v_s_3187_, 4);
                v_recoveredErrors_3193_ = leanh::lean_ctor_get(v_s_3187_, 5);
                v_isSharedCheck_3200_ = (!leanh::lean_is_exclusive(v_s_3187_)) as u8;
                if v_isSharedCheck_3200_ == 0 {
                    v_unused_3201_ = leanh::lean_ctor_get(v_s_3187_, 3);
                    leanh::lean_dec(v_unused_3201_);
                    v___x_3195_ = v_s_3187_;
                    v_isShared_3196_ = v_isSharedCheck_3200_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3193_);
                    leanh::lean_inc(v_errorMsg_3192_);
                    leanh::lean_inc(v_pos_3191_);
                    leanh::lean_inc(v_lhsPrec_3190_);
                    leanh::lean_inc(v_stxStack_3189_);
                    leanh::lean_dec(v_s_3187_);
                    v___x_3195_ = leanh::lean_box(0);
                    v_isShared_3196_ = v_isSharedCheck_3200_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3196_ == 0 {
                    leanh::lean_ctor_set(v___x_3195_, 3, v_cache_3188_);
                    v___x_3198_ = v___x_3195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_stxStack_3189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_lhsPrec_3190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_pos_3191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 3, v_cache_3188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_errorMsg_3192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 5, v_recoveredErrors_3193_);
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
    mut v_s_3202_: *mut leanh::LeanObject,
    mut v_n_3203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3204_ = leanh::lean_ctor_get(v_s_3202_, 0);
                v_lhsPrec_3205_ = leanh::lean_ctor_get(v_s_3202_, 1);
                v_pos_3206_ = leanh::lean_ctor_get(v_s_3202_, 2);
                v_cache_3207_ = leanh::lean_ctor_get(v_s_3202_, 3);
                v_errorMsg_3208_ = leanh::lean_ctor_get(v_s_3202_, 4);
                v_recoveredErrors_3209_ = leanh::lean_ctor_get(v_s_3202_, 5);
                v_isSharedCheck_3217_ = (!leanh::lean_is_exclusive(v_s_3202_)) as u8;
                if v_isSharedCheck_3217_ == 0 {
                    v___x_3211_ = v_s_3202_;
                    v_isShared_3212_ = v_isSharedCheck_3217_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3209_);
                    leanh::lean_inc(v_errorMsg_3208_);
                    leanh::lean_inc(v_cache_3207_);
                    leanh::lean_inc(v_pos_3206_);
                    leanh::lean_inc(v_lhsPrec_3205_);
                    leanh::lean_inc(v_stxStack_3204_);
                    leanh::lean_dec(v_s_3202_);
                    v___x_3211_ = leanh::lean_box(0);
                    v_isShared_3212_ = v_isSharedCheck_3217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3213_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_3204_, v_n_3203_);
                if v_isShared_3212_ == 0 {
                    leanh::lean_ctor_set(v___x_3211_, 0, v___x_3213_);
                    v___x_3215_ = v___x_3211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3216_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_lhsPrec_3205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_pos_3206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_cache_3207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 4, v_errorMsg_3208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 5, v_recoveredErrors_3209_);
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
    mut v_s_3218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3219_ = leanh::lean_ctor_get(v_s_3218_, 0);
                v_lhsPrec_3220_ = leanh::lean_ctor_get(v_s_3218_, 1);
                v_pos_3221_ = leanh::lean_ctor_get(v_s_3218_, 2);
                v_cache_3222_ = leanh::lean_ctor_get(v_s_3218_, 3);
                v_errorMsg_3223_ = leanh::lean_ctor_get(v_s_3218_, 4);
                v_recoveredErrors_3224_ = leanh::lean_ctor_get(v_s_3218_, 5);
                v_isSharedCheck_3232_ = (!leanh::lean_is_exclusive(v_s_3218_)) as u8;
                if v_isSharedCheck_3232_ == 0 {
                    v___x_3226_ = v_s_3218_;
                    v_isShared_3227_ = v_isSharedCheck_3232_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3224_);
                    leanh::lean_inc(v_errorMsg_3223_);
                    leanh::lean_inc(v_cache_3222_);
                    leanh::lean_inc(v_pos_3221_);
                    leanh::lean_inc(v_lhsPrec_3220_);
                    leanh::lean_inc(v_stxStack_3219_);
                    leanh::lean_dec(v_s_3218_);
                    v___x_3226_ = leanh::lean_box(0);
                    v_isShared_3227_ = v_isSharedCheck_3232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3228_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_3219_);
                if v_isShared_3227_ == 0 {
                    leanh::lean_ctor_set(v___x_3226_, 0, v___x_3228_);
                    v___x_3230_ = v___x_3226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_lhsPrec_3220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_pos_3221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_cache_3222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 4, v_errorMsg_3223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 5, v_recoveredErrors_3224_);
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
    mut v_s_3233_: *mut leanh::LeanObject,
    mut v_iniStackSz_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3235_ = leanh::lean_ctor_get(v_s_3233_, 0);
                v_lhsPrec_3236_ = leanh::lean_ctor_get(v_s_3233_, 1);
                v_pos_3237_ = leanh::lean_ctor_get(v_s_3233_, 2);
                v_cache_3238_ = leanh::lean_ctor_get(v_s_3233_, 3);
                v_errorMsg_3239_ = leanh::lean_ctor_get(v_s_3233_, 4);
                v_recoveredErrors_3240_ = leanh::lean_ctor_get(v_s_3233_, 5);
                v_isSharedCheck_3248_ = (!leanh::lean_is_exclusive(v_s_3233_)) as u8;
                if v_isSharedCheck_3248_ == 0 {
                    v___x_3242_ = v_s_3233_;
                    v_isShared_3243_ = v_isSharedCheck_3248_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3240_);
                    leanh::lean_inc(v_errorMsg_3239_);
                    leanh::lean_inc(v_cache_3238_);
                    leanh::lean_inc(v_pos_3237_);
                    leanh::lean_inc(v_lhsPrec_3236_);
                    leanh::lean_inc(v_stxStack_3235_);
                    leanh::lean_dec(v_s_3233_);
                    v___x_3242_ = leanh::lean_box(0);
                    v_isShared_3243_ = v_isSharedCheck_3248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3244_ =
                    l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3235_, v_iniStackSz_3234_);
                if v_isShared_3243_ == 0 {
                    leanh::lean_ctor_set(v___x_3242_, 0, v___x_3244_);
                    v___x_3246_ = v___x_3242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_lhsPrec_3236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_pos_3237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_cache_3238_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_errorMsg_3239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 5, v_recoveredErrors_3240_);
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
    mut v_s_3249_: *mut leanh::LeanObject,
    mut v_iniStackSz_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3251_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3249_, v_iniStackSz_3250_);
    leanh::lean_dec(v_iniStackSz_3250_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_Parser_ParserState_next(
    mut v_s_3252_: *mut leanh::LeanObject,
    mut v_c_3253_: *mut leanh::LeanObject,
    mut v_pos_3254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v_inputString_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut v_unused_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3255_ = leanh::lean_ctor_get(v_c_3253_, 0);
                v_stxStack_3256_ = leanh::lean_ctor_get(v_s_3252_, 0);
                v_lhsPrec_3257_ = leanh::lean_ctor_get(v_s_3252_, 1);
                v_cache_3258_ = leanh::lean_ctor_get(v_s_3252_, 3);
                v_errorMsg_3259_ = leanh::lean_ctor_get(v_s_3252_, 4);
                v_recoveredErrors_3260_ = leanh::lean_ctor_get(v_s_3252_, 5);
                v_isSharedCheck_3269_ = (!leanh::lean_is_exclusive(v_s_3252_)) as u8;
                if v_isSharedCheck_3269_ == 0 {
                    v_unused_3270_ = leanh::lean_ctor_get(v_s_3252_, 2);
                    leanh::lean_dec(v_unused_3270_);
                    v___x_3262_ = v_s_3252_;
                    v_isShared_3263_ = v_isSharedCheck_3269_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3260_);
                    leanh::lean_inc(v_errorMsg_3259_);
                    leanh::lean_inc(v_cache_3258_);
                    leanh::lean_inc(v_lhsPrec_3257_);
                    leanh::lean_inc(v_stxStack_3256_);
                    leanh::lean_dec(v_s_3252_);
                    v___x_3262_ = leanh::lean_box(0);
                    v_isShared_3263_ = v_isSharedCheck_3269_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputString_3264_ = leanh::lean_ctor_get(v_toInputContext_3255_, 0);
                v___x_3265_ = lean_string_utf8_next(v_inputString_3264_, v_pos_3254_);
                if v_isShared_3263_ == 0 {
                    leanh::lean_ctor_set(v___x_3262_, 2, v___x_3265_);
                    v___x_3267_ = v___x_3262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_stxStack_3256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_lhsPrec_3257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 2, v___x_3265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 3, v_cache_3258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 4, v_errorMsg_3259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 5, v_recoveredErrors_3260_);
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
    mut v_s_3271_: *mut leanh::LeanObject,
    mut v_c_3272_: *mut leanh::LeanObject,
    mut v_pos_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Lean_Parser_ParserState_next(v_s_3271_, v_c_3272_, v_pos_3273_);
    leanh::lean_dec(v_pos_3273_);
    leanh::lean_dec_ref(v_c_3272_);
    return v_res_3274_;
}
pub unsafe fn l_Lean_Parser_ParserState_next_x27___redArg(
    mut v_s_3275_: *mut leanh::LeanObject,
    mut v_c_3276_: *mut leanh::LeanObject,
    mut v_pos_3277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v_inputString_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_unused_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3278_ = leanh::lean_ctor_get(v_c_3276_, 0);
                v_stxStack_3279_ = leanh::lean_ctor_get(v_s_3275_, 0);
                v_lhsPrec_3280_ = leanh::lean_ctor_get(v_s_3275_, 1);
                v_cache_3281_ = leanh::lean_ctor_get(v_s_3275_, 3);
                v_errorMsg_3282_ = leanh::lean_ctor_get(v_s_3275_, 4);
                v_recoveredErrors_3283_ = leanh::lean_ctor_get(v_s_3275_, 5);
                v_isSharedCheck_3292_ = (!leanh::lean_is_exclusive(v_s_3275_)) as u8;
                if v_isSharedCheck_3292_ == 0 {
                    v_unused_3293_ = leanh::lean_ctor_get(v_s_3275_, 2);
                    leanh::lean_dec(v_unused_3293_);
                    v___x_3285_ = v_s_3275_;
                    v_isShared_3286_ = v_isSharedCheck_3292_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3283_);
                    leanh::lean_inc(v_errorMsg_3282_);
                    leanh::lean_inc(v_cache_3281_);
                    leanh::lean_inc(v_lhsPrec_3280_);
                    leanh::lean_inc(v_stxStack_3279_);
                    leanh::lean_dec(v_s_3275_);
                    v___x_3285_ = leanh::lean_box(0);
                    v_isShared_3286_ = v_isSharedCheck_3292_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputString_3287_ = leanh::lean_ctor_get(v_toInputContext_3278_, 0);
                v___x_3288_ = lean_string_utf8_next_fast(v_inputString_3287_, v_pos_3277_);
                if v_isShared_3286_ == 0 {
                    leanh::lean_ctor_set(v___x_3285_, 2, v___x_3288_);
                    v___x_3290_ = v___x_3285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_stxStack_3279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_lhsPrec_3280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 2, v___x_3288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 3, v_cache_3281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 4, v_errorMsg_3282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 5, v_recoveredErrors_3283_);
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
    mut v_s_3294_: *mut leanh::LeanObject,
    mut v_c_3295_: *mut leanh::LeanObject,
    mut v_pos_3296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3297_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3294_, v_c_3295_, v_pos_3296_);
    leanh::lean_dec(v_pos_3296_);
    leanh::lean_dec_ref(v_c_3295_);
    return v_res_3297_;
}
pub unsafe fn l_Lean_Parser_ParserState_next_x27(
    mut v_s_3298_: *mut leanh::LeanObject,
    mut v_c_3299_: *mut leanh::LeanObject,
    mut v_pos_3300_: *mut leanh::LeanObject,
    mut v_h_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3302_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3298_, v_c_3299_, v_pos_3300_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_Parser_ParserState_next_x27___boxed(
    mut v_s_3303_: *mut leanh::LeanObject,
    mut v_c_3304_: *mut leanh::LeanObject,
    mut v_pos_3305_: *mut leanh::LeanObject,
    mut v_h_3306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Parser_ParserState_next_x27(v_s_3303_, v_c_3304_, v_pos_3305_, v_h_3306_);
    leanh::lean_dec(v_pos_3305_);
    leanh::lean_dec_ref(v_c_3304_);
    return v_res_3307_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(
    mut v_x_3308_: *mut leanh::LeanObject,
    mut v_x_3309_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3308_) == 0 {
        if leanh::lean_obj_tag(v_x_3309_) == 0 {
            let mut v___x_3310_: u8 = 0;
            v___x_3310_ = 1;
            return v___x_3310_;
        } else {
            let mut v___x_3311_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_3309_, 1);
            v___x_3311_ = 0;
            return v___x_3311_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_3309_) == 0 {
            let mut v___x_3312_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_3308_, 1);
            v___x_3312_ = 0;
            return v___x_3312_;
        } else {
            let mut v_val_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3315_: u8 = 0;
            v_val_3313_ = leanh::lean_ctor_get(v_x_3308_, 0);
            leanh::lean_inc(v_val_3313_);
            leanh::lean_dec_ref_known(v_x_3308_, 1);
            v_val_3314_ = leanh::lean_ctor_get(v_x_3309_, 0);
            leanh::lean_inc(v_val_3314_);
            leanh::lean_dec_ref_known(v_x_3309_, 1);
            v___x_3315_ = l_Lean_Parser_instBEqError_beq(v_val_3313_, v_val_3314_);
            return v___x_3315_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(
    mut v_x_3316_: *mut leanh::LeanObject,
    mut v_x_3317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3318_: u8 = 0;
    let mut v_r_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3318_ =
        l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_3316_, v_x_3317_);
    v_r_3319_ = leanh::lean_box((v_res_3318_) as usize);
    return v_r_3319_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkNode(
    mut v_s_3320_: *mut leanh::LeanObject,
    mut v_k_3321_: *mut leanh::LeanObject,
    mut v_iniStackSz_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stack_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stack_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: u8 = 0;
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stack_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3323_ = leanh::lean_ctor_get(v_s_3320_, 0);
                v_lhsPrec_3324_ = leanh::lean_ctor_get(v_s_3320_, 1);
                v_pos_3325_ = leanh::lean_ctor_get(v_s_3320_, 2);
                v_cache_3326_ = leanh::lean_ctor_get(v_s_3320_, 3);
                v_errorMsg_3327_ = leanh::lean_ctor_get(v_s_3320_, 4);
                v_recoveredErrors_3328_ = leanh::lean_ctor_get(v_s_3320_, 5);
                v_isSharedCheck_3349_ = (!leanh::lean_is_exclusive(v_s_3320_)) as u8;
                if v_isSharedCheck_3349_ == 0 {
                    v___x_3330_ = v_s_3320_;
                    v_isShared_3331_ = v_isSharedCheck_3349_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3328_);
                    leanh::lean_inc(v_errorMsg_3327_);
                    leanh::lean_inc(v_cache_3326_);
                    leanh::lean_inc(v_pos_3325_);
                    leanh::lean_inc(v_lhsPrec_3324_);
                    leanh::lean_inc(v_stxStack_3323_);
                    leanh::lean_dec(v_s_3320_);
                    v___x_3330_ = leanh::lean_box(0);
                    v_isShared_3331_ = v_isSharedCheck_3349_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3342_ = leanh::lean_box(0);
                leanh::lean_inc(v_errorMsg_3327_);
                v___x_3343_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(
                    v_errorMsg_3327_,
                    v___x_3342_,
                );
                if v___x_3343_ == 0 {
                    v___x_3344_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3323_);
                    v___x_3345_ = lean_nat_dec_eq(v___x_3344_, v_iniStackSz_3322_);
                    leanh::lean_dec(v___x_3344_);
                    if v___x_3345_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3330_);
                        leanh::lean_dec(v_k_3321_);
                        v___x_3346_ = leanh::lean_box(0);
                        v_stack_3347_ =
                            l_Lean_Parser_SyntaxStack_push(v_stxStack_3323_, v___x_3346_);
                        v___x_3348_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        leanh::lean_ctor_set(v___x_3348_, 0, v_stack_3347_);
                        leanh::lean_ctor_set(v___x_3348_, 1, v_lhsPrec_3324_);
                        leanh::lean_ctor_set(v___x_3348_, 2, v_pos_3325_);
                        leanh::lean_ctor_set(v___x_3348_, 3, v_cache_3326_);
                        leanh::lean_ctor_set(v___x_3348_, 4, v_errorMsg_3327_);
                        leanh::lean_ctor_set(v___x_3348_, 5, v_recoveredErrors_3328_);
                        return v___x_3348_;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3333_ = leanh::lean_box(2);
                v___x_3334_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3323_);
                v___x_3335_ = l_Lean_Parser_SyntaxStack_extract(
                    v_stxStack_3323_,
                    v_iniStackSz_3322_,
                    v___x_3334_,
                );
                leanh::lean_dec(v___x_3334_);
                v_newNode_3336_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v_newNode_3336_, 0, v___x_3333_);
                leanh::lean_ctor_set(v_newNode_3336_, 1, v_k_3321_);
                leanh::lean_ctor_set(v_newNode_3336_, 2, v___x_3335_);
                v_stack_3337_ =
                    l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3323_, v_iniStackSz_3322_);
                v_stack_3338_ = l_Lean_Parser_SyntaxStack_push(v_stack_3337_, v_newNode_3336_);
                if v_isShared_3331_ == 0 {
                    leanh::lean_ctor_set(v___x_3330_, 0, v_stack_3338_);
                    v___x_3340_ = v___x_3330_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_stack_3338_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_lhsPrec_3324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_pos_3325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_cache_3326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 4, v_errorMsg_3327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 5, v_recoveredErrors_3328_);
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
    mut v_s_3350_: *mut leanh::LeanObject,
    mut v_k_3351_: *mut leanh::LeanObject,
    mut v_iniStackSz_3352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_Parser_ParserState_mkNode(v_s_3350_, v_k_3351_, v_iniStackSz_3352_);
    leanh::lean_dec(v_iniStackSz_3352_);
    return v_res_3353_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkTrailingNode(
    mut v_s_3354_: *mut leanh::LeanObject,
    mut v_k_3355_: *mut leanh::LeanObject,
    mut v_iniStackSz_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stack_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stack_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3357_ = leanh::lean_ctor_get(v_s_3354_, 0);
                v_lhsPrec_3358_ = leanh::lean_ctor_get(v_s_3354_, 1);
                v_pos_3359_ = leanh::lean_ctor_get(v_s_3354_, 2);
                v_cache_3360_ = leanh::lean_ctor_get(v_s_3354_, 3);
                v_errorMsg_3361_ = leanh::lean_ctor_get(v_s_3354_, 4);
                v_recoveredErrors_3362_ = leanh::lean_ctor_get(v_s_3354_, 5);
                v_isSharedCheck_3377_ = (!leanh::lean_is_exclusive(v_s_3354_)) as u8;
                if v_isSharedCheck_3377_ == 0 {
                    v___x_3364_ = v_s_3354_;
                    v_isShared_3365_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3362_);
                    leanh::lean_inc(v_errorMsg_3361_);
                    leanh::lean_inc(v_cache_3360_);
                    leanh::lean_inc(v_pos_3359_);
                    leanh::lean_inc(v_lhsPrec_3358_);
                    leanh::lean_inc(v_stxStack_3357_);
                    leanh::lean_dec(v_s_3354_);
                    v___x_3364_ = leanh::lean_box(0);
                    v_isShared_3365_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3366_ = leanh::lean_box(2);
                v___x_3367_ = leanh::lean_unsigned_to_nat(1);
                v___x_3368_ = lean_nat_sub(v_iniStackSz_3356_, v___x_3367_);
                v___x_3369_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_3357_);
                v___x_3370_ =
                    l_Lean_Parser_SyntaxStack_extract(v_stxStack_3357_, v___x_3368_, v___x_3369_);
                leanh::lean_dec(v___x_3369_);
                v_newNode_3371_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v_newNode_3371_, 0, v___x_3366_);
                leanh::lean_ctor_set(v_newNode_3371_, 1, v_k_3355_);
                leanh::lean_ctor_set(v_newNode_3371_, 2, v___x_3370_);
                v_stack_3372_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_3357_, v___x_3368_);
                leanh::lean_dec(v___x_3368_);
                v_stack_3373_ = l_Lean_Parser_SyntaxStack_push(v_stack_3372_, v_newNode_3371_);
                if v_isShared_3365_ == 0 {
                    leanh::lean_ctor_set(v___x_3364_, 0, v_stack_3373_);
                    v___x_3375_ = v___x_3364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3376_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_stack_3373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_lhsPrec_3358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_pos_3359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 3, v_cache_3360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 4, v_errorMsg_3361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 5, v_recoveredErrors_3362_);
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
    mut v_s_3378_: *mut leanh::LeanObject,
    mut v_k_3379_: *mut leanh::LeanObject,
    mut v_iniStackSz_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3381_ =
        l_Lean_Parser_ParserState_mkTrailingNode(v_s_3378_, v_k_3379_, v_iniStackSz_3380_);
    leanh::lean_dec(v_iniStackSz_3380_);
    return v_res_3381_;
}
pub unsafe fn l_Lean_Parser_ParserState_allErrors(
    mut v_s_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_errorMsg_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_errorMsg_3385_ = leanh::lean_ctor_get(v_s_3384_, 4);
    if leanh::lean_obj_tag(v_errorMsg_3385_) == 0 {
        let mut v_recoveredErrors_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_recoveredErrors_3386_ = leanh::lean_ctor_get(v_s_3384_, 5);
        leanh::lean_inc_ref(v_recoveredErrors_3386_);
        leanh::lean_dec_ref(v_s_3384_);
        v___x_3387_ = l_Lean_Parser_ParserState_allErrors___closed__0;
        v___x_3388_ = l_Array_append___redArg(v_recoveredErrors_3386_, v___x_3387_);
        return v___x_3388_;
    } else {
        let mut v_stxStack_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pos_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_recoveredErrors_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_errorMsg_3385_);
        v_stxStack_3389_ = leanh::lean_ctor_get(v_s_3384_, 0);
        leanh::lean_inc_ref(v_stxStack_3389_);
        v_pos_3390_ = leanh::lean_ctor_get(v_s_3384_, 2);
        leanh::lean_inc(v_pos_3390_);
        v_recoveredErrors_3391_ = leanh::lean_ctor_get(v_s_3384_, 5);
        leanh::lean_inc_ref(v_recoveredErrors_3391_);
        leanh::lean_dec_ref(v_s_3384_);
        v_val_3392_ = leanh::lean_ctor_get(v_errorMsg_3385_, 0);
        leanh::lean_inc(v_val_3392_);
        leanh::lean_dec_ref_known(v_errorMsg_3385_, 1);
        v___x_3393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3393_, 0, v_stxStack_3389_);
        leanh::lean_ctor_set(v___x_3393_, 1, v_val_3392_);
        v___x_3394_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3394_, 0, v_pos_3390_);
        leanh::lean_ctor_set(v___x_3394_, 1, v___x_3393_);
        v___x_3395_ = leanh::lean_unsigned_to_nat(1);
        v___x_3396_ = lean_mk_empty_array_with_capacity(v___x_3395_);
        v___x_3397_ = lean_array_push(v___x_3396_, v___x_3394_);
        v___x_3398_ = l_Array_append___redArg(v_recoveredErrors_3391_, v___x_3397_);
        leanh::lean_dec_ref(v___x_3397_);
        return v___x_3398_;
    }
}
pub unsafe fn l_Lean_Parser_ParserState_setError(
    mut v_s_3399_: *mut leanh::LeanObject,
    mut v_e_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3408_: u8 = 0;
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut v_unused_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3401_ = leanh::lean_ctor_get(v_s_3399_, 0);
                v_lhsPrec_3402_ = leanh::lean_ctor_get(v_s_3399_, 1);
                v_pos_3403_ = leanh::lean_ctor_get(v_s_3399_, 2);
                v_cache_3404_ = leanh::lean_ctor_get(v_s_3399_, 3);
                v_recoveredErrors_3405_ = leanh::lean_ctor_get(v_s_3399_, 5);
                v_isSharedCheck_3413_ = (!leanh::lean_is_exclusive(v_s_3399_)) as u8;
                if v_isSharedCheck_3413_ == 0 {
                    v_unused_3414_ = leanh::lean_ctor_get(v_s_3399_, 4);
                    leanh::lean_dec(v_unused_3414_);
                    v___x_3407_ = v_s_3399_;
                    v_isShared_3408_ = v_isSharedCheck_3413_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3405_);
                    leanh::lean_inc(v_cache_3404_);
                    leanh::lean_inc(v_pos_3403_);
                    leanh::lean_inc(v_lhsPrec_3402_);
                    leanh::lean_inc(v_stxStack_3401_);
                    leanh::lean_dec(v_s_3399_);
                    v___x_3407_ = leanh::lean_box(0);
                    v_isShared_3408_ = v_isSharedCheck_3413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3409_, 0, v_e_3400_);
                if v_isShared_3408_ == 0 {
                    leanh::lean_ctor_set(v___x_3407_, 4, v___x_3409_);
                    v___x_3411_ = v___x_3407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_stxStack_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_lhsPrec_3402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_pos_3403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_cache_3404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 4, v___x_3409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 5, v_recoveredErrors_3405_);
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
    mut v_s_3415_: *mut leanh::LeanObject,
    mut v_msg_3416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v_unused_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3417_ = leanh::lean_ctor_get(v_s_3415_, 0);
                v_lhsPrec_3418_ = leanh::lean_ctor_get(v_s_3415_, 1);
                v_pos_3419_ = leanh::lean_ctor_get(v_s_3415_, 2);
                v_cache_3420_ = leanh::lean_ctor_get(v_s_3415_, 3);
                v_recoveredErrors_3421_ = leanh::lean_ctor_get(v_s_3415_, 5);
                v_isSharedCheck_3435_ = (!leanh::lean_is_exclusive(v_s_3415_)) as u8;
                if v_isSharedCheck_3435_ == 0 {
                    v_unused_3436_ = leanh::lean_ctor_get(v_s_3415_, 4);
                    leanh::lean_dec(v_unused_3436_);
                    v___x_3423_ = v_s_3415_;
                    v_isShared_3424_ = v_isSharedCheck_3435_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3421_);
                    leanh::lean_inc(v_cache_3420_);
                    leanh::lean_inc(v_pos_3419_);
                    leanh::lean_inc(v_lhsPrec_3418_);
                    leanh::lean_inc(v_stxStack_3417_);
                    leanh::lean_dec(v_s_3415_);
                    v___x_3423_ = leanh::lean_box(0);
                    v_isShared_3424_ = v_isSharedCheck_3435_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3425_ = leanh::lean_box(0);
                v___x_3426_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_3427_ = leanh::lean_box(0);
                v___x_3428_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3428_, 0, v_msg_3416_);
                leanh::lean_ctor_set(v___x_3428_, 1, v___x_3427_);
                v___x_3429_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3429_, 0, v___x_3425_);
                leanh::lean_ctor_set(v___x_3429_, 1, v___x_3426_);
                leanh::lean_ctor_set(v___x_3429_, 2, v___x_3428_);
                v___x_3430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3430_, 0, v___x_3429_);
                if v_isShared_3424_ == 0 {
                    leanh::lean_ctor_set(v___x_3423_, 4, v___x_3430_);
                    v___x_3432_ = v___x_3423_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_stxStack_3417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_lhsPrec_3418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_pos_3419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_cache_3420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 4, v___x_3430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 5, v_recoveredErrors_3421_);
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
    mut v_s_3437_: *mut leanh::LeanObject,
    mut v_msg_3438_: *mut leanh::LeanObject,
    mut v_expected_3439_: *mut leanh::LeanObject,
    mut v_pushMissing_3440_: u8,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut v_unused_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3441_ = leanh::lean_ctor_get(v_s_3437_, 0);
                v_lhsPrec_3442_ = leanh::lean_ctor_get(v_s_3437_, 1);
                v_pos_3443_ = leanh::lean_ctor_get(v_s_3437_, 2);
                v_cache_3444_ = leanh::lean_ctor_get(v_s_3437_, 3);
                v_recoveredErrors_3445_ = leanh::lean_ctor_get(v_s_3437_, 5);
                v_isSharedCheck_3456_ = (!leanh::lean_is_exclusive(v_s_3437_)) as u8;
                if v_isSharedCheck_3456_ == 0 {
                    v_unused_3457_ = leanh::lean_ctor_get(v_s_3437_, 4);
                    leanh::lean_dec(v_unused_3457_);
                    v___x_3447_ = v_s_3437_;
                    v_isShared_3448_ = v_isSharedCheck_3456_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3445_);
                    leanh::lean_inc(v_cache_3444_);
                    leanh::lean_inc(v_pos_3443_);
                    leanh::lean_inc(v_lhsPrec_3442_);
                    leanh::lean_inc(v_stxStack_3441_);
                    leanh::lean_dec(v_s_3437_);
                    v___x_3447_ = leanh::lean_box(0);
                    v_isShared_3448_ = v_isSharedCheck_3456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3449_ = leanh::lean_box(0);
                v___x_3450_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3450_, 0, v___x_3449_);
                leanh::lean_ctor_set(v___x_3450_, 1, v_msg_3438_);
                leanh::lean_ctor_set(v___x_3450_, 2, v_expected_3439_);
                v___x_3451_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3451_, 0, v___x_3450_);
                if v_isShared_3448_ == 0 {
                    leanh::lean_ctor_set(v___x_3447_, 4, v___x_3451_);
                    v_s_3453_ = v___x_3447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_stxStack_3441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_lhsPrec_3442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_pos_3443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 3, v_cache_3444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 4, v___x_3451_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 5, v_recoveredErrors_3445_);
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
    mut v_s_3458_: *mut leanh::LeanObject,
    mut v_msg_3459_: *mut leanh::LeanObject,
    mut v_expected_3460_: *mut leanh::LeanObject,
    mut v_pushMissing_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pushMissing_boxed_3462_: u8 = 0;
    let mut v_res_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pushMissing_boxed_3462_ = (leanh::lean_unbox(v_pushMissing_3461_) as u8);
    v_res_3463_ = l_Lean_Parser_ParserState_mkUnexpectedError(
        v_s_3458_,
        v_msg_3459_,
        v_expected_3460_,
        v_pushMissing_boxed_3462_,
    );
    return v_res_3463_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkEOIError(
    mut v_s_3465_: *mut leanh::LeanObject,
    mut v_expected_3466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_s_3470_: *mut leanh::LeanObject,
    mut v_ex_3471_: *mut leanh::LeanObject,
    mut v_pos_3472_: *mut leanh::LeanObject,
    mut v_initStackSz_x3f_3473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v_unused_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_3494_ = l_Lean_Parser_ParserState_setPos(v_s_3470_, v_pos_3472_);
                if leanh::lean_obj_tag(v_initStackSz_x3f_3473_) == 1 {
                    v_val_3495_ = leanh::lean_ctor_get(v_initStackSz_x3f_3473_, 0);
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
                v_stxStack_3476_ = leanh::lean_ctor_get(v_s_3475_, 0);
                v_lhsPrec_3477_ = leanh::lean_ctor_get(v_s_3475_, 1);
                v_pos_3478_ = leanh::lean_ctor_get(v_s_3475_, 2);
                v_cache_3479_ = leanh::lean_ctor_get(v_s_3475_, 3);
                v_recoveredErrors_3480_ = leanh::lean_ctor_get(v_s_3475_, 5);
                v_isSharedCheck_3492_ = (!leanh::lean_is_exclusive(v_s_3475_)) as u8;
                if v_isSharedCheck_3492_ == 0 {
                    v_unused_3493_ = leanh::lean_ctor_get(v_s_3475_, 4);
                    leanh::lean_dec(v_unused_3493_);
                    v___x_3482_ = v_s_3475_;
                    v_isShared_3483_ = v_isSharedCheck_3492_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3480_);
                    leanh::lean_inc(v_cache_3479_);
                    leanh::lean_inc(v_pos_3478_);
                    leanh::lean_inc(v_lhsPrec_3477_);
                    leanh::lean_inc(v_stxStack_3476_);
                    leanh::lean_dec(v_s_3475_);
                    v___x_3482_ = leanh::lean_box(0);
                    v_isShared_3483_ = v_isSharedCheck_3492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3484_ = leanh::lean_box(0);
                v___x_3485_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_3486_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3486_, 0, v___x_3484_);
                leanh::lean_ctor_set(v___x_3486_, 1, v___x_3485_);
                leanh::lean_ctor_set(v___x_3486_, 2, v_ex_3471_);
                v___x_3487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3487_, 0, v___x_3486_);
                if v_isShared_3483_ == 0 {
                    leanh::lean_ctor_set(v___x_3482_, 4, v___x_3487_);
                    v_s_3489_ = v___x_3482_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_stxStack_3476_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_lhsPrec_3477_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_pos_3478_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 3, v_cache_3479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 4, v___x_3487_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 5, v_recoveredErrors_3480_);
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
    mut v_s_3497_: *mut leanh::LeanObject,
    mut v_ex_3498_: *mut leanh::LeanObject,
    mut v_pos_3499_: *mut leanh::LeanObject,
    mut v_initStackSz_x3f_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3501_ = l_Lean_Parser_ParserState_mkErrorsAt(
        v_s_3497_,
        v_ex_3498_,
        v_pos_3499_,
        v_initStackSz_x3f_3500_,
    );
    leanh::lean_dec(v_initStackSz_x3f_3500_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkErrorAt(
    mut v_s_3502_: *mut leanh::LeanObject,
    mut v_msg_3503_: *mut leanh::LeanObject,
    mut v_pos_3504_: *mut leanh::LeanObject,
    mut v_initStackSz_x3f_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3506_ = leanh::lean_box(0);
    v___x_3507_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3507_, 0, v_msg_3503_);
    leanh::lean_ctor_set(v___x_3507_, 1, v___x_3506_);
    v___x_3508_ = l_Lean_Parser_ParserState_mkErrorsAt(
        v_s_3502_,
        v___x_3507_,
        v_pos_3504_,
        v_initStackSz_x3f_3505_,
    );
    return v___x_3508_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkErrorAt___boxed(
    mut v_s_3509_: *mut leanh::LeanObject,
    mut v_msg_3510_: *mut leanh::LeanObject,
    mut v_pos_3511_: *mut leanh::LeanObject,
    mut v_initStackSz_x3f_3512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3513_ = l_Lean_Parser_ParserState_mkErrorAt(
        v_s_3509_,
        v_msg_3510_,
        v_pos_3511_,
        v_initStackSz_x3f_3512_,
    );
    leanh::lean_dec(v_initStackSz_x3f_3512_);
    return v_res_3513_;
}
pub unsafe fn l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(
    mut v_msg_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = leanh::lean_unsigned_to_nat(0);
    v___x_3516_ = lean_panic_fn_borrowed(v___x_3515_, v_msg_3514_);
    return v___x_3516_;
}
pub unsafe fn _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2;
    v___x_3521_ = leanh::lean_unsigned_to_nat(14);
    v___x_3522_ = leanh::lean_unsigned_to_nat(22);
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
    mut v_s_3526_: *mut leanh::LeanObject,
    mut v_ex_3527_: *mut leanh::LeanObject,
    mut v_iniPos_3528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_unused_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3529_ = leanh::lean_ctor_get(v_s_3526_, 0);
                v_tk_3530_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3529_);
                v___x_3553_ = leanh::lean_unsigned_to_nat(0);
                v___x_3554_ = lean_nat_dec_lt(v___x_3553_, v_iniPos_3528_);
                if v___x_3554_ == 0 {
                    leanh::lean_dec(v_iniPos_3528_);
                    v___x_3555_ = l_Lean_Syntax_getPos_x3f(v_tk_3530_, v___x_3554_);
                    if leanh::lean_obj_tag(v___x_3555_) == 0 {
                        v___x_3556_ = leanh::lean_obj_once(
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
                        v_val_3558_ = leanh::lean_ctor_get(v___x_3555_, 0);
                        leanh::lean_inc(v_val_3558_);
                        leanh::lean_dec_ref_known(v___x_3555_, 1);
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
                v_stxStack_3534_ = leanh::lean_ctor_get(v_s_3533_, 0);
                v_lhsPrec_3535_ = leanh::lean_ctor_get(v_s_3533_, 1);
                v_pos_3536_ = leanh::lean_ctor_get(v_s_3533_, 2);
                v_cache_3537_ = leanh::lean_ctor_get(v_s_3533_, 3);
                v_recoveredErrors_3538_ = leanh::lean_ctor_get(v_s_3533_, 5);
                v_isSharedCheck_3551_ = (!leanh::lean_is_exclusive(v_s_3533_)) as u8;
                if v_isSharedCheck_3551_ == 0 {
                    v_unused_3552_ = leanh::lean_ctor_get(v_s_3533_, 4);
                    leanh::lean_dec(v_unused_3552_);
                    v___x_3540_ = v_s_3533_;
                    v_isShared_3541_ = v_isSharedCheck_3551_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3538_);
                    leanh::lean_inc(v_cache_3537_);
                    leanh::lean_inc(v_pos_3536_);
                    leanh::lean_inc(v_lhsPrec_3535_);
                    leanh::lean_inc(v_stxStack_3534_);
                    leanh::lean_dec(v_s_3533_);
                    v___x_3540_ = leanh::lean_box(0);
                    v_isShared_3541_ = v_isSharedCheck_3551_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3542_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
                v___x_3543_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3543_, 0, v_tk_3530_);
                leanh::lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                leanh::lean_ctor_set(v___x_3543_, 2, v_ex_3527_);
                v___x_3544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                if v_isShared_3541_ == 0 {
                    leanh::lean_ctor_set(v___x_3540_, 4, v___x_3544_);
                    v_s_3546_ = v___x_3540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_stxStack_3534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_lhsPrec_3535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_pos_3536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_cache_3537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 4, v___x_3544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 5, v_recoveredErrors_3538_);
                    v_s_3546_ = v_reuseFailAlloc_3550_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3547_ = l_Lean_Parser_ParserState_popSyntax(v_s_3546_);
                v___x_3548_ = leanh::lean_box(0);
                v___x_3549_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3547_, v___x_3548_);
                return v___x_3549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_ParserState_mkUnexpectedTokenError(
    mut v_s_3559_: *mut leanh::LeanObject,
    mut v_msg_3560_: *mut leanh::LeanObject,
    mut v_iniPos_3561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3562_ = leanh::lean_box(0);
    v___x_3563_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3563_, 0, v_msg_3560_);
    leanh::lean_ctor_set(v___x_3563_, 1, v___x_3562_);
    v___x_3564_ =
        l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_3559_, v___x_3563_, v_iniPos_3561_);
    return v___x_3564_;
}
pub unsafe fn l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
    mut v_s_3565_: *mut leanh::LeanObject,
    mut v_msg_3566_: *mut leanh::LeanObject,
    mut v_pos_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = l_Lean_Parser_ParserState_setPos(v_s_3565_, v_pos_3567_);
    v___x_3569_ = leanh::lean_box(0);
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
    mut v_ctx_3573_: *mut leanh::LeanObject,
    mut v_as_3574_: *mut leanh::LeanObject,
    mut v_sz_3575_: usize,
    mut v_i_3576_: usize,
    mut v_b_3577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3578_: u8 = 0;
    let mut v_a_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errStr_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: usize = 0;
    let mut v___x_3593_: usize = 0;
    let mut v_errStr_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3578_ = lean_usize_dec_lt(v_i_3576_, v_sz_3575_);
                if v___x_3578_ == 0 {
                    leanh::lean_dec_ref(v_ctx_3573_);
                    return v_b_3577_;
                } else {
                    v_a_3579_ = lean_array_uget_borrowed(v_as_3574_, v_i_3576_);
                    v_snd_3580_ = leanh::lean_ctor_get(v_a_3579_, 1);
                    v_fst_3581_ = leanh::lean_ctor_get(v_a_3579_, 0);
                    v_snd_3582_ = leanh::lean_ctor_get(v_snd_3580_, 1);
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
                v_fileName_3585_ = leanh::lean_ctor_get(v_ctx_3573_, 1);
                v_fileMap_3586_ = leanh::lean_ctor_get(v_ctx_3573_, 2);
                leanh::lean_inc_ref(v_fileMap_3586_);
                v___x_3587_ = l_Lean_FileMap_toPosition(v_fileMap_3586_, v_fst_3581_);
                leanh::lean_inc(v_snd_3582_);
                v___x_3588_ = l_Lean_Parser_Error_toString(v_snd_3582_);
                v___x_3589_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_fileName_3585_);
                v___x_3590_ = l_Lean_mkErrorStringWithPos(
                    v_fileName_3585_,
                    v___x_3587_,
                    v___x_3588_,
                    v___x_3589_,
                    v___x_3589_,
                    v___x_3589_,
                );
                leanh::lean_dec_ref(v___x_3588_);
                v___x_3591_ = lean_string_append(v_errStr_3584_, v___x_3590_);
                leanh::lean_dec_ref(v___x_3590_);
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
    mut v_ctx_3599_: *mut leanh::LeanObject,
    mut v_as_3600_: *mut leanh::LeanObject,
    mut v_sz_3601_: *mut leanh::LeanObject,
    mut v_i_3602_: *mut leanh::LeanObject,
    mut v_b_3603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3604_: usize = 0;
    let mut v_i_boxed_3605_: usize = 0;
    let mut v_res_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3604_ = leanh::lean_unbox_usize(v_sz_3601_);
    leanh::lean_dec(v_sz_3601_);
    v_i_boxed_3605_ = leanh::lean_unbox_usize(v_i_3602_);
    leanh::lean_dec(v_i_3602_);
    v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_3599_, v_as_3600_, v_sz_boxed_3604_, v_i_boxed_3605_, v_b_3603_);
    leanh::lean_dec_ref(v_as_3600_);
    return v_res_3606_;
}
pub unsafe fn l_Lean_Parser_ParserState_toErrorMsg(
    mut v_ctx_3607_: *mut leanh::LeanObject,
    mut v_s_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_errStr_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_errStr_3609_ = l_Lean_Parser_instInhabitedInputContext___closed__0;
    v___x_3610_ = l_Lean_Parser_ParserState_allErrors(v_s_3608_);
    v_sz_3611_ = lean_array_size(v___x_3610_);
    v___x_3612_ = 0usize;
    v___x_3613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_3607_, v___x_3610_, v_sz_3611_, v___x_3612_, v_errStr_3609_);
    leanh::lean_dec_ref(v___x_3610_);
    return v___x_3613_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserFn___lam__0(
    mut v_x_3614_: *mut leanh::LeanObject,
    mut v_s_3615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_s_3615_);
    return v_s_3615_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(
    mut v_x_3616_: *mut leanh::LeanObject,
    mut v_s_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_3616_, v_s_3617_);
    leanh::lean_dec_ref(v_s_3617_);
    leanh::lean_dec_ref(v_x_3616_);
    return v_res_3618_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorIdx(
    mut v_x_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3621_) {
        0 => {
            let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3622_ = leanh::lean_unsigned_to_nat(0);
            return v___x_3622_;
        }
        1 => {
            let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3623_ = leanh::lean_unsigned_to_nat(1);
            return v___x_3623_;
        }
        2 => {
            let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3624_ = leanh::lean_unsigned_to_nat(2);
            return v___x_3624_;
        }
        _ => {
            let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3625_ = leanh::lean_unsigned_to_nat(3);
            return v___x_3625_;
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorIdx___boxed(
    mut v_x_3626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3627_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_3626_);
    leanh::lean_dec(v_x_3626_);
    return v_res_3627_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorElim___redArg(
    mut v_t_3628_: *mut leanh::LeanObject,
    mut v_k_3629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_3628_) {
        2 => {
            let mut v_a_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3630_ = leanh::lean_ctor_get(v_t_3628_, 0);
            leanh::lean_inc(v_a_3630_);
            leanh::lean_dec_ref_known(v_t_3628_, 1);
            v___x_3631_ = leanh::lean_apply_1(v_k_3629_, v_a_3630_);
            return v___x_3631_;
        }
        3 => {
            let mut v_a_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3632_ = leanh::lean_ctor_get(v_t_3628_, 0);
            leanh::lean_inc(v_a_3632_);
            leanh::lean_dec_ref_known(v_t_3628_, 1);
            v___x_3633_ = leanh::lean_apply_1(v_k_3629_, v_a_3632_);
            return v___x_3633_;
        }
        _ => {
            leanh::lean_dec(v_t_3628_);
            return v_k_3629_;
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorElim(
    mut v_motive_3634_: *mut leanh::LeanObject,
    mut v_ctorIdx_3635_: *mut leanh::LeanObject,
    mut v_t_3636_: *mut leanh::LeanObject,
    mut v_h_3637_: *mut leanh::LeanObject,
    mut v_k_3638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3639_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3636_, v_k_3638_);
    return v___x_3639_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_ctorElim___boxed(
    mut v_motive_3640_: *mut leanh::LeanObject,
    mut v_ctorIdx_3641_: *mut leanh::LeanObject,
    mut v_t_3642_: *mut leanh::LeanObject,
    mut v_h_3643_: *mut leanh::LeanObject,
    mut v_k_3644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3645_ = l_Lean_Parser_FirstTokens_ctorElim(
        v_motive_3640_,
        v_ctorIdx_3641_,
        v_t_3642_,
        v_h_3643_,
        v_k_3644_,
    );
    leanh::lean_dec(v_ctorIdx_3641_);
    return v_res_3645_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_epsilon_elim___redArg(
    mut v_t_3646_: *mut leanh::LeanObject,
    mut v_epsilon_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3648_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3646_, v_epsilon_3647_);
    return v___x_3648_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_epsilon_elim(
    mut v_motive_3649_: *mut leanh::LeanObject,
    mut v_t_3650_: *mut leanh::LeanObject,
    mut v_h_3651_: *mut leanh::LeanObject,
    mut v_epsilon_3652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3653_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3650_, v_epsilon_3652_);
    return v___x_3653_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_unknown_elim___redArg(
    mut v_t_3654_: *mut leanh::LeanObject,
    mut v_unknown_3655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3654_, v_unknown_3655_);
    return v___x_3656_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_unknown_elim(
    mut v_motive_3657_: *mut leanh::LeanObject,
    mut v_t_3658_: *mut leanh::LeanObject,
    mut v_h_3659_: *mut leanh::LeanObject,
    mut v_unknown_3660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3661_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3658_, v_unknown_3660_);
    return v___x_3661_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_tokens_elim___redArg(
    mut v_t_3662_: *mut leanh::LeanObject,
    mut v_tokens_3663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3664_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3662_, v_tokens_3663_);
    return v___x_3664_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_tokens_elim(
    mut v_motive_3665_: *mut leanh::LeanObject,
    mut v_t_3666_: *mut leanh::LeanObject,
    mut v_h_3667_: *mut leanh::LeanObject,
    mut v_tokens_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3669_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3666_, v_tokens_3668_);
    return v___x_3669_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_optTokens_elim___redArg(
    mut v_t_3670_: *mut leanh::LeanObject,
    mut v_optTokens_3671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3670_, v_optTokens_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_optTokens_elim(
    mut v_motive_3673_: *mut leanh::LeanObject,
    mut v_t_3674_: *mut leanh::LeanObject,
    mut v_h_3675_: *mut leanh::LeanObject,
    mut v_optTokens_3676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3677_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_3674_, v_optTokens_3676_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedFirstTokens_default() -> *mut leanh::LeanObject
{
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3678_ = leanh::lean_box(0);
    return v___x_3678_;
}
pub unsafe fn _init_l_Lean_Parser_instInhabitedFirstTokens() -> *mut leanh::LeanObject {
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3679_ = leanh::lean_box(0);
    return v___x_3679_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_seq(
    mut v_x_3680_: *mut leanh::LeanObject,
    mut v_x_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3680_) {
                0 => {
                    return v_x_3681_;
                }
                3 => match leanh::lean_obj_tag(v_x_3681_) {
                    3 => {
                        v_a_3682_ = leanh::lean_ctor_get(v_x_3680_, 0);
                        leanh::lean_inc(v_a_3682_);
                        leanh::lean_dec_ref_known(v_x_3680_, 1);
                        v_a_3683_ = leanh::lean_ctor_get(v_x_3681_, 0);
                        v_isSharedCheck_3691_ = (!leanh::lean_is_exclusive(v_x_3681_)) as u8;
                        if v_isSharedCheck_3691_ == 0 {
                            v___x_3685_ = v_x_3681_;
                            v_isShared_3686_ = v_isSharedCheck_3691_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3683_);
                            leanh::lean_dec(v_x_3681_);
                            v___x_3685_ = leanh::lean_box(0);
                            v_isShared_3686_ = v_isSharedCheck_3691_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_a_3692_ = leanh::lean_ctor_get(v_x_3680_, 0);
                        leanh::lean_inc(v_a_3692_);
                        leanh::lean_dec_ref_known(v_x_3680_, 1);
                        v_a_3693_ = leanh::lean_ctor_get(v_x_3681_, 0);
                        v_isSharedCheck_3701_ = (!leanh::lean_is_exclusive(v_x_3681_)) as u8;
                        if v_isSharedCheck_3701_ == 0 {
                            v___x_3695_ = v_x_3681_;
                            v_isShared_3696_ = v_isSharedCheck_3701_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3693_);
                            leanh::lean_dec(v_x_3681_);
                            v___x_3695_ = leanh::lean_box(0);
                            v_isShared_3696_ = v_isSharedCheck_3701_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        leanh::lean_dec_ref_known(v_x_3680_, 1);
                        return v_x_3681_;
                    }
                    _ => {
                        leanh::lean_dec(v_x_3681_);
                        return v_x_3680_;
                    }
                },
                _ => {
                    leanh::lean_dec(v_x_3681_);
                    return v_x_3680_;
                }
            },
            1 => {
                v___x_3687_ = l_List_appendTR___redArg(v_a_3682_, v_a_3683_);
                if v_isShared_3686_ == 0 {
                    leanh::lean_ctor_set(v___x_3685_, 0, v___x_3687_);
                    v___x_3689_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
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
                    leanh::lean_ctor_set(v___x_3695_, 0, v___x_3697_);
                    v___x_3699_ = v___x_3695_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
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
    mut v_x_3702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3702_) == 2 {
                    v_a_3703_ = leanh::lean_ctor_get(v_x_3702_, 0);
                    v_isSharedCheck_3710_ = (!leanh::lean_is_exclusive(v_x_3702_)) as u8;
                    if v_isSharedCheck_3710_ == 0 {
                        v___x_3705_ = v_x_3702_;
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3703_);
                        leanh::lean_dec(v_x_3702_);
                        v___x_3705_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set_tag(v___x_3705_, 3);
                    v___x_3708_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
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
    mut v_x_3711_: *mut leanh::LeanObject,
    mut v_x_3712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_u2081_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_u2082_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v_a_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3711_) {
                0 => {
                    v___x_3718_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3712_);
                    return v___x_3718_;
                }
                2 => match leanh::lean_obj_tag(v_x_3712_) {
                    0 => {
                        v___x_3719_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3711_);
                        return v___x_3719_;
                    }
                    2 => {
                        v_a_3720_ = leanh::lean_ctor_get(v_x_3711_, 0);
                        leanh::lean_inc(v_a_3720_);
                        leanh::lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3721_ = leanh::lean_ctor_get(v_x_3712_, 0);
                        v_isSharedCheck_3729_ = (!leanh::lean_is_exclusive(v_x_3712_)) as u8;
                        if v_isSharedCheck_3729_ == 0 {
                            v___x_3723_ = v_x_3712_;
                            v_isShared_3724_ = v_isSharedCheck_3729_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3721_);
                            leanh::lean_dec(v_x_3712_);
                            v___x_3723_ = leanh::lean_box(0);
                            v_isShared_3724_ = v_isSharedCheck_3729_;
                            state = 2;
                            continue;
                        }
                    }
                    3 => {
                        v_a_3730_ = leanh::lean_ctor_get(v_x_3711_, 0);
                        leanh::lean_inc(v_a_3730_);
                        leanh::lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3731_ = leanh::lean_ctor_get(v_x_3712_, 0);
                        leanh::lean_inc(v_a_3731_);
                        leanh::lean_dec_ref_known(v_x_3712_, 1);
                        v_s_u2081_3714_ = v_a_3730_;
                        v_s_u2082_3715_ = v_a_3731_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref_known(v_x_3711_, 1);
                        leanh::lean_dec(v_x_3712_);
                        v___x_3732_ = leanh::lean_box(1);
                        return v___x_3732_;
                    }
                },
                3 => match leanh::lean_obj_tag(v_x_3712_) {
                    0 => {
                        v___x_3733_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3711_);
                        return v___x_3733_;
                    }
                    3 => {
                        v_a_3734_ = leanh::lean_ctor_get(v_x_3711_, 0);
                        leanh::lean_inc(v_a_3734_);
                        leanh::lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3735_ = leanh::lean_ctor_get(v_x_3712_, 0);
                        leanh::lean_inc(v_a_3735_);
                        leanh::lean_dec_ref_known(v_x_3712_, 1);
                        v_s_u2081_3714_ = v_a_3734_;
                        v_s_u2082_3715_ = v_a_3735_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v_a_3736_ = leanh::lean_ctor_get(v_x_3711_, 0);
                        leanh::lean_inc(v_a_3736_);
                        leanh::lean_dec_ref_known(v_x_3711_, 1);
                        v_a_3737_ = leanh::lean_ctor_get(v_x_3712_, 0);
                        leanh::lean_inc(v_a_3737_);
                        leanh::lean_dec_ref_known(v_x_3712_, 1);
                        v_s_u2081_3714_ = v_a_3736_;
                        v_s_u2082_3715_ = v_a_3737_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref_known(v_x_3711_, 1);
                        leanh::lean_dec(v_x_3712_);
                        v___x_3738_ = leanh::lean_box(1);
                        return v___x_3738_;
                    }
                },
                _ => {
                    if leanh::lean_obj_tag(v_x_3712_) == 0 {
                        v___x_3739_ = l_Lean_Parser_FirstTokens_toOptional(v_x_3711_);
                        return v___x_3739_;
                    } else {
                        leanh::lean_dec(v_x_3712_);
                        leanh::lean_dec(v_x_3711_);
                        v___x_3740_ = leanh::lean_box(1);
                        return v___x_3740_;
                    }
                }
            },
            1 => {
                v___x_3716_ = l_List_appendTR___redArg(v_s_u2081_3714_, v_s_u2082_3715_);
                v___x_3717_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3717_, 0, v___x_3716_);
                return v___x_3717_;
            }
            2 => {
                v___x_3725_ = l_List_appendTR___redArg(v_a_3720_, v_a_3721_);
                if v_isShared_3724_ == 0 {
                    leanh::lean_ctor_set(v___x_3723_, 0, v___x_3725_);
                    v___x_3727_ = v___x_3723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
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
    mut v_x_3741_: *mut leanh::LeanObject,
    mut v_x_3742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3742_) == 0 {
                    return v_x_3741_;
                } else {
                    v_head_3743_ = leanh::lean_ctor_get(v_x_3742_, 0);
                    v_tail_3744_ = leanh::lean_ctor_get(v_x_3742_, 1);
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
    mut v_x_3749_: *mut leanh::LeanObject,
    mut v_x_3750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3751_ =
        l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(
            v_x_3749_, v_x_3750_,
        );
    leanh::lean_dec(v_x_3750_);
    return v_res_3751_;
}
pub unsafe fn l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(
    mut v_x_3755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3755_) == 0 {
        let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3756_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0;
        return v___x_3756_;
    } else {
        let mut v_tail_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_3757_ = leanh::lean_ctor_get(v_x_3755_, 1);
        if leanh::lean_obj_tag(v_tail_3757_) == 0 {
            let mut v_head_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_3758_ = leanh::lean_ctor_get(v_x_3755_, 0);
            v___x_3759_ =
                l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1;
            v___x_3760_ = lean_string_append(v___x_3759_, v_head_3758_);
            v___x_3761_ =
                l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2;
            v___x_3762_ = lean_string_append(v___x_3760_, v___x_3761_);
            return v___x_3762_;
        } else {
            let mut v_head_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3767_: u32 = 0;
            let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_3763_ = leanh::lean_ctor_get(v_x_3755_, 0);
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
    mut v_x_3769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3770_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_3769_);
    leanh::lean_dec(v_x_3769_);
    return v_res_3770_;
}
pub unsafe fn l_Lean_Parser_FirstTokens_toStr(
    mut v_x_3774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3774_) {
        0 => {
            let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3775_ = l_Lean_Parser_FirstTokens_toStr___closed__0;
            return v___x_3775_;
        }
        1 => {
            let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3776_ = l_Lean_Parser_FirstTokens_toStr___closed__1;
            return v___x_3776_;
        }
        2 => {
            let mut v_a_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3777_ = leanh::lean_ctor_get(v_x_3774_, 0);
            v___x_3778_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_3777_);
            return v___x_3778_;
        }
        _ => {
            let mut v_a_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3779_ = leanh::lean_ctor_get(v_x_3774_, 0);
            v___x_3780_ = l_Lean_Parser_FirstTokens_toStr___closed__2;
            v___x_3781_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_3779_);
            v___x_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
            leanh::lean_dec_ref(v___x_3781_);
            return v___x_3782_;
        }
    }
}
pub unsafe fn l_Lean_Parser_FirstTokens_toStr___boxed(
    mut v_x_3783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3784_ = l_Lean_Parser_FirstTokens_toStr(v_x_3783_);
    leanh::lean_dec(v_x_3783_);
    return v_res_3784_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__0(
    mut v___y_3787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___y_3787_);
    return v___y_3787_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(
    mut v___y_3788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3789_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_3788_);
    leanh::lean_dec(v___y_3788_);
    return v_res_3789_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__1(
    mut v___y_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_3790_);
    return v___y_3790_;
}
pub unsafe fn l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(
    mut v___y_3791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_3791_);
    leanh::lean_dec_ref(v___y_3791_);
    return v_res_3792_;
}
pub unsafe fn l_Lean_Parser_withFn(
    mut v_f_3806_: *mut leanh::LeanObject,
    mut v_p_3807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3808_ = leanh::lean_ctor_get(v_p_3807_, 0);
                v_fn_3809_ = leanh::lean_ctor_get(v_p_3807_, 1);
                v_isSharedCheck_3817_ = (!leanh::lean_is_exclusive(v_p_3807_)) as u8;
                if v_isSharedCheck_3817_ == 0 {
                    v___x_3811_ = v_p_3807_;
                    v_isShared_3812_ = v_isSharedCheck_3817_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fn_3809_);
                    leanh::lean_inc(v_info_3808_);
                    leanh::lean_dec(v_p_3807_);
                    v___x_3811_ = leanh::lean_box(0);
                    v_isShared_3812_ = v_isSharedCheck_3817_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3813_ = leanh::lean_apply_1(v_f_3806_, v_fn_3809_);
                if v_isShared_3812_ == 0 {
                    leanh::lean_ctor_set(v___x_3811_, 1, v___x_3813_);
                    v___x_3815_ = v___x_3811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_info_3808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 1, v___x_3813_);
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
    mut v_f_3818_: *mut leanh::LeanObject,
    mut v_p_3819_: *mut leanh::LeanObject,
    mut v_c_3820_: *mut leanh::LeanObject,
    mut v_s_3821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toParserModuleContext_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tokens_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3822_ = leanh::lean_ctor_get(v_c_3820_, 0);
                v_toParserModuleContext_3823_ = leanh::lean_ctor_get(v_c_3820_, 1);
                v_toCacheableParserContext_3824_ = leanh::lean_ctor_get(v_c_3820_, 2);
                v_tokens_3825_ = leanh::lean_ctor_get(v_c_3820_, 3);
                v_isSharedCheck_3834_ = (!leanh::lean_is_exclusive(v_c_3820_)) as u8;
                if v_isSharedCheck_3834_ == 0 {
                    v___x_3827_ = v_c_3820_;
                    v_isShared_3828_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tokens_3825_);
                    leanh::lean_inc(v_toCacheableParserContext_3824_);
                    leanh::lean_inc(v_toParserModuleContext_3823_);
                    leanh::lean_inc(v_toInputContext_3822_);
                    leanh::lean_dec(v_c_3820_);
                    v___x_3827_ = leanh::lean_box(0);
                    v_isShared_3828_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3829_ =
                    leanh::lean_apply_1(v_f_3818_, v_toCacheableParserContext_3824_);
                if v_isShared_3828_ == 0 {
                    leanh::lean_ctor_set(v___x_3827_, 2, v___x_3829_);
                    v___x_3831_ = v___x_3827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_toInputContext_3822_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3833_,
                        1,
                        v_toParserModuleContext_3823_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 2, v___x_3829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_tokens_3825_);
                    v___x_3831_ = v_reuseFailAlloc_3833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3832_ = leanh::lean_apply_2(v_p_3819_, v___x_3831_, v_s_3821_);
                return v___x_3832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_adaptCacheableContext(
    mut v_f_3835_: *mut leanh::LeanObject,
    mut v_p_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3837_ = leanh::lean_ctor_get(v_p_3836_, 0);
                v_fn_3838_ = leanh::lean_ctor_get(v_p_3836_, 1);
                v_isSharedCheck_3846_ = (!leanh::lean_is_exclusive(v_p_3836_)) as u8;
                if v_isSharedCheck_3846_ == 0 {
                    v___x_3840_ = v_p_3836_;
                    v_isShared_3841_ = v_isSharedCheck_3846_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fn_3838_);
                    leanh::lean_inc(v_info_3837_);
                    leanh::lean_dec(v_p_3836_);
                    v___x_3840_ = leanh::lean_box(0);
                    v_isShared_3841_ = v_isSharedCheck_3846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3842_ = leanh::lean_alloc_closure(
                    l_Lean_Parser_adaptCacheableContextFn as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___x_3842_, 0, v_f_3835_);
                leanh::lean_closure_set(v___x_3842_, 1, v_fn_3838_);
                if v_isShared_3841_ == 0 {
                    leanh::lean_ctor_set(v___x_3840_, 1, v___x_3842_);
                    v___x_3844_ = v___x_3840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_info_3837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3842_);
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
    mut v_drop_3847_: *mut leanh::LeanObject,
    mut v_p_3848_: *mut leanh::LeanObject,
    mut v_c_3849_: *mut leanh::LeanObject,
    mut v_s_3850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stxStack_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v_raw_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_drop_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3864_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v_raw_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut v_unused_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3891_: u8 = 0;
    let mut v_reuseFailAlloc_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3894_: u8 = 0;
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stxStack_3851_ = leanh::lean_ctor_get(v_s_3850_, 0);
                v_lhsPrec_3852_ = leanh::lean_ctor_get(v_s_3850_, 1);
                v_pos_3853_ = leanh::lean_ctor_get(v_s_3850_, 2);
                v_cache_3854_ = leanh::lean_ctor_get(v_s_3850_, 3);
                v_errorMsg_3855_ = leanh::lean_ctor_get(v_s_3850_, 4);
                v_recoveredErrors_3856_ = leanh::lean_ctor_get(v_s_3850_, 5);
                v_isSharedCheck_3895_ = (!leanh::lean_is_exclusive(v_s_3850_)) as u8;
                if v_isSharedCheck_3895_ == 0 {
                    v___x_3858_ = v_s_3850_;
                    v_isShared_3859_ = v_isSharedCheck_3895_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3856_);
                    leanh::lean_inc(v_errorMsg_3855_);
                    leanh::lean_inc(v_cache_3854_);
                    leanh::lean_inc(v_pos_3853_);
                    leanh::lean_inc(v_lhsPrec_3852_);
                    leanh::lean_inc(v_stxStack_3851_);
                    leanh::lean_dec(v_s_3850_);
                    v___x_3858_ = leanh::lean_box(0);
                    v_isShared_3859_ = v_isSharedCheck_3895_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_raw_3860_ = leanh::lean_ctor_get(v_stxStack_3851_, 0);
                v_drop_3861_ = leanh::lean_ctor_get(v_stxStack_3851_, 1);
                v_isSharedCheck_3894_ = (!leanh::lean_is_exclusive(v_stxStack_3851_)) as u8;
                if v_isSharedCheck_3894_ == 0 {
                    v___x_3863_ = v_stxStack_3851_;
                    v_isShared_3864_ = v_isSharedCheck_3894_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_drop_3861_);
                    leanh::lean_inc(v_raw_3860_);
                    leanh::lean_dec(v_stxStack_3851_);
                    v___x_3863_ = leanh::lean_box(0);
                    v_isShared_3864_ = v_isSharedCheck_3894_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3864_ == 0 {
                    leanh::lean_ctor_set(v___x_3863_, 1, v_drop_3847_);
                    v___x_3866_ = v___x_3863_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3893_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_raw_3860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_drop_3847_);
                    v___x_3866_ = v_reuseFailAlloc_3893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3859_ == 0 {
                    leanh::lean_ctor_set(v___x_3858_, 0, v___x_3866_);
                    v___x_3868_ = v___x_3858_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3892_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_lhsPrec_3852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_pos_3853_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 3, v_cache_3854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 4, v_errorMsg_3855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 5, v_recoveredErrors_3856_);
                    v___x_3868_ = v_reuseFailAlloc_3892_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_s_3869_ = leanh::lean_apply_2(v_p_3848_, v_c_3849_, v___x_3868_);
                v_stxStack_3870_ = leanh::lean_ctor_get(v_s_3869_, 0);
                v_lhsPrec_3871_ = leanh::lean_ctor_get(v_s_3869_, 1);
                v_pos_3872_ = leanh::lean_ctor_get(v_s_3869_, 2);
                v_cache_3873_ = leanh::lean_ctor_get(v_s_3869_, 3);
                v_errorMsg_3874_ = leanh::lean_ctor_get(v_s_3869_, 4);
                v_recoveredErrors_3875_ = leanh::lean_ctor_get(v_s_3869_, 5);
                v_isSharedCheck_3891_ = (!leanh::lean_is_exclusive(v_s_3869_)) as u8;
                if v_isSharedCheck_3891_ == 0 {
                    v___x_3877_ = v_s_3869_;
                    v_isShared_3878_ = v_isSharedCheck_3891_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3875_);
                    leanh::lean_inc(v_errorMsg_3874_);
                    leanh::lean_inc(v_cache_3873_);
                    leanh::lean_inc(v_pos_3872_);
                    leanh::lean_inc(v_lhsPrec_3871_);
                    leanh::lean_inc(v_stxStack_3870_);
                    leanh::lean_dec(v_s_3869_);
                    v___x_3877_ = leanh::lean_box(0);
                    v_isShared_3878_ = v_isSharedCheck_3891_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_raw_3879_ = leanh::lean_ctor_get(v_stxStack_3870_, 0);
                v_isSharedCheck_3889_ = (!leanh::lean_is_exclusive(v_stxStack_3870_)) as u8;
                if v_isSharedCheck_3889_ == 0 {
                    v_unused_3890_ = leanh::lean_ctor_get(v_stxStack_3870_, 1);
                    leanh::lean_dec(v_unused_3890_);
                    v___x_3881_ = v_stxStack_3870_;
                    v_isShared_3882_ = v_isSharedCheck_3889_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_raw_3879_);
                    leanh::lean_dec(v_stxStack_3870_);
                    v___x_3881_ = leanh::lean_box(0);
                    v_isShared_3882_ = v_isSharedCheck_3889_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3882_ == 0 {
                    leanh::lean_ctor_set(v___x_3881_, 1, v_drop_3861_);
                    v___x_3884_ = v___x_3881_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_raw_3879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_drop_3861_);
                    v___x_3884_ = v_reuseFailAlloc_3888_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3878_ == 0 {
                    leanh::lean_ctor_set(v___x_3877_, 0, v___x_3884_);
                    v___x_3886_ = v___x_3877_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3887_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_lhsPrec_3871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_pos_3872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 3, v_cache_3873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 4, v_errorMsg_3874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 5, v_recoveredErrors_3875_);
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
    mut v_p_3896_: *mut leanh::LeanObject,
    mut v_c_3897_: *mut leanh::LeanObject,
    mut v_s_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v_tokenCache_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserCache_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_x27_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v_tokenCache_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut v_unused_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3940_: u8 = 0;
    let mut v_reuseFailAlloc_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cache_3899_ = leanh::lean_ctor_get(v_s_3898_, 3);
                v_stxStack_3900_ = leanh::lean_ctor_get(v_s_3898_, 0);
                v_lhsPrec_3901_ = leanh::lean_ctor_get(v_s_3898_, 1);
                v_pos_3902_ = leanh::lean_ctor_get(v_s_3898_, 2);
                v_errorMsg_3903_ = leanh::lean_ctor_get(v_s_3898_, 4);
                v_recoveredErrors_3904_ = leanh::lean_ctor_get(v_s_3898_, 5);
                v_isSharedCheck_3944_ = (!leanh::lean_is_exclusive(v_s_3898_)) as u8;
                if v_isSharedCheck_3944_ == 0 {
                    v___x_3906_ = v_s_3898_;
                    v_isShared_3907_ = v_isSharedCheck_3944_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3904_);
                    leanh::lean_inc(v_errorMsg_3903_);
                    leanh::lean_inc(v_cache_3899_);
                    leanh::lean_inc(v_pos_3902_);
                    leanh::lean_inc(v_lhsPrec_3901_);
                    leanh::lean_inc(v_stxStack_3900_);
                    leanh::lean_dec(v_s_3898_);
                    v___x_3906_ = leanh::lean_box(0);
                    v_isShared_3907_ = v_isSharedCheck_3944_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tokenCache_3908_ = leanh::lean_ctor_get(v_cache_3899_, 0);
                v_parserCache_3909_ = leanh::lean_ctor_get(v_cache_3899_, 1);
                v_isSharedCheck_3943_ = (!leanh::lean_is_exclusive(v_cache_3899_)) as u8;
                if v_isSharedCheck_3943_ == 0 {
                    v___x_3911_ = v_cache_3899_;
                    v_isShared_3912_ = v_isSharedCheck_3943_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_parserCache_3909_);
                    leanh::lean_inc(v_tokenCache_3908_);
                    leanh::lean_dec(v_cache_3899_);
                    v___x_3911_ = leanh::lean_box(0);
                    v_isShared_3912_ = v_isSharedCheck_3943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3913_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Parser_initCacheForInput___closed__2_once),
                    _init_l_Lean_Parser_initCacheForInput___closed__2,
                );
                if v_isShared_3912_ == 0 {
                    leanh::lean_ctor_set(v___x_3911_, 1, v___x_3913_);
                    v___x_3915_ = v___x_3911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_tokenCache_3908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 1, v___x_3913_);
                    v___x_3915_ = v_reuseFailAlloc_3942_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3907_ == 0 {
                    leanh::lean_ctor_set(v___x_3906_, 3, v___x_3915_);
                    v___x_3917_ = v___x_3906_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3941_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_stxStack_3900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_lhsPrec_3901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_pos_3902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 3, v___x_3915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_errorMsg_3903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 5, v_recoveredErrors_3904_);
                    v___x_3917_ = v_reuseFailAlloc_3941_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_s_x27_3918_ = leanh::lean_apply_2(v_p_3896_, v_c_3897_, v___x_3917_);
                v_cache_3919_ = leanh::lean_ctor_get(v_s_x27_3918_, 3);
                v_stxStack_3920_ = leanh::lean_ctor_get(v_s_x27_3918_, 0);
                v_lhsPrec_3921_ = leanh::lean_ctor_get(v_s_x27_3918_, 1);
                v_pos_3922_ = leanh::lean_ctor_get(v_s_x27_3918_, 2);
                v_errorMsg_3923_ = leanh::lean_ctor_get(v_s_x27_3918_, 4);
                v_recoveredErrors_3924_ = leanh::lean_ctor_get(v_s_x27_3918_, 5);
                v_isSharedCheck_3940_ = (!leanh::lean_is_exclusive(v_s_x27_3918_)) as u8;
                if v_isSharedCheck_3940_ == 0 {
                    v___x_3926_ = v_s_x27_3918_;
                    v_isShared_3927_ = v_isSharedCheck_3940_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_3924_);
                    leanh::lean_inc(v_errorMsg_3923_);
                    leanh::lean_inc(v_cache_3919_);
                    leanh::lean_inc(v_pos_3922_);
                    leanh::lean_inc(v_lhsPrec_3921_);
                    leanh::lean_inc(v_stxStack_3920_);
                    leanh::lean_dec(v_s_x27_3918_);
                    v___x_3926_ = leanh::lean_box(0);
                    v_isShared_3927_ = v_isSharedCheck_3940_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_tokenCache_3928_ = leanh::lean_ctor_get(v_cache_3919_, 0);
                v_isSharedCheck_3938_ = (!leanh::lean_is_exclusive(v_cache_3919_)) as u8;
                if v_isSharedCheck_3938_ == 0 {
                    v_unused_3939_ = leanh::lean_ctor_get(v_cache_3919_, 1);
                    leanh::lean_dec(v_unused_3939_);
                    v___x_3930_ = v_cache_3919_;
                    v_isShared_3931_ = v_isSharedCheck_3938_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_tokenCache_3928_);
                    leanh::lean_dec(v_cache_3919_);
                    v___x_3930_ = leanh::lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3938_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3931_ == 0 {
                    leanh::lean_ctor_set(v___x_3930_, 1, v_parserCache_3909_);
                    v___x_3933_ = v___x_3930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3937_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_tokenCache_3928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_parserCache_3909_);
                    v___x_3933_ = v_reuseFailAlloc_3937_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3927_ == 0 {
                    leanh::lean_ctor_set(v___x_3926_, 3, v___x_3933_);
                    v___x_3935_ = v___x_3926_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3936_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_stxStack_3920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_lhsPrec_3921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_pos_3922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 3, v___x_3933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_errorMsg_3923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 5, v_recoveredErrors_3924_);
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
    mut v_p_3945_: *mut leanh::LeanObject,
    mut v_a_3946_: *mut leanh::LeanObject,
    mut v_a_3947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3948_ = leanh::lean_alloc_closure(
        l_Lean_Parser_withResetCacheFn___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3948_, 0, v_p_3945_);
    v___x_3949_ = leanh::lean_unsigned_to_nat(0);
    v___x_3950_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(
        v___x_3949_,
        v___f_3948_,
        v_a_3946_,
        v_a_3947_,
    );
    return v___x_3950_;
}
pub unsafe fn l_Lean_Parser_withResetCache(
    mut v_p_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3952_ = leanh::lean_ctor_get(v_p_3951_, 0);
                v_fn_3953_ = leanh::lean_ctor_get(v_p_3951_, 1);
                v_isSharedCheck_3961_ = (!leanh::lean_is_exclusive(v_p_3951_)) as u8;
                if v_isSharedCheck_3961_ == 0 {
                    v___x_3955_ = v_p_3951_;
                    v_isShared_3956_ = v_isSharedCheck_3961_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fn_3953_);
                    leanh::lean_inc(v_info_3952_);
                    leanh::lean_dec(v_p_3951_);
                    v___x_3955_ = leanh::lean_box(0);
                    v_isShared_3956_ = v_isSharedCheck_3961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3957_ = leanh::lean_alloc_closure(
                    l_Lean_Parser_withResetCacheFn as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___x_3957_, 0, v_fn_3953_);
                if v_isShared_3956_ == 0 {
                    leanh::lean_ctor_set(v___x_3955_, 1, v___x_3957_);
                    v___x_3959_ = v___x_3955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_info_3952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3957_);
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
    mut v_f_3962_: *mut leanh::LeanObject,
    mut v_p_3963_: *mut leanh::LeanObject,
    mut v_c_3964_: *mut leanh::LeanObject,
    mut v_s_3965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3966_ = leanh::lean_apply_1(v_f_3962_, v_c_3964_);
    v___x_3967_ = leanh::lean_apply_2(v_p_3963_, v___x_3966_, v_s_3965_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_Parser_adaptUncacheableContextFn(
    mut v_f_3968_: *mut leanh::LeanObject,
    mut v_p_3969_: *mut leanh::LeanObject,
    mut v_a_3970_: *mut leanh::LeanObject,
    mut v_a_3971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3972_ = leanh::lean_alloc_closure(
        l_Lean_Parser_adaptUncacheableContextFn___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_3972_, 0, v_f_3968_);
    leanh::lean_closure_set(v___f_3972_, 1, v_p_3969_);
    v___x_3973_ = l_Lean_Parser_withResetCacheFn(v___f_3972_, v_a_3970_, v_a_3971_);
    return v___x_3973_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(
    mut v_a_3974_: *mut leanh::LeanObject,
    mut v_x_3975_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3976_: u8 = 0;
    let mut v_key_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3975_) == 0 {
                    v___x_3976_ = 0;
                    return v___x_3976_;
                } else {
                    v_key_3977_ = leanh::lean_ctor_get(v_x_3975_, 0);
                    v_tail_3978_ = leanh::lean_ctor_get(v_x_3975_, 2);
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
    mut v_a_3981_: *mut leanh::LeanObject,
    mut v_x_3982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3983_: u8 = 0;
    let mut v_r_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_3981_, v_x_3982_);
    leanh::lean_dec(v_x_3982_);
    leanh::lean_dec_ref(v_a_3981_);
    v_r_3984_ = leanh::lean_box((v_res_3983_) as usize);
    return v_r_3984_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_3985_: *mut leanh::LeanObject,
    mut v_x_3986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3992_: u8 = 0;
    let mut v_parserName_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u64 = 0;
    let mut v_hash_4018_: u64 = 0;
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3986_) == 0 {
                    return v_x_3985_;
                } else {
                    v_key_3987_ = leanh::lean_ctor_get(v_x_3986_, 0);
                    v_value_3988_ = leanh::lean_ctor_get(v_x_3986_, 1);
                    v_tail_3989_ = leanh::lean_ctor_get(v_x_3986_, 2);
                    v_isSharedCheck_4019_ = (!leanh::lean_is_exclusive(v_x_3986_)) as u8;
                    if v_isSharedCheck_4019_ == 0 {
                        v___x_3991_ = v_x_3986_;
                        v_isShared_3992_ = v_isSharedCheck_4019_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3989_);
                        leanh::lean_inc(v_value_3988_);
                        leanh::lean_inc(v_key_3987_);
                        leanh::lean_dec(v_x_3986_);
                        v___x_3991_ = leanh::lean_box(0);
                        v_isShared_3992_ = v_isSharedCheck_4019_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_parserName_3993_ = leanh::lean_ctor_get(v_key_3987_, 1);
                v_pos_3994_ = leanh::lean_ctor_get(v_key_3987_, 2);
                v___x_3995_ = lean_array_get_size(v_x_3985_);
                v___x_3996_ = l_String_instHashableRaw_hash(v_pos_3994_);
                if leanh::lean_obj_tag(v_parserName_3993_) == 0 {
                    v___x_4017_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_3998_ = v___x_4017_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4018_ = leanh::lean_ctor_get_uint64(
                        v_parserName_3993_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                leanh::lean_inc(v___x_4011_);
                if v_isShared_3992_ == 0 {
                    leanh::lean_ctor_set(v___x_3991_, 2, v___x_4011_);
                    v___x_4013_ = v___x_3991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4016_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_key_3987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_value_3988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 2, v___x_4011_);
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
    mut v_i_4020_: *mut leanh::LeanObject,
    mut v_source_4021_: *mut leanh::LeanObject,
    mut v_target_4022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: u8 = 0;
    let mut v_es_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4023_ = lean_array_get_size(v_source_4021_);
                v___x_4024_ = lean_nat_dec_lt(v_i_4020_, v___x_4023_);
                if v___x_4024_ == 0 {
                    leanh::lean_dec_ref(v_source_4021_);
                    leanh::lean_dec(v_i_4020_);
                    return v_target_4022_;
                } else {
                    v_es_4025_ = lean_array_fget(v_source_4021_, v_i_4020_);
                    v___x_4026_ = leanh::lean_box(0);
                    v_source_4027_ = lean_array_fset(v_source_4021_, v_i_4020_, v___x_4026_);
                    v_target_4028_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_4022_, v_es_4025_);
                    v___x_4029_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4030_ = lean_nat_add(v_i_4020_, v___x_4029_);
                    leanh::lean_dec(v_i_4020_);
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
    mut v_data_4032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4033_ = lean_array_get_size(v_data_4032_);
    v___x_4034_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4035_ = lean_nat_mul(v___x_4033_, v___x_4034_);
    v___x_4036_ = leanh::lean_unsigned_to_nat(0);
    v___x_4037_ = leanh::lean_box(0);
    v___x_4038_ = lean_mk_array(v_nbuckets_4035_, v___x_4037_);
    v___x_4039_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_4036_, v_data_4032_, v___x_4038_);
    return v___x_4039_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(
    mut v_a_4040_: *mut leanh::LeanObject,
    mut v_b_4041_: *mut leanh::LeanObject,
    mut v_x_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4042_) == 0 {
                    leanh::lean_dec(v_b_4041_);
                    leanh::lean_dec_ref(v_a_4040_);
                    return v_x_4042_;
                } else {
                    v_key_4043_ = leanh::lean_ctor_get(v_x_4042_, 0);
                    v_value_4044_ = leanh::lean_ctor_get(v_x_4042_, 1);
                    v_tail_4045_ = leanh::lean_ctor_get(v_x_4042_, 2);
                    v_isSharedCheck_4057_ = (!leanh::lean_is_exclusive(v_x_4042_)) as u8;
                    if v_isSharedCheck_4057_ == 0 {
                        v___x_4047_ = v_x_4042_;
                        v_isShared_4048_ = v_isSharedCheck_4057_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4045_);
                        leanh::lean_inc(v_value_4044_);
                        leanh::lean_inc(v_key_4043_);
                        leanh::lean_dec(v_x_4042_);
                        v___x_4047_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_4047_, 2, v___x_4050_);
                        v___x_4052_ = v___x_4047_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4053_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_key_4043_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_value_4044_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 2, v___x_4050_);
                        v___x_4052_ = v_reuseFailAlloc_4053_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_4044_);
                    leanh::lean_dec(v_key_4043_);
                    if v_isShared_4048_ == 0 {
                        leanh::lean_ctor_set(v___x_4047_, 1, v_b_4041_);
                        leanh::lean_ctor_set(v___x_4047_, 0, v_a_4040_);
                        v___x_4055_ = v___x_4047_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4056_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4040_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_b_4041_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_tail_4045_);
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
    mut v_m_4058_: *mut leanh::LeanObject,
    mut v_a_4059_: *mut leanh::LeanObject,
    mut v_b_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4065_: u8 = 0;
    let mut v_parserName_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v_val_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u64 = 0;
    let mut v_hash_4111_: u64 = 0;
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4061_ = leanh::lean_ctor_get(v_m_4058_, 0);
                v_buckets_4062_ = leanh::lean_ctor_get(v_m_4058_, 1);
                v_isSharedCheck_4112_ = (!leanh::lean_is_exclusive(v_m_4058_)) as u8;
                if v_isSharedCheck_4112_ == 0 {
                    v___x_4064_ = v_m_4058_;
                    v_isShared_4065_ = v_isSharedCheck_4112_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4062_);
                    leanh::lean_inc(v_size_4061_);
                    leanh::lean_dec(v_m_4058_);
                    v___x_4064_ = leanh::lean_box(0);
                    v_isShared_4065_ = v_isSharedCheck_4112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_parserName_4066_ = leanh::lean_ctor_get(v_a_4059_, 1);
                v_pos_4067_ = leanh::lean_ctor_get(v_a_4059_, 2);
                v___x_4068_ = lean_array_get_size(v_buckets_4062_);
                v___x_4069_ = l_String_instHashableRaw_hash(v_pos_4067_);
                if leanh::lean_obj_tag(v_parserName_4066_) == 0 {
                    v___x_4110_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4071_ = v___x_4110_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4111_ = leanh::lean_ctor_get_uint64(
                        v_parserName_4066_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    v___x_4086_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4087_ = lean_nat_add(v_size_4061_, v___x_4086_);
                    leanh::lean_dec(v_size_4061_);
                    leanh::lean_inc(v_bkt_4084_);
                    v___x_4088_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4088_, 0, v_a_4059_);
                    leanh::lean_ctor_set(v___x_4088_, 1, v_b_4060_);
                    leanh::lean_ctor_set(v___x_4088_, 2, v_bkt_4084_);
                    v_buckets_x27_4089_ =
                        lean_array_uset(v_buckets_4062_, v___x_4083_, v___x_4088_);
                    v___x_4090_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4091_ = lean_nat_mul(v_size_x27_4087_, v___x_4090_);
                    v___x_4092_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4093_ = lean_nat_div(v___x_4091_, v___x_4092_);
                    leanh::lean_dec(v___x_4091_);
                    v___x_4094_ = lean_array_get_size(v_buckets_x27_4089_);
                    v___x_4095_ = lean_nat_dec_le(v___x_4093_, v___x_4094_);
                    leanh::lean_dec(v___x_4093_);
                    if v___x_4095_ == 0 {
                        v_val_4096_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_4089_);
                        if v_isShared_4065_ == 0 {
                            leanh::lean_ctor_set(v___x_4064_, 1, v_val_4096_);
                            leanh::lean_ctor_set(v___x_4064_, 0, v_size_x27_4087_);
                            v___x_4098_ = v___x_4064_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4099_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4099_,
                                0,
                                v_size_x27_4087_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_4099_, 1, v_val_4096_);
                            v___x_4098_ = v_reuseFailAlloc_4099_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4065_ == 0 {
                            leanh::lean_ctor_set(v___x_4064_, 1, v_buckets_x27_4089_);
                            leanh::lean_ctor_set(v___x_4064_, 0, v_size_x27_4087_);
                            v___x_4101_ = v___x_4064_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4102_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4102_,
                                0,
                                v_size_x27_4087_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4102_,
                                1,
                                v_buckets_x27_4089_,
                            );
                            v___x_4101_ = v_reuseFailAlloc_4102_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_4084_);
                    v___x_4103_ = leanh::lean_box(0);
                    v_buckets_x27_4104_ =
                        lean_array_uset(v_buckets_4062_, v___x_4083_, v___x_4103_);
                    v___x_4105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_4059_, v_b_4060_, v_bkt_4084_);
                    v___x_4106_ = lean_array_uset(v_buckets_x27_4104_, v___x_4083_, v___x_4105_);
                    if v_isShared_4065_ == 0 {
                        leanh::lean_ctor_set(v___x_4064_, 1, v___x_4106_);
                        v___x_4108_ = v___x_4064_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4109_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_size_4061_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 1, v___x_4106_);
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
    mut v_a_4113_: *mut leanh::LeanObject,
    mut v_x_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4114_) == 0 {
                    v___x_4115_ = leanh::lean_box(0);
                    return v___x_4115_;
                } else {
                    v_key_4116_ = leanh::lean_ctor_get(v_x_4114_, 0);
                    v_value_4117_ = leanh::lean_ctor_get(v_x_4114_, 1);
                    v_tail_4118_ = leanh::lean_ctor_get(v_x_4114_, 2);
                    v___x_4119_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_4116_, v_a_4113_);
                    if v___x_4119_ == 0 {
                        v_x_4114_ = v_tail_4118_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4117_);
                        v___x_4121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4121_, 0, v_value_4117_);
                        return v___x_4121_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(
    mut v_a_4122_: *mut leanh::LeanObject,
    mut v_x_4123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_4122_, v_x_4123_);
    leanh::lean_dec(v_x_4123_);
    leanh::lean_dec_ref(v_a_4122_);
    return v_res_4124_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(
    mut v_m_4125_: *mut leanh::LeanObject,
    mut v_a_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserName_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: u64 = 0;
    let mut v_hash_4149_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4127_ = leanh::lean_ctor_get(v_m_4125_, 1);
                v_parserName_4128_ = leanh::lean_ctor_get(v_a_4126_, 1);
                v_pos_4129_ = leanh::lean_ctor_get(v_a_4126_, 2);
                v___x_4130_ = lean_array_get_size(v_buckets_4127_);
                v___x_4131_ = l_String_instHashableRaw_hash(v_pos_4129_);
                if leanh::lean_obj_tag(v_parserName_4128_) == 0 {
                    v___x_4148_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4133_ = v___x_4148_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4149_ = leanh::lean_ctor_get_uint64(
                        v_parserName_4128_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_m_4150_: *mut leanh::LeanObject,
    mut v_a_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_4150_, v_a_4151_);
    leanh::lean_dec_ref(v_a_4151_);
    leanh::lean_dec_ref(v_m_4150_);
    return v_res_4152_;
}
pub unsafe fn l_Lean_Parser_withCacheFn(
    mut v_parserName_4153_: *mut leanh::LeanObject,
    mut v_p_4154_: *mut leanh::LeanObject,
    mut v_c_4155_: *mut leanh::LeanObject,
    mut v_s_4156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCacheableParserContext_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v_parserCache_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newPos_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_raw_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initStackSz_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v_tokenCache_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parserCache_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4197_: u8 = 0;
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4207_: u8 = 0;
    let mut v_isSharedCheck_4208_: u8 = 0;
    let mut v_reuseFailAlloc_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut v_unused_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cache_4157_ = leanh::lean_ctor_get(v_s_4156_, 3);
                leanh::lean_inc_ref(v_cache_4157_);
                v_toCacheableParserContext_4158_ = leanh::lean_ctor_get(v_c_4155_, 2);
                v_stxStack_4159_ = leanh::lean_ctor_get(v_s_4156_, 0);
                v_pos_4160_ = leanh::lean_ctor_get(v_s_4156_, 2);
                v_recoveredErrors_4161_ = leanh::lean_ctor_get(v_s_4156_, 5);
                v_isSharedCheck_4210_ = (!leanh::lean_is_exclusive(v_s_4156_)) as u8;
                if v_isSharedCheck_4210_ == 0 {
                    v_unused_4211_ = leanh::lean_ctor_get(v_s_4156_, 4);
                    leanh::lean_dec(v_unused_4211_);
                    v_unused_4212_ = leanh::lean_ctor_get(v_s_4156_, 3);
                    leanh::lean_dec(v_unused_4212_);
                    v_unused_4213_ = leanh::lean_ctor_get(v_s_4156_, 1);
                    leanh::lean_dec(v_unused_4213_);
                    v___x_4163_ = v_s_4156_;
                    v_isShared_4164_ = v_isSharedCheck_4210_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_4161_);
                    leanh::lean_inc(v_pos_4160_);
                    leanh::lean_inc(v_stxStack_4159_);
                    leanh::lean_dec(v_s_4156_);
                    v___x_4163_ = leanh::lean_box(0);
                    v_isShared_4164_ = v_isSharedCheck_4210_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_parserCache_4165_ = leanh::lean_ctor_get(v_cache_4157_, 1);
                leanh::lean_inc(v_pos_4160_);
                leanh::lean_inc_ref(v_toCacheableParserContext_4158_);
                v_key_4166_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v_key_4166_, 0, v_toCacheableParserContext_4158_);
                leanh::lean_ctor_set(v_key_4166_, 1, v_parserName_4153_);
                leanh::lean_ctor_set(v_key_4166_, 2, v_pos_4160_);
                v___x_4167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_4165_, v_key_4166_);
                if leanh::lean_obj_tag(v___x_4167_) == 1 {
                    leanh::lean_dec_ref_known(v_key_4166_, 3);
                    leanh::lean_dec(v_pos_4160_);
                    leanh::lean_dec_ref(v_c_4155_);
                    leanh::lean_dec_ref(v_p_4154_);
                    v_val_4168_ = leanh::lean_ctor_get(v___x_4167_, 0);
                    leanh::lean_inc(v_val_4168_);
                    leanh::lean_dec_ref_known(v___x_4167_, 1);
                    v_stx_4169_ = leanh::lean_ctor_get(v_val_4168_, 0);
                    leanh::lean_inc(v_stx_4169_);
                    v_lhsPrec_4170_ = leanh::lean_ctor_get(v_val_4168_, 1);
                    leanh::lean_inc(v_lhsPrec_4170_);
                    v_newPos_4171_ = leanh::lean_ctor_get(v_val_4168_, 2);
                    leanh::lean_inc(v_newPos_4171_);
                    v_errorMsg_4172_ = leanh::lean_ctor_get(v_val_4168_, 3);
                    leanh::lean_inc(v_errorMsg_4172_);
                    leanh::lean_dec(v_val_4168_);
                    v___x_4173_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_4159_, v_stx_4169_);
                    if v_isShared_4164_ == 0 {
                        leanh::lean_ctor_set(v___x_4163_, 4, v_errorMsg_4172_);
                        leanh::lean_ctor_set(v___x_4163_, 2, v_newPos_4171_);
                        leanh::lean_ctor_set(v___x_4163_, 1, v_lhsPrec_4170_);
                        leanh::lean_ctor_set(v___x_4163_, 0, v___x_4173_);
                        v___x_4175_ = v___x_4163_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4176_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4176_, 1, v_lhsPrec_4170_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4176_, 2, v_newPos_4171_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4176_, 3, v_cache_4157_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4176_, 4, v_errorMsg_4172_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_4176_,
                            5,
                            v_recoveredErrors_4161_,
                        );
                        v___x_4175_ = v_reuseFailAlloc_4176_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4167_);
                    v_raw_4177_ = leanh::lean_ctor_get(v_stxStack_4159_, 0);
                    v_initStackSz_4178_ = lean_array_get_size(v_raw_4177_);
                    v___x_4179_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4180_ = leanh::lean_box(0);
                    if v_isShared_4164_ == 0 {
                        leanh::lean_ctor_set(v___x_4163_, 4, v___x_4180_);
                        leanh::lean_ctor_set(v___x_4163_, 1, v___x_4179_);
                        v___x_4182_ = v___x_4163_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4209_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_stxStack_4159_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 1, v___x_4179_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_pos_4160_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_cache_4157_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 4, v___x_4180_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_4209_,
                            5,
                            v_recoveredErrors_4161_,
                        );
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
                v_cache_4184_ = leanh::lean_ctor_get(v_s_4183_, 3);
                v_stxStack_4185_ = leanh::lean_ctor_get(v_s_4183_, 0);
                v_lhsPrec_4186_ = leanh::lean_ctor_get(v_s_4183_, 1);
                v_pos_4187_ = leanh::lean_ctor_get(v_s_4183_, 2);
                v_errorMsg_4188_ = leanh::lean_ctor_get(v_s_4183_, 4);
                v_recoveredErrors_4189_ = leanh::lean_ctor_get(v_s_4183_, 5);
                v_isSharedCheck_4208_ = (!leanh::lean_is_exclusive(v_s_4183_)) as u8;
                if v_isSharedCheck_4208_ == 0 {
                    v___x_4191_ = v_s_4183_;
                    v_isShared_4192_ = v_isSharedCheck_4208_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_recoveredErrors_4189_);
                    leanh::lean_inc(v_errorMsg_4188_);
                    leanh::lean_inc(v_cache_4184_);
                    leanh::lean_inc(v_pos_4187_);
                    leanh::lean_inc(v_lhsPrec_4186_);
                    leanh::lean_inc(v_stxStack_4185_);
                    leanh::lean_dec(v_s_4183_);
                    v___x_4191_ = leanh::lean_box(0);
                    v_isShared_4192_ = v_isSharedCheck_4208_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_tokenCache_4193_ = leanh::lean_ctor_get(v_cache_4184_, 0);
                v_parserCache_4194_ = leanh::lean_ctor_get(v_cache_4184_, 1);
                v_isSharedCheck_4207_ = (!leanh::lean_is_exclusive(v_cache_4184_)) as u8;
                if v_isSharedCheck_4207_ == 0 {
                    v___x_4196_ = v_cache_4184_;
                    v_isShared_4197_ = v_isSharedCheck_4207_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_parserCache_4194_);
                    leanh::lean_inc(v_tokenCache_4193_);
                    leanh::lean_dec(v_cache_4184_);
                    v___x_4196_ = leanh::lean_box(0);
                    v_isShared_4197_ = v_isSharedCheck_4207_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4198_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4185_);
                leanh::lean_inc(v_errorMsg_4188_);
                leanh::lean_inc(v_pos_4187_);
                leanh::lean_inc(v_lhsPrec_4186_);
                v___x_4199_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4199_, 0, v___x_4198_);
                leanh::lean_ctor_set(v___x_4199_, 1, v_lhsPrec_4186_);
                leanh::lean_ctor_set(v___x_4199_, 2, v_pos_4187_);
                leanh::lean_ctor_set(v___x_4199_, 3, v_errorMsg_4188_);
                v___x_4200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_4194_, v_key_4166_, v___x_4199_);
                if v_isShared_4197_ == 0 {
                    leanh::lean_ctor_set(v___x_4196_, 1, v___x_4200_);
                    v___x_4202_ = v___x_4196_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_tokenCache_4193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4206_, 1, v___x_4200_);
                    v___x_4202_ = v_reuseFailAlloc_4206_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4192_ == 0 {
                    leanh::lean_ctor_set(v___x_4191_, 3, v___x_4202_);
                    v___x_4204_ = v___x_4191_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4205_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_stxStack_4185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_lhsPrec_4186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 2, v_pos_4187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 3, v___x_4202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 4, v_errorMsg_4188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 5, v_recoveredErrors_4189_);
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
    mut v_00_u03b2_4214_: *mut leanh::LeanObject,
    mut v_m_4215_: *mut leanh::LeanObject,
    mut v_a_4216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_4215_, v_a_4216_);
    return v___x_4217_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(
    mut v_00_u03b2_4218_: *mut leanh::LeanObject,
    mut v_m_4219_: *mut leanh::LeanObject,
    mut v_a_4220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4221_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(
            v_00_u03b2_4218_,
            v_m_4219_,
            v_a_4220_,
        );
    leanh::lean_dec_ref(v_a_4220_);
    leanh::lean_dec_ref(v_m_4219_);
    return v_res_4221_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(
    mut v_00_u03b2_4222_: *mut leanh::LeanObject,
    mut v_m_4223_: *mut leanh::LeanObject,
    mut v_a_4224_: *mut leanh::LeanObject,
    mut v_b_4225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4226_ =
        l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(
            v_m_4223_, v_a_4224_, v_b_4225_,
        );
    return v___x_4226_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(
    mut v_00_u03b2_4227_: *mut leanh::LeanObject,
    mut v_a_4228_: *mut leanh::LeanObject,
    mut v_x_4229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_4228_, v_x_4229_);
    return v___x_4230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(
    mut v_00_u03b2_4231_: *mut leanh::LeanObject,
    mut v_a_4232_: *mut leanh::LeanObject,
    mut v_x_4233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_4231_, v_a_4232_, v_x_4233_);
    leanh::lean_dec(v_x_4233_);
    leanh::lean_dec_ref(v_a_4232_);
    return v_res_4234_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(
    mut v_00_u03b2_4235_: *mut leanh::LeanObject,
    mut v_a_4236_: *mut leanh::LeanObject,
    mut v_x_4237_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4238_: u8 = 0;
    v___x_4238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_4236_, v_x_4237_);
    return v___x_4238_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(
    mut v_00_u03b2_4239_: *mut leanh::LeanObject,
    mut v_a_4240_: *mut leanh::LeanObject,
    mut v_x_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4242_: u8 = 0;
    let mut v_r_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_4239_, v_a_4240_, v_x_4241_);
    leanh::lean_dec(v_x_4241_);
    leanh::lean_dec_ref(v_a_4240_);
    v_r_4243_ = leanh::lean_box((v_res_4242_) as usize);
    return v_r_4243_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(
    mut v_00_u03b2_4244_: *mut leanh::LeanObject,
    mut v_data_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4246_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_4245_);
    return v___x_4246_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(
    mut v_00_u03b2_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
    mut v_b_4249_: *mut leanh::LeanObject,
    mut v_x_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_4248_, v_b_4249_, v_x_4250_);
    return v___x_4251_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4252_: *mut leanh::LeanObject,
    mut v_i_4253_: *mut leanh::LeanObject,
    mut v_source_4254_: *mut leanh::LeanObject,
    mut v_target_4255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4256_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_4253_, v_source_4254_, v_target_4255_);
    return v___x_4256_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_4257_: *mut leanh::LeanObject,
    mut v_x_4258_: *mut leanh::LeanObject,
    mut v_x_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4260_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_4258_, v_x_4259_);
    return v___x_4260_;
}
pub unsafe fn l_Lean_Parser_withCache(
    mut v_parserName_4261_: *mut leanh::LeanObject,
    mut v_p_4262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4267_: u8 = 0;
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_4263_ = leanh::lean_ctor_get(v_p_4262_, 0);
                v_fn_4264_ = leanh::lean_ctor_get(v_p_4262_, 1);
                v_isSharedCheck_4272_ = (!leanh::lean_is_exclusive(v_p_4262_)) as u8;
                if v_isSharedCheck_4272_ == 0 {
                    v___x_4266_ = v_p_4262_;
                    v_isShared_4267_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fn_4264_);
                    leanh::lean_inc(v_info_4263_);
                    leanh::lean_dec(v_p_4262_);
                    v___x_4266_ = leanh::lean_box(0);
                    v_isShared_4267_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4268_ = leanh::lean_alloc_closure(
                    l_Lean_Parser_withCacheFn as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___x_4268_, 0, v_parserName_4261_);
                leanh::lean_closure_set(v___x_4268_, 1, v_fn_4264_);
                if v_isShared_4267_ == 0 {
                    leanh::lean_ctor_set(v___x_4266_, 1, v___x_4268_);
                    v___x_4270_ = v___x_4266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_info_4263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 1, v___x_4268_);
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
-> *mut leanh::LeanObject {
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4280_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1;
    v___x_4281_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2;
    v___x_4282_ = l_Lean_addBuiltinDocString(v___x_4280_, v___x_4281_);
    return v___x_4282_;
}
pub unsafe fn l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(
    mut v_a_4283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4284_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
    return v_res_4284_;
}
pub unsafe fn l_Lean_Parser_ParserFn_run(
    mut v_p_4289_: *mut leanh::LeanObject,
    mut v_ictx_4290_: *mut leanh::LeanObject,
    mut v_pmctx_4291_: *mut leanh::LeanObject,
    mut v_tokens_4292_: *mut leanh::LeanObject,
    mut v_s_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_Parser_ParserFn_run___closed__0;
    v___x_4295_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4295_, 0, v_ictx_4290_);
    leanh::lean_ctor_set(v___x_4295_, 1, v_pmctx_4291_);
    leanh::lean_ctor_set(v___x_4295_, 2, v___x_4294_);
    leanh::lean_ctor_set(v___x_4295_, 3, v_tokens_4292_);
    v___x_4296_ = leanh::lean_apply_2(v_p_4289_, v___x_4295_, v_s_4293_);
    return v___x_4296_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Trie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
    leanh::lean_mark_persistent(l_Lean_Parser_maxPrec);
    l_Lean_Parser_argPrec = _init_l_Lean_Parser_argPrec();
    leanh::lean_mark_persistent(l_Lean_Parser_argPrec);
    l_Lean_Parser_leadPrec = _init_l_Lean_Parser_leadPrec();
    leanh::lean_mark_persistent(l_Lean_Parser_leadPrec);
    l_Lean_Parser_minPrec = _init_l_Lean_Parser_minPrec();
    leanh::lean_mark_persistent(l_Lean_Parser_minPrec);
    l_Lean_Parser_instInhabitedInputContext = _init_l_Lean_Parser_instInhabitedInputContext();
    leanh::lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext);
    l_Lean_Parser_instInhabitedFirstTokens_default =
        _init_l_Lean_Parser_instInhabitedFirstTokens_default();
    leanh::lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens_default);
    l_Lean_Parser_instInhabitedFirstTokens = _init_l_Lean_Parser_instInhabitedFirstTokens();
    leanh::lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens);
    res = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_InputContext_endPos__valid___autoParam =
        _init_l_Lean_Parser_InputContext_endPos__valid___autoParam();
    leanh::lean_mark_persistent(l_Lean_Parser_InputContext_endPos__valid___autoParam);
    l_Lean_Parser_InputContext_mk___auto__1 = _init_l_Lean_Parser_InputContext_mk___auto__1();
    leanh::lean_mark_persistent(l_Lean_Parser_InputContext_mk___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Trie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Parser_Types(builtin);
}