// Lean compiler output
// Module: Std.Data.TreeMap.Basic
// Imports: Std.Data.DTreeMap.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::List::Control::l_List_forIn_x27_loop___redArg;
use crate::r#gen::Init::Data::Repr::{
    l_List_repr___redArg, l_Prod_repr___boxed, l_Repr_addAppParen,
    l_instReprTupleOfRepr___redArg___lam__0,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_mkAtom, l_Lean_replaceRef,
    l_String_toRawSubstring_x27, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Basic::{
    initialize_Std_Data_DTreeMap_Basic,
    l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg,
    runtime_initialize_Std_Data_DTreeMap_Basic,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_alter___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_beq___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_modify___redArg,
    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg,
    l_Std_DTreeMap_Internal_Impl_erase___redArg, l_Std_DTreeMap_Internal_Impl_filter___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_get___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getD___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___redArg, l_Std_DTreeMap_Internal_Impl_foldl___redArg,
    l_Std_DTreeMap_Internal_Impl_foldlM___redArg, l_Std_DTreeMap_Internal_Impl_foldrM___redArg,
    l_Std_DTreeMap_Internal_Impl_forInStep___redArg, l_Std_DTreeMap_Internal_Impl_getKey___redArg,
    l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyD___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg,
    l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg, l_Std_DTreeMap_Internal_Impl_maxKey___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg, l_Std_DTreeMap_Internal_Impl_minKey___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_minKeyD___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_TreeMap___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_TreeMap___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_TreeMap___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_TreeMap___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Std_TreeMap___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__3_value) as *mut LeanObject;
static l_Std_TreeMap___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeMap___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeMap___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeMap___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_TreeMap___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
static mut l_Std_TreeMap___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__6_value) as *mut LeanObject;
static l_Std_TreeMap___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeMap___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeMap___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeMap___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_TreeMap___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeMap___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Std_TreeMap___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__10_value) as *mut LeanObject;
static l_Std_TreeMap___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeMap___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__11_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeMap___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__11_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeMap___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__11_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__10_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Std_TreeMap___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap___auto__1___closed__14_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 109, 112, 97, 114, 101, 0],
};
static mut l_Std_TreeMap___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__14_value) as *mut LeanObject;
static mut l_Std_TreeMap___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap___auto__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__14_value) as *mut LeanObject,
        16710690322389477741 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__17_value) as *mut LeanObject;
static mut l_Std_TreeMap___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeMap___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap_term___x7em___00__closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_TreeMap_term___x7em___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__1_value: LeanStringObject<8> =
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
        m_data: [84, 114, 101, 101, 77, 97, 112, 0],
    };
static mut l_Std_TreeMap_term___x7em___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__1_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 126, 109, 95, 0],
    };
static mut l_Std_TreeMap_term___x7em___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__2_value) as *mut LeanObject;
static l_Std_TreeMap_term___x7em___00__closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__0_value) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Std_TreeMap_term___x7em___00__closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__1_value) as *mut LeanObject,
        16988956666274133190 as *mut LeanObject,
    ],
};
pub static l_Std_TreeMap_term___x7em___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__2_value) as *mut LeanObject,
        8130031363167941592 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_term___x7em___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__3_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__4_value: LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Std_TreeMap_term___x7em___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__4_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__4_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_term___x7em___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__5_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__6_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [32, 126, 109, 32, 0],
    };
static mut l_Std_TreeMap_term___x7em___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__6_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_term___x7em___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__7_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Std_TreeMap_term___x7em___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__8_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__8_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_term___x7em___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__9_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__9_value) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_term___x7em___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__10_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_term___x7em___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__11_value) as *mut LeanObject;
pub static l_Std_TreeMap_term___x7em___00__closed__12_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__3_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_term___x7em___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__12_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_term___x7em__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__12_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__1_value) as *mut LeanObject;
static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__1_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__3_value) as *mut LeanObject;
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__3_value) as *mut LeanObject,6049842283740396800 as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__5_value) as *mut LeanObject;
static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap_term___x7em___00__closed__1_value) as *mut LeanObject,16988956666274133190 as *mut LeanObject] };
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__3_value) as *mut LeanObject,1334357656782775489 as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__6_value) as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__9_value) as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__10_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeMap_getEntryGE_x21___redArg___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Std_TreeMap_getEntryGE_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_getEntryGE_x21___redArg___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
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
static mut l_Std_TreeMap_getEntryGE_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeMap_getEntryGE_x21___redArg___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
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
static mut l_Std_TreeMap_getEntryGE_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeMap_getEntryGE_x21___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_foldr___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_foldr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_foldr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_foldr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_foldr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_foldr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_foldr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_foldr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_foldr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_foldr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeMap_foldr___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_foldr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_foldr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeMap_partition___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_partition___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_partition___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_any___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_TreeMap_any___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_any___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_keys___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_keys___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_keys___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_keysArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_keysArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_keysArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_values___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_values___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_values___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_valuesArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_valuesArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_valuesArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_toList___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_toList___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_ofList___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_unitOfList___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap_toArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeMap_toArray___redArg___closed__1_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_TreeMap_toArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_toArray___redArg___closed__1_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_ofArray___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_unitOfArray___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap_instRepr___redArg___lam__1___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            83, 116, 100, 46, 84, 114, 101, 101, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32,
            0,
        ],
    };
static mut l_Std_TreeMap_instRepr___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instRepr___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instRepr___redArg___lam__1___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeMap_instRepr___redArg___lam__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_TreeMap_instRepr___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instRepr___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    v___x_2598_ = l_Std_TreeMap___auto__1___closed__10;
    v___x_2599_ = l_Lean_mkAtom(v___x_2598_);
    return v___x_2599_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    v___x_2600_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__12_once),
        _init_l_Std_TreeMap___auto__1___closed__12,
    );
    v___x_2601_ = l_Std_TreeMap___auto__1___closed__5;
    v___x_2602_ = lean_array_push(v___x_2601_, v___x_2600_);
    return v___x_2602_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_TreeMap___auto__1___closed__14;
    v___x_2605_ = lean_string_utf8_byte_size(v___x_2604_);
    return v___x_2605_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    v___x_2606_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__15_once),
        _init_l_Std_TreeMap___auto__1___closed__15,
    );
    v___x_2607_ = lean_unsigned_to_nat(0);
    v___x_2608_ = l_Std_TreeMap___auto__1___closed__14;
    v___x_2609_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2609_, 0, v___x_2608_);
    lean_ctor_set(v___x_2609_, 1, v___x_2607_);
    lean_ctor_set(v___x_2609_, 2, v___x_2606_);
    return v___x_2609_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    v___x_2612_ = lean_box(0);
    v___x_2613_ = l_Std_TreeMap___auto__1___closed__17;
    v___x_2614_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__16_once),
        _init_l_Std_TreeMap___auto__1___closed__16,
    );
    v___x_2615_ = lean_box(2);
    v___x_2616_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_2616_, 0, v___x_2615_);
    lean_ctor_set(v___x_2616_, 1, v___x_2614_);
    lean_ctor_set(v___x_2616_, 2, v___x_2613_);
    lean_ctor_set(v___x_2616_, 3, v___x_2612_);
    return v___x_2616_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    v___x_2617_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__18_once),
        _init_l_Std_TreeMap___auto__1___closed__18,
    );
    v___x_2618_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__13_once),
        _init_l_Std_TreeMap___auto__1___closed__13,
    );
    v___x_2619_ = lean_array_push(v___x_2618_, v___x_2617_);
    return v___x_2619_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    v___x_2620_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__19_once),
        _init_l_Std_TreeMap___auto__1___closed__19,
    );
    v___x_2621_ = l_Std_TreeMap___auto__1___closed__11;
    v___x_2622_ = lean_box(2);
    v___x_2623_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2623_, 0, v___x_2622_);
    lean_ctor_set(v___x_2623_, 1, v___x_2621_);
    lean_ctor_set(v___x_2623_, 2, v___x_2620_);
    return v___x_2623_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    v___x_2624_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__20_once),
        _init_l_Std_TreeMap___auto__1___closed__20,
    );
    v___x_2625_ = l_Std_TreeMap___auto__1___closed__5;
    v___x_2626_ = lean_array_push(v___x_2625_, v___x_2624_);
    return v___x_2626_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    v___x_2627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__21_once),
        _init_l_Std_TreeMap___auto__1___closed__21,
    );
    v___x_2628_ = l_Std_TreeMap___auto__1___closed__9;
    v___x_2629_ = lean_box(2);
    v___x_2630_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2630_, 0, v___x_2629_);
    lean_ctor_set(v___x_2630_, 1, v___x_2628_);
    lean_ctor_set(v___x_2630_, 2, v___x_2627_);
    return v___x_2630_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    v___x_2631_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__22_once),
        _init_l_Std_TreeMap___auto__1___closed__22,
    );
    v___x_2632_ = l_Std_TreeMap___auto__1___closed__5;
    v___x_2633_ = lean_array_push(v___x_2632_, v___x_2631_);
    return v___x_2633_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    v___x_2634_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__23_once),
        _init_l_Std_TreeMap___auto__1___closed__23,
    );
    v___x_2635_ = l_Std_TreeMap___auto__1___closed__7;
    v___x_2636_ = lean_box(2);
    v___x_2637_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2637_, 0, v___x_2636_);
    lean_ctor_set(v___x_2637_, 1, v___x_2635_);
    lean_ctor_set(v___x_2637_, 2, v___x_2634_);
    return v___x_2637_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    v___x_2638_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__24_once),
        _init_l_Std_TreeMap___auto__1___closed__24,
    );
    v___x_2639_ = l_Std_TreeMap___auto__1___closed__5;
    v___x_2640_ = lean_array_push(v___x_2639_, v___x_2638_);
    return v___x_2640_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2641_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__25_once),
        _init_l_Std_TreeMap___auto__1___closed__25,
    );
    v___x_2642_ = l_Std_TreeMap___auto__1___closed__4;
    v___x_2643_ = lean_box(2);
    v___x_2644_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2644_, 0, v___x_2643_);
    lean_ctor_set(v___x_2644_, 1, v___x_2642_);
    lean_ctor_set(v___x_2644_, 2, v___x_2641_);
    return v___x_2644_;
}
pub unsafe fn _init_l_Std_TreeMap___auto__1() -> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    v___x_2645_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26_once),
        _init_l_Std_TreeMap___auto__1___closed__26,
    );
    return v___x_2645_;
}
pub unsafe fn l_Std_TreeMap_empty(
    mut v_00_u03b1_2646_: *mut LeanObject,
    mut v_00_u03b2_2647_: *mut LeanObject,
    mut v_cmp_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    v___x_2649_ = lean_box(1);
    return v___x_2649_;
}
pub unsafe fn l_Std_TreeMap_empty___boxed(
    mut v_00_u03b1_2650_: *mut LeanObject,
    mut v_00_u03b2_2651_: *mut LeanObject,
    mut v_cmp_2652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2653_: *mut LeanObject = core::ptr::null_mut();
    v_res_2653_ = l_Std_TreeMap_empty(v_00_u03b1_2650_, v_00_u03b2_2651_, v_cmp_2652_);
    lean_dec_ref(v_cmp_2652_);
    return v_res_2653_;
}
pub unsafe fn l_Std_TreeMap_instEmptyCollection(
    mut v_00_u03b1_2654_: *mut LeanObject,
    mut v_00_u03b2_2655_: *mut LeanObject,
    mut v_cmp_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    v___x_2657_ = lean_box(1);
    return v___x_2657_;
}
pub unsafe fn l_Std_TreeMap_instEmptyCollection___boxed(
    mut v_00_u03b1_2658_: *mut LeanObject,
    mut v_00_u03b2_2659_: *mut LeanObject,
    mut v_cmp_2660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2661_: *mut LeanObject = core::ptr::null_mut();
    v_res_2661_ =
        l_Std_TreeMap_instEmptyCollection(v_00_u03b1_2658_, v_00_u03b2_2659_, v_cmp_2660_);
    lean_dec_ref(v_cmp_2660_);
    return v_res_2661_;
}
pub unsafe fn l_Std_TreeMap_instInhabited(
    mut v_00_u03b1_2662_: *mut LeanObject,
    mut v_00_u03b2_2663_: *mut LeanObject,
    mut v_cmp_2664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    v___x_2665_ = lean_box(1);
    return v___x_2665_;
}
pub unsafe fn l_Std_TreeMap_instInhabited___boxed(
    mut v_00_u03b1_2666_: *mut LeanObject,
    mut v_00_u03b2_2667_: *mut LeanObject,
    mut v_cmp_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Std_TreeMap_instInhabited(v_00_u03b1_2666_, v_00_u03b2_2667_, v_cmp_2668_);
    lean_dec_ref(v_cmp_2668_);
    return v_res_2669_;
}
pub unsafe fn _init_l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__4()
-> *mut LeanObject {
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    v___x_2707_ = l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__3;
    v___x_2708_ = l_String_toRawSubstring_x27(v___x_2707_);
    return v___x_2708_;
}
pub unsafe fn l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1(
    mut v_x_2726_: *mut LeanObject,
    mut v_a_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: u8 = 0;
    v___x_2729_ = l_Std_TreeMap_term___x7em___00__closed__3;
    lean_inc(v_x_2726_);
    v___x_2730_ = l_Lean_Syntax_isOfKind(v_x_2726_, v___x_2729_);
    if v___x_2730_ == 0 {
        let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2726_);
        v___x_2731_ = lean_box(1);
        v___x_2732_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2732_, 0, v___x_2731_);
        lean_ctor_set(v___x_2732_, 1, v_a_2728_);
        return v___x_2732_;
    } else {
        let mut v_quotContext_2733_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2734_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2740_: u8 = 0;
        let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2733_ = lean_ctor_get(v_a_2727_, 1);
        v_currMacroScope_2734_ = lean_ctor_get(v_a_2727_, 2);
        v_ref_2735_ = lean_ctor_get(v_a_2727_, 5);
        v___x_2736_ = lean_unsigned_to_nat(0);
        v___x_2737_ = l_Lean_Syntax_getArg(v_x_2726_, v___x_2736_);
        v___x_2738_ = lean_unsigned_to_nat(2);
        v___x_2739_ = l_Lean_Syntax_getArg(v_x_2726_, v___x_2738_);
        lean_dec(v_x_2726_);
        v___x_2740_ = 0;
        v___x_2741_ = l_Lean_SourceInfo_fromRef(v_ref_2735_, v___x_2740_);
        v___x_2742_ = l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2;
        v___x_2743_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__4), core::ptr::addr_of_mut!(l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__4_once), _init_l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__4);
        v___x_2744_ = l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__5;
        lean_inc(v_currMacroScope_2734_);
        lean_inc(v_quotContext_2733_);
        v___x_2745_ =
            l_Lean_addMacroScope(v_quotContext_2733_, v___x_2744_, v_currMacroScope_2734_);
        v___x_2746_ = l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__10;
        lean_inc_n(v___x_2741_, 2);
        v___x_2747_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2747_, 0, v___x_2741_);
        lean_ctor_set(v___x_2747_, 1, v___x_2743_);
        lean_ctor_set(v___x_2747_, 2, v___x_2745_);
        lean_ctor_set(v___x_2747_, 3, v___x_2746_);
        v___x_2748_ = l_Std_TreeMap___auto__1___closed__9;
        v___x_2749_ = l_Lean_Syntax_node2(v___x_2741_, v___x_2748_, v___x_2737_, v___x_2739_);
        v___x_2750_ = l_Lean_Syntax_node2(v___x_2741_, v___x_2742_, v___x_2747_, v___x_2749_);
        v___x_2751_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2751_, 0, v___x_2750_);
        lean_ctor_set(v___x_2751_, 1, v_a_2728_);
        return v___x_2751_;
    }
}
pub unsafe fn l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___boxed(
    mut v_x_2752_: *mut LeanObject,
    mut v_a_2753_: *mut LeanObject,
    mut v_a_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2755_: *mut LeanObject = core::ptr::null_mut();
    v_res_2755_ = l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1(v_x_2752_, v_a_2753_, v_a_2754_);
    lean_dec_ref(v_a_2753_);
    return v_res_2755_;
}
pub unsafe fn l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1(
    mut v_x_2759_: *mut LeanObject,
    mut v_a_2760_: *mut LeanObject,
    mut v_a_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    v___x_2762_ = l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______macroRules__Std__TreeMap__term___x7em____1___closed__2;
    lean_inc(v_x_2759_);
    v___x_2763_ = l_Lean_Syntax_isOfKind(v_x_2759_, v___x_2762_);
    if v___x_2763_ == 0 {
        let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2759_);
        v___x_2764_ = lean_box(0);
        v___x_2765_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2765_, 0, v___x_2764_);
        lean_ctor_set(v___x_2765_, 1, v_a_2761_);
        return v___x_2765_;
    } else {
        let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2769_: u8 = 0;
        v___x_2766_ = lean_unsigned_to_nat(0);
        v___x_2767_ = l_Lean_Syntax_getArg(v_x_2759_, v___x_2766_);
        v___x_2768_ = l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___closed__1;
        lean_inc(v___x_2767_);
        v___x_2769_ = l_Lean_Syntax_isOfKind(v___x_2767_, v___x_2768_);
        if v___x_2769_ == 0 {
            let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2767_);
            lean_dec(v_x_2759_);
            v___x_2770_ = lean_box(0);
            v___x_2771_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2771_, 0, v___x_2770_);
            lean_ctor_set(v___x_2771_, 1, v_a_2761_);
            return v___x_2771_;
        } else {
            let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2775_: u8 = 0;
            v___x_2772_ = lean_unsigned_to_nat(1);
            v___x_2773_ = l_Lean_Syntax_getArg(v_x_2759_, v___x_2772_);
            lean_dec(v_x_2759_);
            v___x_2774_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_2773_);
            v___x_2775_ = l_Lean_Syntax_matchesNull(v___x_2773_, v___x_2774_);
            if v___x_2775_ == 0 {
                let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2773_);
                lean_dec(v___x_2767_);
                v___x_2776_ = lean_box(0);
                v___x_2777_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2777_, 0, v___x_2776_);
                lean_ctor_set(v___x_2777_, 1, v_a_2761_);
                return v___x_2777_;
            } else {
                let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_2780_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2781_: u8 = 0;
                let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
                v___x_2778_ = l_Lean_Syntax_getArg(v___x_2773_, v___x_2766_);
                v___x_2779_ = l_Lean_Syntax_getArg(v___x_2773_, v___x_2772_);
                lean_dec(v___x_2773_);
                v_ref_2780_ = l_Lean_replaceRef(v___x_2767_, v_a_2760_);
                lean_dec(v___x_2767_);
                v___x_2781_ = 0;
                v___x_2782_ = l_Lean_SourceInfo_fromRef(v_ref_2780_, v___x_2781_);
                lean_dec(v_ref_2780_);
                v___x_2783_ = l_Std_TreeMap_term___x7em___00__closed__3;
                v___x_2784_ = l_Std_TreeMap_term___x7em___00__closed__6;
                lean_inc(v___x_2782_);
                v___x_2785_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2785_, 0, v___x_2782_);
                lean_ctor_set(v___x_2785_, 1, v___x_2784_);
                v___x_2786_ = l_Lean_Syntax_node3(
                    v___x_2782_,
                    v___x_2783_,
                    v___x_2778_,
                    v___x_2785_,
                    v___x_2779_,
                );
                v___x_2787_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2787_, 0, v___x_2786_);
                lean_ctor_set(v___x_2787_, 1, v_a_2761_);
                return v___x_2787_;
            }
        }
    }
}
pub unsafe fn l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1___boxed(
    mut v_x_2788_: *mut LeanObject,
    mut v_a_2789_: *mut LeanObject,
    mut v_a_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2791_: *mut LeanObject = core::ptr::null_mut();
    v_res_2791_ =
        l_Std_TreeMap___aux__Std__Data__TreeMap__Basic______unexpand__Std__TreeMap__Equiv__1(
            v_x_2788_, v_a_2789_, v_a_2790_,
        );
    lean_dec(v_a_2789_);
    return v_res_2791_;
}
pub unsafe fn l_Std_TreeMap_insert___redArg(
    mut v_cmp_2792_: *mut LeanObject,
    mut v_l_2793_: *mut LeanObject,
    mut v_a_2794_: *mut LeanObject,
    mut v_b_2795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    v___x_2796_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2792_, v_a_2794_, v_b_2795_, v_l_2793_);
    return v___x_2796_;
}
pub unsafe fn l_Std_TreeMap_insert(
    mut v_00_u03b1_2797_: *mut LeanObject,
    mut v_00_u03b2_2798_: *mut LeanObject,
    mut v_cmp_2799_: *mut LeanObject,
    mut v_l_2800_: *mut LeanObject,
    mut v_a_2801_: *mut LeanObject,
    mut v_b_2802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    v___x_2803_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2799_, v_a_2801_, v_b_2802_, v_l_2800_);
    return v___x_2803_;
}
pub unsafe fn l_Std_TreeMap_instSingletonProd___redArg___lam__0(
    mut v_cmp_2804_: *mut LeanObject,
    mut v_e_2805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2806_ = lean_ctor_get(v_e_2805_, 0);
    lean_inc(v_fst_2806_);
    v_snd_2807_ = lean_ctor_get(v_e_2805_, 1);
    lean_inc(v_snd_2807_);
    lean_dec_ref(v_e_2805_);
    v___x_2808_ = lean_box(1);
    v___x_2809_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_2804_,
        v_fst_2806_,
        v_snd_2807_,
        v___x_2808_,
    );
    return v___x_2809_;
}
pub unsafe fn l_Std_TreeMap_instSingletonProd___redArg(
    mut v_cmp_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2811_: *mut LeanObject = core::ptr::null_mut();
    v___f_2811_ = lean_alloc_closure(
        l_Std_TreeMap_instSingletonProd___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2811_, 0, v_cmp_2810_);
    return v___f_2811_;
}
pub unsafe fn l_Std_TreeMap_instSingletonProd(
    mut v_00_u03b1_2812_: *mut LeanObject,
    mut v_00_u03b2_2813_: *mut LeanObject,
    mut v_cmp_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2815_: *mut LeanObject = core::ptr::null_mut();
    v___f_2815_ = lean_alloc_closure(
        l_Std_TreeMap_instSingletonProd___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2815_, 0, v_cmp_2814_);
    return v___f_2815_;
}
pub unsafe fn l_Std_TreeMap_instInsertProd___redArg___lam__0(
    mut v_cmp_2816_: *mut LeanObject,
    mut v_e_2817_: *mut LeanObject,
    mut v_s_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2819_ = lean_ctor_get(v_e_2817_, 0);
    lean_inc(v_fst_2819_);
    v_snd_2820_ = lean_ctor_get(v_e_2817_, 1);
    lean_inc(v_snd_2820_);
    lean_dec_ref(v_e_2817_);
    v___x_2821_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_2816_,
        v_fst_2819_,
        v_snd_2820_,
        v_s_2818_,
    );
    return v___x_2821_;
}
pub unsafe fn l_Std_TreeMap_instInsertProd___redArg(
    mut v_cmp_2822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2823_: *mut LeanObject = core::ptr::null_mut();
    v___f_2823_ = lean_alloc_closure(
        l_Std_TreeMap_instInsertProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2823_, 0, v_cmp_2822_);
    return v___f_2823_;
}
pub unsafe fn l_Std_TreeMap_instInsertProd(
    mut v_00_u03b1_2824_: *mut LeanObject,
    mut v_00_u03b2_2825_: *mut LeanObject,
    mut v_cmp_2826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2827_: *mut LeanObject = core::ptr::null_mut();
    v___f_2827_ = lean_alloc_closure(
        l_Std_TreeMap_instInsertProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2827_, 0, v_cmp_2826_);
    return v___f_2827_;
}
pub unsafe fn l_Std_TreeMap_insertIfNew___redArg(
    mut v_cmp_2828_: *mut LeanObject,
    mut v_t_2829_: *mut LeanObject,
    mut v_a_2830_: *mut LeanObject,
    mut v_b_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2832_: u8 = 0;
    lean_inc(v_t_2829_);
    lean_inc(v_a_2830_);
    lean_inc_ref(v_cmp_2828_);
    v___x_2832_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2828_, v_a_2830_, v_t_2829_);
    if v___x_2832_ == 0 {
        let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
        v___x_2833_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2828_,
            v_a_2830_,
            v_b_2831_,
            v_t_2829_,
        );
        return v___x_2833_;
    } else {
        lean_dec(v_b_2831_);
        lean_dec(v_a_2830_);
        lean_dec_ref(v_cmp_2828_);
        return v_t_2829_;
    }
}
pub unsafe fn l_Std_TreeMap_insertIfNew(
    mut v_00_u03b1_2834_: *mut LeanObject,
    mut v_00_u03b2_2835_: *mut LeanObject,
    mut v_cmp_2836_: *mut LeanObject,
    mut v_t_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
    mut v_b_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2840_: u8 = 0;
    lean_inc(v_t_2837_);
    lean_inc(v_a_2838_);
    lean_inc_ref(v_cmp_2836_);
    v___x_2840_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2836_, v_a_2838_, v_t_2837_);
    if v___x_2840_ == 0 {
        let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
        v___x_2841_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2836_,
            v_a_2838_,
            v_b_2839_,
            v_t_2837_,
        );
        return v___x_2841_;
    } else {
        lean_dec(v_b_2839_);
        lean_dec(v_a_2838_);
        lean_dec_ref(v_cmp_2836_);
        return v_t_2837_;
    }
}
pub unsafe fn l_Std_TreeMap_containsThenInsert___redArg(
    mut v_cmp_2842_: *mut LeanObject,
    mut v_t_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_b_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: u8 = 0;
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2846_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_2843_);
                v_m_2847_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_2842_,
                    v_a_2844_,
                    v_b_2845_,
                    v_t_2843_,
                );
                if lean_obj_tag(v_m_2847_) == 0 {
                    v_size_2853_ = lean_ctor_get(v_m_2847_, 0);
                    lean_inc(v_size_2853_);
                    v___y_2849_ = v_size_2853_;
                    state = 1;
                    continue;
                } else {
                    v___x_2854_ = lean_unsigned_to_nat(0);
                    v___y_2849_ = v___x_2854_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2850_ = lean_nat_dec_eq(v_sz_2846_, v___y_2849_);
                lean_dec(v___y_2849_);
                lean_dec(v_sz_2846_);
                v___x_2851_ = lean_box((v___x_2850_) as usize);
                v___x_2852_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2852_, 0, v___x_2851_);
                lean_ctor_set(v___x_2852_, 1, v_m_2847_);
                return v___x_2852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_containsThenInsert(
    mut v_00_u03b1_2855_: *mut LeanObject,
    mut v_00_u03b2_2856_: *mut LeanObject,
    mut v_cmp_2857_: *mut LeanObject,
    mut v_t_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_b_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2861_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_2858_);
                v_m_2862_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_2857_,
                    v_a_2859_,
                    v_b_2860_,
                    v_t_2858_,
                );
                if lean_obj_tag(v_m_2862_) == 0 {
                    v_size_2868_ = lean_ctor_get(v_m_2862_, 0);
                    lean_inc(v_size_2868_);
                    v___y_2864_ = v_size_2868_;
                    state = 1;
                    continue;
                } else {
                    v___x_2869_ = lean_unsigned_to_nat(0);
                    v___y_2864_ = v___x_2869_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2865_ = lean_nat_dec_eq(v_sz_2861_, v___y_2864_);
                lean_dec(v___y_2864_);
                lean_dec(v_sz_2861_);
                v___x_2866_ = lean_box((v___x_2865_) as usize);
                v___x_2867_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2867_, 0, v___x_2866_);
                lean_ctor_set(v___x_2867_, 1, v_m_2862_);
                return v___x_2867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_containsThenInsertIfNew___redArg(
    mut v_cmp_2870_: *mut LeanObject,
    mut v_t_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_b_2873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2874_: u8 = 0;
    lean_inc(v_t_2871_);
    lean_inc(v_a_2872_);
    lean_inc_ref(v_cmp_2870_);
    v___x_2874_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2870_, v_a_2872_, v_t_2871_);
    if v___x_2874_ == 0 {
        let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
        v___x_2875_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2870_,
            v_a_2872_,
            v_b_2873_,
            v_t_2871_,
        );
        v___x_2876_ = lean_box((v___x_2874_) as usize);
        v___x_2877_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2877_, 0, v___x_2876_);
        lean_ctor_set(v___x_2877_, 1, v___x_2875_);
        return v___x_2877_;
    } else {
        let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_b_2873_);
        lean_dec(v_a_2872_);
        lean_dec_ref(v_cmp_2870_);
        v___x_2878_ = lean_box((v___x_2874_) as usize);
        v___x_2879_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2879_, 0, v___x_2878_);
        lean_ctor_set(v___x_2879_, 1, v_t_2871_);
        return v___x_2879_;
    }
}
pub unsafe fn l_Std_TreeMap_containsThenInsertIfNew(
    mut v_00_u03b1_2880_: *mut LeanObject,
    mut v_00_u03b2_2881_: *mut LeanObject,
    mut v_cmp_2882_: *mut LeanObject,
    mut v_t_2883_: *mut LeanObject,
    mut v_a_2884_: *mut LeanObject,
    mut v_b_2885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2886_: u8 = 0;
    lean_inc(v_t_2883_);
    lean_inc(v_a_2884_);
    lean_inc_ref(v_cmp_2882_);
    v___x_2886_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2882_, v_a_2884_, v_t_2883_);
    if v___x_2886_ == 0 {
        let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
        v___x_2887_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2882_,
            v_a_2884_,
            v_b_2885_,
            v_t_2883_,
        );
        v___x_2888_ = lean_box((v___x_2886_) as usize);
        v___x_2889_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2889_, 0, v___x_2888_);
        lean_ctor_set(v___x_2889_, 1, v___x_2887_);
        return v___x_2889_;
    } else {
        let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_b_2885_);
        lean_dec(v_a_2884_);
        lean_dec_ref(v_cmp_2882_);
        v___x_2890_ = lean_box((v___x_2886_) as usize);
        v___x_2891_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2891_, 0, v___x_2890_);
        lean_ctor_set(v___x_2891_, 1, v_t_2883_);
        return v___x_2891_;
    }
}
pub unsafe fn l_Std_TreeMap_getThenInsertIfNew_x3f___redArg(
    mut v_cmp_2892_: *mut LeanObject,
    mut v_t_2893_: *mut LeanObject,
    mut v_a_2894_: *mut LeanObject,
    mut v_b_2895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2894_);
    lean_inc(v_t_2893_);
    lean_inc_ref(v_cmp_2892_);
    v___x_2896_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2892_, v_t_2893_, v_a_2894_);
    if lean_obj_tag(v___x_2896_) == 0 {
        let mut v___x_2897_: u8 = 0;
        lean_inc(v_t_2893_);
        lean_inc(v_a_2894_);
        lean_inc_ref(v_cmp_2892_);
        v___x_2897_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2892_, v_a_2894_, v_t_2893_);
        if v___x_2897_ == 0 {
            let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
            v___x_2898_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_2892_,
                v_a_2894_,
                v_b_2895_,
                v_t_2893_,
            );
            v___x_2899_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2899_, 0, v___x_2896_);
            lean_ctor_set(v___x_2899_, 1, v___x_2898_);
            return v___x_2899_;
        } else {
            let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_b_2895_);
            lean_dec(v_a_2894_);
            lean_dec_ref(v_cmp_2892_);
            v___x_2900_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2900_, 0, v___x_2896_);
            lean_ctor_set(v___x_2900_, 1, v_t_2893_);
            return v___x_2900_;
        }
    } else {
        let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_b_2895_);
        lean_dec(v_a_2894_);
        lean_dec_ref(v_cmp_2892_);
        v___x_2901_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2901_, 0, v___x_2896_);
        lean_ctor_set(v___x_2901_, 1, v_t_2893_);
        return v___x_2901_;
    }
}
pub unsafe fn l_Std_TreeMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2902_: *mut LeanObject,
    mut v_00_u03b2_2903_: *mut LeanObject,
    mut v_cmp_2904_: *mut LeanObject,
    mut v_t_2905_: *mut LeanObject,
    mut v_a_2906_: *mut LeanObject,
    mut v_b_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2906_);
    lean_inc(v_t_2905_);
    lean_inc_ref(v_cmp_2904_);
    v___x_2908_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2904_, v_t_2905_, v_a_2906_);
    if lean_obj_tag(v___x_2908_) == 0 {
        let mut v___x_2909_: u8 = 0;
        lean_inc(v_t_2905_);
        lean_inc(v_a_2906_);
        lean_inc_ref(v_cmp_2904_);
        v___x_2909_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2904_, v_a_2906_, v_t_2905_);
        if v___x_2909_ == 0 {
            let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
            v___x_2910_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_2904_,
                v_a_2906_,
                v_b_2907_,
                v_t_2905_,
            );
            v___x_2911_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2911_, 0, v___x_2908_);
            lean_ctor_set(v___x_2911_, 1, v___x_2910_);
            return v___x_2911_;
        } else {
            let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_b_2907_);
            lean_dec(v_a_2906_);
            lean_dec_ref(v_cmp_2904_);
            v___x_2912_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2912_, 0, v___x_2908_);
            lean_ctor_set(v___x_2912_, 1, v_t_2905_);
            return v___x_2912_;
        }
    } else {
        let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_b_2907_);
        lean_dec(v_a_2906_);
        lean_dec_ref(v_cmp_2904_);
        v___x_2913_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2913_, 0, v___x_2908_);
        lean_ctor_set(v___x_2913_, 1, v_t_2905_);
        return v___x_2913_;
    }
}
pub unsafe fn l_Std_TreeMap_contains___redArg(
    mut v_cmp_2914_: *mut LeanObject,
    mut v_l_2915_: *mut LeanObject,
    mut v_a_2916_: *mut LeanObject,
) -> u8 {
    let mut v___x_2917_: u8 = 0;
    v___x_2917_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2914_, v_a_2916_, v_l_2915_);
    return v___x_2917_;
}
pub unsafe fn l_Std_TreeMap_contains___redArg___boxed(
    mut v_cmp_2918_: *mut LeanObject,
    mut v_l_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2921_: u8 = 0;
    let mut v_r_2922_: *mut LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Std_TreeMap_contains___redArg(v_cmp_2918_, v_l_2919_, v_a_2920_);
    v_r_2922_ = lean_box((v_res_2921_) as usize);
    return v_r_2922_;
}
pub unsafe fn l_Std_TreeMap_contains(
    mut v_00_u03b1_2923_: *mut LeanObject,
    mut v_00_u03b2_2924_: *mut LeanObject,
    mut v_cmp_2925_: *mut LeanObject,
    mut v_l_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
) -> u8 {
    let mut v___x_2928_: u8 = 0;
    v___x_2928_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2925_, v_a_2927_, v_l_2926_);
    return v___x_2928_;
}
pub unsafe fn l_Std_TreeMap_contains___boxed(
    mut v_00_u03b1_2929_: *mut LeanObject,
    mut v_00_u03b2_2930_: *mut LeanObject,
    mut v_cmp_2931_: *mut LeanObject,
    mut v_l_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2934_: u8 = 0;
    let mut v_r_2935_: *mut LeanObject = core::ptr::null_mut();
    v_res_2934_ = l_Std_TreeMap_contains(
        v_00_u03b1_2929_,
        v_00_u03b2_2930_,
        v_cmp_2931_,
        v_l_2932_,
        v_a_2933_,
    );
    v_r_2935_ = lean_box((v_res_2934_) as usize);
    return v_r_2935_;
}
pub unsafe fn l_Std_TreeMap_instMembership(
    mut v_00_u03b1_2936_: *mut LeanObject,
    mut v_00_u03b2_2937_: *mut LeanObject,
    mut v_cmp_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    v___x_2939_ = lean_box(0);
    return v___x_2939_;
}
pub unsafe fn l_Std_TreeMap_instMembership___boxed(
    mut v_00_u03b1_2940_: *mut LeanObject,
    mut v_00_u03b2_2941_: *mut LeanObject,
    mut v_cmp_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2943_: *mut LeanObject = core::ptr::null_mut();
    v_res_2943_ = l_Std_TreeMap_instMembership(v_00_u03b1_2940_, v_00_u03b2_2941_, v_cmp_2942_);
    lean_dec_ref(v_cmp_2942_);
    return v_res_2943_;
}
pub unsafe fn l_Std_TreeMap_instDecidableMem___redArg(
    mut v_cmp_2944_: *mut LeanObject,
    mut v_m_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
) -> u8 {
    let mut v___x_2947_: u8 = 0;
    v___x_2947_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2944_, v_a_2946_, v_m_2945_);
    return v___x_2947_;
}
pub unsafe fn l_Std_TreeMap_instDecidableMem___redArg___boxed(
    mut v_cmp_2948_: *mut LeanObject,
    mut v_m_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2951_: u8 = 0;
    let mut v_r_2952_: *mut LeanObject = core::ptr::null_mut();
    v_res_2951_ = l_Std_TreeMap_instDecidableMem___redArg(v_cmp_2948_, v_m_2949_, v_a_2950_);
    v_r_2952_ = lean_box((v_res_2951_) as usize);
    return v_r_2952_;
}
pub unsafe fn l_Std_TreeMap_instDecidableMem(
    mut v_00_u03b1_2953_: *mut LeanObject,
    mut v_00_u03b2_2954_: *mut LeanObject,
    mut v_cmp_2955_: *mut LeanObject,
    mut v_m_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
) -> u8 {
    let mut v___x_2958_: u8 = 0;
    v___x_2958_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2955_, v_a_2957_, v_m_2956_);
    return v___x_2958_;
}
pub unsafe fn l_Std_TreeMap_instDecidableMem___boxed(
    mut v_00_u03b1_2959_: *mut LeanObject,
    mut v_00_u03b2_2960_: *mut LeanObject,
    mut v_cmp_2961_: *mut LeanObject,
    mut v_m_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2964_: u8 = 0;
    let mut v_r_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2964_ = l_Std_TreeMap_instDecidableMem(
        v_00_u03b1_2959_,
        v_00_u03b2_2960_,
        v_cmp_2961_,
        v_m_2962_,
        v_a_2963_,
    );
    v_r_2965_ = lean_box((v_res_2964_) as usize);
    return v_r_2965_;
}
pub unsafe fn l_Std_TreeMap_size___redArg(mut v_t_2966_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_t_2966_) == 0 {
        let mut v_size_2967_: *mut LeanObject = core::ptr::null_mut();
        v_size_2967_ = lean_ctor_get(v_t_2966_, 0);
        lean_inc(v_size_2967_);
        return v_size_2967_;
    } else {
        let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
        v___x_2968_ = lean_unsigned_to_nat(0);
        return v___x_2968_;
    }
}
pub unsafe fn l_Std_TreeMap_size___redArg___boxed(
    mut v_t_2969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2970_: *mut LeanObject = core::ptr::null_mut();
    v_res_2970_ = l_Std_TreeMap_size___redArg(v_t_2969_);
    lean_dec(v_t_2969_);
    return v_res_2970_;
}
pub unsafe fn l_Std_TreeMap_size(
    mut v_00_u03b1_2971_: *mut LeanObject,
    mut v_00_u03b2_2972_: *mut LeanObject,
    mut v_cmp_2973_: *mut LeanObject,
    mut v_t_2974_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_2974_) == 0 {
        let mut v_size_2975_: *mut LeanObject = core::ptr::null_mut();
        v_size_2975_ = lean_ctor_get(v_t_2974_, 0);
        lean_inc(v_size_2975_);
        return v_size_2975_;
    } else {
        let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
        v___x_2976_ = lean_unsigned_to_nat(0);
        return v___x_2976_;
    }
}
pub unsafe fn l_Std_TreeMap_size___boxed(
    mut v_00_u03b1_2977_: *mut LeanObject,
    mut v_00_u03b2_2978_: *mut LeanObject,
    mut v_cmp_2979_: *mut LeanObject,
    mut v_t_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2981_: *mut LeanObject = core::ptr::null_mut();
    v_res_2981_ = l_Std_TreeMap_size(v_00_u03b1_2977_, v_00_u03b2_2978_, v_cmp_2979_, v_t_2980_);
    lean_dec(v_t_2980_);
    lean_dec_ref(v_cmp_2979_);
    return v_res_2981_;
}
pub unsafe fn l_Std_TreeMap_isEmpty___redArg(mut v_t_2982_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_t_2982_) == 0 {
        let mut v___x_2983_: u8 = 0;
        v___x_2983_ = 0;
        return v___x_2983_;
    } else {
        let mut v___x_2984_: u8 = 0;
        v___x_2984_ = 1;
        return v___x_2984_;
    }
}
pub unsafe fn l_Std_TreeMap_isEmpty___redArg___boxed(
    mut v_t_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2986_: u8 = 0;
    let mut v_r_2987_: *mut LeanObject = core::ptr::null_mut();
    v_res_2986_ = l_Std_TreeMap_isEmpty___redArg(v_t_2985_);
    lean_dec(v_t_2985_);
    v_r_2987_ = lean_box((v_res_2986_) as usize);
    return v_r_2987_;
}
pub unsafe fn l_Std_TreeMap_isEmpty(
    mut v_00_u03b1_2988_: *mut LeanObject,
    mut v_00_u03b2_2989_: *mut LeanObject,
    mut v_cmp_2990_: *mut LeanObject,
    mut v_t_2991_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_t_2991_) == 0 {
        let mut v___x_2992_: u8 = 0;
        v___x_2992_ = 0;
        return v___x_2992_;
    } else {
        let mut v___x_2993_: u8 = 0;
        v___x_2993_ = 1;
        return v___x_2993_;
    }
}
pub unsafe fn l_Std_TreeMap_isEmpty___boxed(
    mut v_00_u03b1_2994_: *mut LeanObject,
    mut v_00_u03b2_2995_: *mut LeanObject,
    mut v_cmp_2996_: *mut LeanObject,
    mut v_t_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2998_: u8 = 0;
    let mut v_r_2999_: *mut LeanObject = core::ptr::null_mut();
    v_res_2998_ = l_Std_TreeMap_isEmpty(v_00_u03b1_2994_, v_00_u03b2_2995_, v_cmp_2996_, v_t_2997_);
    lean_dec(v_t_2997_);
    lean_dec_ref(v_cmp_2996_);
    v_r_2999_ = lean_box((v_res_2998_) as usize);
    return v_r_2999_;
}
pub unsafe fn l_Std_TreeMap_erase___redArg(
    mut v_cmp_3000_: *mut LeanObject,
    mut v_t_3001_: *mut LeanObject,
    mut v_a_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    v___x_3003_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3000_, v_a_3002_, v_t_3001_);
    return v___x_3003_;
}
pub unsafe fn l_Std_TreeMap_erase(
    mut v_00_u03b1_3004_: *mut LeanObject,
    mut v_00_u03b2_3005_: *mut LeanObject,
    mut v_cmp_3006_: *mut LeanObject,
    mut v_t_3007_: *mut LeanObject,
    mut v_a_3008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    v___x_3009_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3006_, v_a_3008_, v_t_3007_);
    return v___x_3009_;
}
pub unsafe fn l_Std_TreeMap_get_x3f___redArg(
    mut v_cmp_3010_: *mut LeanObject,
    mut v_t_3011_: *mut LeanObject,
    mut v_a_3012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    v___x_3013_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_3010_, v_t_3011_, v_a_3012_);
    return v___x_3013_;
}
pub unsafe fn l_Std_TreeMap_get_x3f(
    mut v_00_u03b1_3014_: *mut LeanObject,
    mut v_00_u03b2_3015_: *mut LeanObject,
    mut v_cmp_3016_: *mut LeanObject,
    mut v_t_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    v___x_3019_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_3016_, v_t_3017_, v_a_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Std_TreeMap_get___redArg(
    mut v_cmp_3020_: *mut LeanObject,
    mut v_t_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    v___x_3023_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_3020_, v_t_3021_, v_a_3022_);
    return v___x_3023_;
}
pub unsafe fn l_Std_TreeMap_get(
    mut v_00_u03b1_3024_: *mut LeanObject,
    mut v_00_u03b2_3025_: *mut LeanObject,
    mut v_cmp_3026_: *mut LeanObject,
    mut v_t_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
    mut v_h_3029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    v___x_3030_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_3026_, v_t_3027_, v_a_3028_);
    return v___x_3030_;
}
pub unsafe fn l_Std_TreeMap_get_x21___redArg(
    mut v_cmp_3031_: *mut LeanObject,
    mut v_inst_3032_: *mut LeanObject,
    mut v_t_3033_: *mut LeanObject,
    mut v_a_3034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    v___x_3035_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_3031_,
        v_inst_3032_,
        v_t_3033_,
        v_a_3034_,
    );
    return v___x_3035_;
}
pub unsafe fn l_Std_TreeMap_get_x21___redArg___boxed(
    mut v_cmp_3036_: *mut LeanObject,
    mut v_inst_3037_: *mut LeanObject,
    mut v_t_3038_: *mut LeanObject,
    mut v_a_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3040_: *mut LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Std_TreeMap_get_x21___redArg(v_cmp_3036_, v_inst_3037_, v_t_3038_, v_a_3039_);
    lean_dec(v_inst_3037_);
    return v_res_3040_;
}
pub unsafe fn l_Std_TreeMap_get_x21(
    mut v_00_u03b1_3041_: *mut LeanObject,
    mut v_00_u03b2_3042_: *mut LeanObject,
    mut v_cmp_3043_: *mut LeanObject,
    mut v_inst_3044_: *mut LeanObject,
    mut v_t_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    v___x_3047_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_3043_,
        v_inst_3044_,
        v_t_3045_,
        v_a_3046_,
    );
    return v___x_3047_;
}
pub unsafe fn l_Std_TreeMap_get_x21___boxed(
    mut v_00_u03b1_3048_: *mut LeanObject,
    mut v_00_u03b2_3049_: *mut LeanObject,
    mut v_cmp_3050_: *mut LeanObject,
    mut v_inst_3051_: *mut LeanObject,
    mut v_t_3052_: *mut LeanObject,
    mut v_a_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3054_: *mut LeanObject = core::ptr::null_mut();
    v_res_3054_ = l_Std_TreeMap_get_x21(
        v_00_u03b1_3048_,
        v_00_u03b2_3049_,
        v_cmp_3050_,
        v_inst_3051_,
        v_t_3052_,
        v_a_3053_,
    );
    lean_dec(v_inst_3051_);
    return v_res_3054_;
}
pub unsafe fn l_Std_TreeMap_getD___redArg(
    mut v_cmp_3055_: *mut LeanObject,
    mut v_t_3056_: *mut LeanObject,
    mut v_a_3057_: *mut LeanObject,
    mut v_fallback_3058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    v___x_3059_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_3055_,
        v_t_3056_,
        v_a_3057_,
        v_fallback_3058_,
    );
    return v___x_3059_;
}
pub unsafe fn l_Std_TreeMap_getD___redArg___boxed(
    mut v_cmp_3060_: *mut LeanObject,
    mut v_t_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_fallback_3063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3064_: *mut LeanObject = core::ptr::null_mut();
    v_res_3064_ = l_Std_TreeMap_getD___redArg(v_cmp_3060_, v_t_3061_, v_a_3062_, v_fallback_3063_);
    lean_dec(v_fallback_3063_);
    return v_res_3064_;
}
pub unsafe fn l_Std_TreeMap_getD(
    mut v_00_u03b1_3065_: *mut LeanObject,
    mut v_00_u03b2_3066_: *mut LeanObject,
    mut v_cmp_3067_: *mut LeanObject,
    mut v_t_3068_: *mut LeanObject,
    mut v_a_3069_: *mut LeanObject,
    mut v_fallback_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    v___x_3071_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_3067_,
        v_t_3068_,
        v_a_3069_,
        v_fallback_3070_,
    );
    return v___x_3071_;
}
pub unsafe fn l_Std_TreeMap_getD___boxed(
    mut v_00_u03b1_3072_: *mut LeanObject,
    mut v_00_u03b2_3073_: *mut LeanObject,
    mut v_cmp_3074_: *mut LeanObject,
    mut v_t_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
    mut v_fallback_3077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3078_: *mut LeanObject = core::ptr::null_mut();
    v_res_3078_ = l_Std_TreeMap_getD(
        v_00_u03b1_3072_,
        v_00_u03b2_3073_,
        v_cmp_3074_,
        v_t_3075_,
        v_a_3076_,
        v_fallback_3077_,
    );
    lean_dec(v_fallback_3077_);
    return v_res_3078_;
}
pub unsafe fn l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__0(
    mut v_cmp_3079_: *mut LeanObject,
    mut v_m_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_h_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    v___x_3083_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_3079_, v_m_3080_, v_a_3081_);
    return v___x_3083_;
}
pub unsafe fn l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__1(
    mut v_cmp_3084_: *mut LeanObject,
    mut v_m_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    v___x_3087_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_3084_, v_m_3085_, v_a_3086_);
    return v___x_3087_;
}
pub unsafe fn l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__2(
    mut v_cmp_3088_: *mut LeanObject,
    mut v_inst_3089_: *mut LeanObject,
    mut v_m_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    v___x_3092_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_3088_,
        v_inst_3089_,
        v_m_3090_,
        v_a_3091_,
    );
    return v___x_3092_;
}
pub unsafe fn l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__2___boxed(
    mut v_cmp_3093_: *mut LeanObject,
    mut v_inst_3094_: *mut LeanObject,
    mut v_m_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3097_: *mut LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__2(
        v_cmp_3093_,
        v_inst_3094_,
        v_m_3095_,
        v_a_3096_,
    );
    lean_dec(v_inst_3094_);
    return v_res_3097_;
}
pub unsafe fn l_Std_TreeMap_instGetElem_x3fMem___redArg(
    mut v_cmp_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_cmp_3098_, 2);
    v___f_3099_ = lean_alloc_closure(
        l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3099_, 0, v_cmp_3098_);
    v___f_3100_ = lean_alloc_closure(
        l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3100_, 0, v_cmp_3098_);
    v___f_3101_ = lean_alloc_closure(
        l_Std_TreeMap_instGetElem_x3fMem___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3101_, 0, v_cmp_3098_);
    v___x_3102_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3102_, 0, v___f_3099_);
    lean_ctor_set(v___x_3102_, 1, v___f_3100_);
    lean_ctor_set(v___x_3102_, 2, v___f_3101_);
    return v___x_3102_;
}
pub unsafe fn l_Std_TreeMap_instGetElem_x3fMem(
    mut v_00_u03b1_3103_: *mut LeanObject,
    mut v_00_u03b2_3104_: *mut LeanObject,
    mut v_cmp_3105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    v___x_3106_ = l_Std_TreeMap_instGetElem_x3fMem___redArg(v_cmp_3105_);
    return v___x_3106_;
}
pub unsafe fn l_Std_TreeMap_getKey_x3f___redArg(
    mut v_cmp_3107_: *mut LeanObject,
    mut v_t_3108_: *mut LeanObject,
    mut v_a_3109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    v___x_3110_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_3107_, v_t_3108_, v_a_3109_);
    return v___x_3110_;
}
pub unsafe fn l_Std_TreeMap_getKey_x3f(
    mut v_00_u03b1_3111_: *mut LeanObject,
    mut v_00_u03b2_3112_: *mut LeanObject,
    mut v_cmp_3113_: *mut LeanObject,
    mut v_t_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    v___x_3116_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_3113_, v_t_3114_, v_a_3115_);
    return v___x_3116_;
}
pub unsafe fn l_Std_TreeMap_getKey___redArg(
    mut v_cmp_3117_: *mut LeanObject,
    mut v_t_3118_: *mut LeanObject,
    mut v_a_3119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    v___x_3120_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_3117_, v_t_3118_, v_a_3119_);
    return v___x_3120_;
}
pub unsafe fn l_Std_TreeMap_getKey(
    mut v_00_u03b1_3121_: *mut LeanObject,
    mut v_00_u03b2_3122_: *mut LeanObject,
    mut v_cmp_3123_: *mut LeanObject,
    mut v_t_3124_: *mut LeanObject,
    mut v_a_3125_: *mut LeanObject,
    mut v_h_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    v___x_3127_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_3123_, v_t_3124_, v_a_3125_);
    return v___x_3127_;
}
pub unsafe fn l_Std_TreeMap_getKey_x21___redArg(
    mut v_cmp_3128_: *mut LeanObject,
    mut v_inst_3129_: *mut LeanObject,
    mut v_t_3130_: *mut LeanObject,
    mut v_a_3131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_3128_,
        v_t_3130_,
        v_a_3131_,
        v_inst_3129_,
    );
    return v___x_3132_;
}
pub unsafe fn l_Std_TreeMap_getKey_x21___redArg___boxed(
    mut v_cmp_3133_: *mut LeanObject,
    mut v_inst_3134_: *mut LeanObject,
    mut v_t_3135_: *mut LeanObject,
    mut v_a_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3137_: *mut LeanObject = core::ptr::null_mut();
    v_res_3137_ =
        l_Std_TreeMap_getKey_x21___redArg(v_cmp_3133_, v_inst_3134_, v_t_3135_, v_a_3136_);
    lean_dec(v_inst_3134_);
    return v_res_3137_;
}
pub unsafe fn l_Std_TreeMap_getKey_x21(
    mut v_00_u03b1_3138_: *mut LeanObject,
    mut v_00_u03b2_3139_: *mut LeanObject,
    mut v_cmp_3140_: *mut LeanObject,
    mut v_inst_3141_: *mut LeanObject,
    mut v_t_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    v___x_3144_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_3140_,
        v_t_3142_,
        v_a_3143_,
        v_inst_3141_,
    );
    return v___x_3144_;
}
pub unsafe fn l_Std_TreeMap_getKey_x21___boxed(
    mut v_00_u03b1_3145_: *mut LeanObject,
    mut v_00_u03b2_3146_: *mut LeanObject,
    mut v_cmp_3147_: *mut LeanObject,
    mut v_inst_3148_: *mut LeanObject,
    mut v_t_3149_: *mut LeanObject,
    mut v_a_3150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3151_: *mut LeanObject = core::ptr::null_mut();
    v_res_3151_ = l_Std_TreeMap_getKey_x21(
        v_00_u03b1_3145_,
        v_00_u03b2_3146_,
        v_cmp_3147_,
        v_inst_3148_,
        v_t_3149_,
        v_a_3150_,
    );
    lean_dec(v_inst_3148_);
    return v_res_3151_;
}
pub unsafe fn l_Std_TreeMap_getKeyD___redArg(
    mut v_cmp_3152_: *mut LeanObject,
    mut v_t_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
    mut v_fallback_3155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_3152_,
        v_t_3153_,
        v_a_3154_,
        v_fallback_3155_,
    );
    return v___x_3156_;
}
pub unsafe fn l_Std_TreeMap_getKeyD___redArg___boxed(
    mut v_cmp_3157_: *mut LeanObject,
    mut v_t_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_fallback_3160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3161_: *mut LeanObject = core::ptr::null_mut();
    v_res_3161_ =
        l_Std_TreeMap_getKeyD___redArg(v_cmp_3157_, v_t_3158_, v_a_3159_, v_fallback_3160_);
    lean_dec(v_fallback_3160_);
    return v_res_3161_;
}
pub unsafe fn l_Std_TreeMap_getKeyD(
    mut v_00_u03b1_3162_: *mut LeanObject,
    mut v_00_u03b2_3163_: *mut LeanObject,
    mut v_cmp_3164_: *mut LeanObject,
    mut v_t_3165_: *mut LeanObject,
    mut v_a_3166_: *mut LeanObject,
    mut v_fallback_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_3164_,
        v_t_3165_,
        v_a_3166_,
        v_fallback_3167_,
    );
    return v___x_3168_;
}
pub unsafe fn l_Std_TreeMap_getKeyD___boxed(
    mut v_00_u03b1_3169_: *mut LeanObject,
    mut v_00_u03b2_3170_: *mut LeanObject,
    mut v_cmp_3171_: *mut LeanObject,
    mut v_t_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
    mut v_fallback_3174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3175_: *mut LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_Std_TreeMap_getKeyD(
        v_00_u03b1_3169_,
        v_00_u03b2_3170_,
        v_cmp_3171_,
        v_t_3172_,
        v_a_3173_,
        v_fallback_3174_,
    );
    lean_dec(v_fallback_3174_);
    return v_res_3175_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x3f___redArg(
    mut v_t_3176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    v___x_3177_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_3176_);
    return v___x_3177_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x3f___redArg___boxed(
    mut v_t_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3179_: *mut LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_Std_TreeMap_minEntry_x3f___redArg(v_t_3178_);
    lean_dec(v_t_3178_);
    return v_res_3179_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x3f(
    mut v_00_u03b1_3180_: *mut LeanObject,
    mut v_00_u03b2_3181_: *mut LeanObject,
    mut v_cmp_3182_: *mut LeanObject,
    mut v_t_3183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    v___x_3184_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_3183_);
    return v___x_3184_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x3f___boxed(
    mut v_00_u03b1_3185_: *mut LeanObject,
    mut v_00_u03b2_3186_: *mut LeanObject,
    mut v_cmp_3187_: *mut LeanObject,
    mut v_t_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3189_: *mut LeanObject = core::ptr::null_mut();
    v_res_3189_ =
        l_Std_TreeMap_minEntry_x3f(v_00_u03b1_3185_, v_00_u03b2_3186_, v_cmp_3187_, v_t_3188_);
    lean_dec(v_t_3188_);
    lean_dec_ref(v_cmp_3187_);
    return v_res_3189_;
}
pub unsafe fn l_Std_TreeMap_minEntry___redArg(mut v_t_3190_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    v___x_3191_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_3190_);
    return v___x_3191_;
}
pub unsafe fn l_Std_TreeMap_minEntry___redArg___boxed(
    mut v_t_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3193_: *mut LeanObject = core::ptr::null_mut();
    v_res_3193_ = l_Std_TreeMap_minEntry___redArg(v_t_3192_);
    lean_dec(v_t_3192_);
    return v_res_3193_;
}
pub unsafe fn l_Std_TreeMap_minEntry(
    mut v_00_u03b1_3194_: *mut LeanObject,
    mut v_00_u03b2_3195_: *mut LeanObject,
    mut v_cmp_3196_: *mut LeanObject,
    mut v_t_3197_: *mut LeanObject,
    mut v_h_3198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    v___x_3199_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_3197_);
    return v___x_3199_;
}
pub unsafe fn l_Std_TreeMap_minEntry___boxed(
    mut v_00_u03b1_3200_: *mut LeanObject,
    mut v_00_u03b2_3201_: *mut LeanObject,
    mut v_cmp_3202_: *mut LeanObject,
    mut v_t_3203_: *mut LeanObject,
    mut v_h_3204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3205_: *mut LeanObject = core::ptr::null_mut();
    v_res_3205_ = l_Std_TreeMap_minEntry(
        v_00_u03b1_3200_,
        v_00_u03b2_3201_,
        v_cmp_3202_,
        v_t_3203_,
        v_h_3204_,
    );
    lean_dec(v_t_3203_);
    lean_dec_ref(v_cmp_3202_);
    return v_res_3205_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x21___redArg(
    mut v_inst_3206_: *mut LeanObject,
    mut v_t_3207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    v___x_3208_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3206_, v_t_3207_);
    return v___x_3208_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x21___redArg___boxed(
    mut v_inst_3209_: *mut LeanObject,
    mut v_t_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3211_: *mut LeanObject = core::ptr::null_mut();
    v_res_3211_ = l_Std_TreeMap_minEntry_x21___redArg(v_inst_3209_, v_t_3210_);
    lean_dec(v_t_3210_);
    lean_dec_ref(v_inst_3209_);
    return v_res_3211_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x21(
    mut v_00_u03b1_3212_: *mut LeanObject,
    mut v_00_u03b2_3213_: *mut LeanObject,
    mut v_cmp_3214_: *mut LeanObject,
    mut v_inst_3215_: *mut LeanObject,
    mut v_t_3216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    v___x_3217_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3215_, v_t_3216_);
    return v___x_3217_;
}
pub unsafe fn l_Std_TreeMap_minEntry_x21___boxed(
    mut v_00_u03b1_3218_: *mut LeanObject,
    mut v_00_u03b2_3219_: *mut LeanObject,
    mut v_cmp_3220_: *mut LeanObject,
    mut v_inst_3221_: *mut LeanObject,
    mut v_t_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3223_: *mut LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Std_TreeMap_minEntry_x21(
        v_00_u03b1_3218_,
        v_00_u03b2_3219_,
        v_cmp_3220_,
        v_inst_3221_,
        v_t_3222_,
    );
    lean_dec(v_t_3222_);
    lean_dec_ref(v_inst_3221_);
    lean_dec_ref(v_cmp_3220_);
    return v_res_3223_;
}
pub unsafe fn l_Std_TreeMap_minEntryD___redArg(
    mut v_t_3224_: *mut LeanObject,
    mut v_fallback_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    v___x_3226_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_3224_, v_fallback_3225_);
    return v___x_3226_;
}
pub unsafe fn l_Std_TreeMap_minEntryD___redArg___boxed(
    mut v_t_3227_: *mut LeanObject,
    mut v_fallback_3228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3229_: *mut LeanObject = core::ptr::null_mut();
    v_res_3229_ = l_Std_TreeMap_minEntryD___redArg(v_t_3227_, v_fallback_3228_);
    lean_dec_ref(v_fallback_3228_);
    lean_dec(v_t_3227_);
    return v_res_3229_;
}
pub unsafe fn l_Std_TreeMap_minEntryD(
    mut v_00_u03b1_3230_: *mut LeanObject,
    mut v_00_u03b2_3231_: *mut LeanObject,
    mut v_cmp_3232_: *mut LeanObject,
    mut v_t_3233_: *mut LeanObject,
    mut v_fallback_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    v___x_3235_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_3233_, v_fallback_3234_);
    return v___x_3235_;
}
pub unsafe fn l_Std_TreeMap_minEntryD___boxed(
    mut v_00_u03b1_3236_: *mut LeanObject,
    mut v_00_u03b2_3237_: *mut LeanObject,
    mut v_cmp_3238_: *mut LeanObject,
    mut v_t_3239_: *mut LeanObject,
    mut v_fallback_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3241_: *mut LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Std_TreeMap_minEntryD(
        v_00_u03b1_3236_,
        v_00_u03b2_3237_,
        v_cmp_3238_,
        v_t_3239_,
        v_fallback_3240_,
    );
    lean_dec_ref(v_fallback_3240_);
    lean_dec(v_t_3239_);
    lean_dec_ref(v_cmp_3238_);
    return v_res_3241_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x3f___redArg(
    mut v_t_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_3242_);
    return v___x_3243_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x3f___redArg___boxed(
    mut v_t_3244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3245_: *mut LeanObject = core::ptr::null_mut();
    v_res_3245_ = l_Std_TreeMap_maxEntry_x3f___redArg(v_t_3244_);
    lean_dec(v_t_3244_);
    return v_res_3245_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x3f(
    mut v_00_u03b1_3246_: *mut LeanObject,
    mut v_00_u03b2_3247_: *mut LeanObject,
    mut v_cmp_3248_: *mut LeanObject,
    mut v_t_3249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_3249_);
    return v___x_3250_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x3f___boxed(
    mut v_00_u03b1_3251_: *mut LeanObject,
    mut v_00_u03b2_3252_: *mut LeanObject,
    mut v_cmp_3253_: *mut LeanObject,
    mut v_t_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3255_: *mut LeanObject = core::ptr::null_mut();
    v_res_3255_ =
        l_Std_TreeMap_maxEntry_x3f(v_00_u03b1_3251_, v_00_u03b2_3252_, v_cmp_3253_, v_t_3254_);
    lean_dec(v_t_3254_);
    lean_dec_ref(v_cmp_3253_);
    return v_res_3255_;
}
pub unsafe fn l_Std_TreeMap_maxEntry___redArg(mut v_t_3256_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    v___x_3257_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_3256_);
    return v___x_3257_;
}
pub unsafe fn l_Std_TreeMap_maxEntry___redArg___boxed(
    mut v_t_3258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3259_: *mut LeanObject = core::ptr::null_mut();
    v_res_3259_ = l_Std_TreeMap_maxEntry___redArg(v_t_3258_);
    lean_dec(v_t_3258_);
    return v_res_3259_;
}
pub unsafe fn l_Std_TreeMap_maxEntry(
    mut v_00_u03b1_3260_: *mut LeanObject,
    mut v_00_u03b2_3261_: *mut LeanObject,
    mut v_cmp_3262_: *mut LeanObject,
    mut v_t_3263_: *mut LeanObject,
    mut v_h_3264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    v___x_3265_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_3263_);
    return v___x_3265_;
}
pub unsafe fn l_Std_TreeMap_maxEntry___boxed(
    mut v_00_u03b1_3266_: *mut LeanObject,
    mut v_00_u03b2_3267_: *mut LeanObject,
    mut v_cmp_3268_: *mut LeanObject,
    mut v_t_3269_: *mut LeanObject,
    mut v_h_3270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3271_: *mut LeanObject = core::ptr::null_mut();
    v_res_3271_ = l_Std_TreeMap_maxEntry(
        v_00_u03b1_3266_,
        v_00_u03b2_3267_,
        v_cmp_3268_,
        v_t_3269_,
        v_h_3270_,
    );
    lean_dec(v_t_3269_);
    lean_dec_ref(v_cmp_3268_);
    return v_res_3271_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x21___redArg(
    mut v_inst_3272_: *mut LeanObject,
    mut v_t_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    v___x_3274_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3272_, v_t_3273_);
    return v___x_3274_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x21___redArg___boxed(
    mut v_inst_3275_: *mut LeanObject,
    mut v_t_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3277_: *mut LeanObject = core::ptr::null_mut();
    v_res_3277_ = l_Std_TreeMap_maxEntry_x21___redArg(v_inst_3275_, v_t_3276_);
    lean_dec(v_t_3276_);
    lean_dec_ref(v_inst_3275_);
    return v_res_3277_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x21(
    mut v_00_u03b1_3278_: *mut LeanObject,
    mut v_00_u03b2_3279_: *mut LeanObject,
    mut v_cmp_3280_: *mut LeanObject,
    mut v_inst_3281_: *mut LeanObject,
    mut v_t_3282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v___x_3283_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3281_, v_t_3282_);
    return v___x_3283_;
}
pub unsafe fn l_Std_TreeMap_maxEntry_x21___boxed(
    mut v_00_u03b1_3284_: *mut LeanObject,
    mut v_00_u03b2_3285_: *mut LeanObject,
    mut v_cmp_3286_: *mut LeanObject,
    mut v_inst_3287_: *mut LeanObject,
    mut v_t_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3289_: *mut LeanObject = core::ptr::null_mut();
    v_res_3289_ = l_Std_TreeMap_maxEntry_x21(
        v_00_u03b1_3284_,
        v_00_u03b2_3285_,
        v_cmp_3286_,
        v_inst_3287_,
        v_t_3288_,
    );
    lean_dec(v_t_3288_);
    lean_dec_ref(v_inst_3287_);
    lean_dec_ref(v_cmp_3286_);
    return v_res_3289_;
}
pub unsafe fn l_Std_TreeMap_maxEntryD___redArg(
    mut v_t_3290_: *mut LeanObject,
    mut v_fallback_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    v___x_3292_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_3290_, v_fallback_3291_);
    return v___x_3292_;
}
pub unsafe fn l_Std_TreeMap_maxEntryD___redArg___boxed(
    mut v_t_3293_: *mut LeanObject,
    mut v_fallback_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_Std_TreeMap_maxEntryD___redArg(v_t_3293_, v_fallback_3294_);
    lean_dec_ref(v_fallback_3294_);
    lean_dec(v_t_3293_);
    return v_res_3295_;
}
pub unsafe fn l_Std_TreeMap_maxEntryD(
    mut v_00_u03b1_3296_: *mut LeanObject,
    mut v_00_u03b2_3297_: *mut LeanObject,
    mut v_cmp_3298_: *mut LeanObject,
    mut v_t_3299_: *mut LeanObject,
    mut v_fallback_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_3299_, v_fallback_3300_);
    return v___x_3301_;
}
pub unsafe fn l_Std_TreeMap_maxEntryD___boxed(
    mut v_00_u03b1_3302_: *mut LeanObject,
    mut v_00_u03b2_3303_: *mut LeanObject,
    mut v_cmp_3304_: *mut LeanObject,
    mut v_t_3305_: *mut LeanObject,
    mut v_fallback_3306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3307_: *mut LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Std_TreeMap_maxEntryD(
        v_00_u03b1_3302_,
        v_00_u03b2_3303_,
        v_cmp_3304_,
        v_t_3305_,
        v_fallback_3306_,
    );
    lean_dec_ref(v_fallback_3306_);
    lean_dec(v_t_3305_);
    lean_dec_ref(v_cmp_3304_);
    return v_res_3307_;
}
pub unsafe fn l_Std_TreeMap_minKey_x3f___redArg(mut v_t_3308_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    v___x_3309_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_3308_);
    return v___x_3309_;
}
pub unsafe fn l_Std_TreeMap_minKey_x3f___redArg___boxed(
    mut v_t_3310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3311_: *mut LeanObject = core::ptr::null_mut();
    v_res_3311_ = l_Std_TreeMap_minKey_x3f___redArg(v_t_3310_);
    lean_dec(v_t_3310_);
    return v_res_3311_;
}
pub unsafe fn l_Std_TreeMap_minKey_x3f(
    mut v_00_u03b1_3312_: *mut LeanObject,
    mut v_00_u03b2_3313_: *mut LeanObject,
    mut v_cmp_3314_: *mut LeanObject,
    mut v_t_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    v___x_3316_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_3315_);
    return v___x_3316_;
}
pub unsafe fn l_Std_TreeMap_minKey_x3f___boxed(
    mut v_00_u03b1_3317_: *mut LeanObject,
    mut v_00_u03b2_3318_: *mut LeanObject,
    mut v_cmp_3319_: *mut LeanObject,
    mut v_t_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3321_: *mut LeanObject = core::ptr::null_mut();
    v_res_3321_ =
        l_Std_TreeMap_minKey_x3f(v_00_u03b1_3317_, v_00_u03b2_3318_, v_cmp_3319_, v_t_3320_);
    lean_dec(v_t_3320_);
    lean_dec_ref(v_cmp_3319_);
    return v_res_3321_;
}
pub unsafe fn l_Std_TreeMap_minKey___redArg(mut v_t_3322_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    v___x_3323_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_3322_);
    return v___x_3323_;
}
pub unsafe fn l_Std_TreeMap_minKey___redArg___boxed(
    mut v_t_3324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3325_: *mut LeanObject = core::ptr::null_mut();
    v_res_3325_ = l_Std_TreeMap_minKey___redArg(v_t_3324_);
    lean_dec(v_t_3324_);
    return v_res_3325_;
}
pub unsafe fn l_Std_TreeMap_minKey(
    mut v_00_u03b1_3326_: *mut LeanObject,
    mut v_00_u03b2_3327_: *mut LeanObject,
    mut v_cmp_3328_: *mut LeanObject,
    mut v_t_3329_: *mut LeanObject,
    mut v_h_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_3329_);
    return v___x_3331_;
}
pub unsafe fn l_Std_TreeMap_minKey___boxed(
    mut v_00_u03b1_3332_: *mut LeanObject,
    mut v_00_u03b2_3333_: *mut LeanObject,
    mut v_cmp_3334_: *mut LeanObject,
    mut v_t_3335_: *mut LeanObject,
    mut v_h_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3337_: *mut LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Std_TreeMap_minKey(
        v_00_u03b1_3332_,
        v_00_u03b2_3333_,
        v_cmp_3334_,
        v_t_3335_,
        v_h_3336_,
    );
    lean_dec(v_t_3335_);
    lean_dec_ref(v_cmp_3334_);
    return v_res_3337_;
}
pub unsafe fn l_Std_TreeMap_minKey_x21___redArg(
    mut v_inst_3338_: *mut LeanObject,
    mut v_t_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    v___x_3340_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_3338_, v_t_3339_);
    return v___x_3340_;
}
pub unsafe fn l_Std_TreeMap_minKey_x21___redArg___boxed(
    mut v_inst_3341_: *mut LeanObject,
    mut v_t_3342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3343_: *mut LeanObject = core::ptr::null_mut();
    v_res_3343_ = l_Std_TreeMap_minKey_x21___redArg(v_inst_3341_, v_t_3342_);
    lean_dec(v_t_3342_);
    lean_dec(v_inst_3341_);
    return v_res_3343_;
}
pub unsafe fn l_Std_TreeMap_minKey_x21(
    mut v_00_u03b1_3344_: *mut LeanObject,
    mut v_00_u03b2_3345_: *mut LeanObject,
    mut v_cmp_3346_: *mut LeanObject,
    mut v_inst_3347_: *mut LeanObject,
    mut v_t_3348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    v___x_3349_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_3347_, v_t_3348_);
    return v___x_3349_;
}
pub unsafe fn l_Std_TreeMap_minKey_x21___boxed(
    mut v_00_u03b1_3350_: *mut LeanObject,
    mut v_00_u03b2_3351_: *mut LeanObject,
    mut v_cmp_3352_: *mut LeanObject,
    mut v_inst_3353_: *mut LeanObject,
    mut v_t_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3355_: *mut LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Std_TreeMap_minKey_x21(
        v_00_u03b1_3350_,
        v_00_u03b2_3351_,
        v_cmp_3352_,
        v_inst_3353_,
        v_t_3354_,
    );
    lean_dec(v_t_3354_);
    lean_dec(v_inst_3353_);
    lean_dec_ref(v_cmp_3352_);
    return v_res_3355_;
}
pub unsafe fn l_Std_TreeMap_minKeyD___redArg(
    mut v_t_3356_: *mut LeanObject,
    mut v_fallback_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_3356_, v_fallback_3357_);
    return v___x_3358_;
}
pub unsafe fn l_Std_TreeMap_minKeyD___redArg___boxed(
    mut v_t_3359_: *mut LeanObject,
    mut v_fallback_3360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3361_: *mut LeanObject = core::ptr::null_mut();
    v_res_3361_ = l_Std_TreeMap_minKeyD___redArg(v_t_3359_, v_fallback_3360_);
    lean_dec(v_fallback_3360_);
    lean_dec(v_t_3359_);
    return v_res_3361_;
}
pub unsafe fn l_Std_TreeMap_minKeyD(
    mut v_00_u03b1_3362_: *mut LeanObject,
    mut v_00_u03b2_3363_: *mut LeanObject,
    mut v_cmp_3364_: *mut LeanObject,
    mut v_t_3365_: *mut LeanObject,
    mut v_fallback_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    v___x_3367_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_3365_, v_fallback_3366_);
    return v___x_3367_;
}
pub unsafe fn l_Std_TreeMap_minKeyD___boxed(
    mut v_00_u03b1_3368_: *mut LeanObject,
    mut v_00_u03b2_3369_: *mut LeanObject,
    mut v_cmp_3370_: *mut LeanObject,
    mut v_t_3371_: *mut LeanObject,
    mut v_fallback_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3373_: *mut LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Std_TreeMap_minKeyD(
        v_00_u03b1_3368_,
        v_00_u03b2_3369_,
        v_cmp_3370_,
        v_t_3371_,
        v_fallback_3372_,
    );
    lean_dec(v_fallback_3372_);
    lean_dec(v_t_3371_);
    lean_dec_ref(v_cmp_3370_);
    return v_res_3373_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x3f___redArg(mut v_t_3374_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    v___x_3375_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_3374_);
    return v___x_3375_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x3f___redArg___boxed(
    mut v_t_3376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3377_: *mut LeanObject = core::ptr::null_mut();
    v_res_3377_ = l_Std_TreeMap_maxKey_x3f___redArg(v_t_3376_);
    lean_dec(v_t_3376_);
    return v_res_3377_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x3f(
    mut v_00_u03b1_3378_: *mut LeanObject,
    mut v_00_u03b2_3379_: *mut LeanObject,
    mut v_cmp_3380_: *mut LeanObject,
    mut v_t_3381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    v___x_3382_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_3381_);
    return v___x_3382_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x3f___boxed(
    mut v_00_u03b1_3383_: *mut LeanObject,
    mut v_00_u03b2_3384_: *mut LeanObject,
    mut v_cmp_3385_: *mut LeanObject,
    mut v_t_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3387_: *mut LeanObject = core::ptr::null_mut();
    v_res_3387_ =
        l_Std_TreeMap_maxKey_x3f(v_00_u03b1_3383_, v_00_u03b2_3384_, v_cmp_3385_, v_t_3386_);
    lean_dec(v_t_3386_);
    lean_dec_ref(v_cmp_3385_);
    return v_res_3387_;
}
pub unsafe fn l_Std_TreeMap_maxKey___redArg(mut v_t_3388_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    v___x_3389_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_3388_);
    return v___x_3389_;
}
pub unsafe fn l_Std_TreeMap_maxKey___redArg___boxed(
    mut v_t_3390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3391_: *mut LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Std_TreeMap_maxKey___redArg(v_t_3390_);
    lean_dec(v_t_3390_);
    return v_res_3391_;
}
pub unsafe fn l_Std_TreeMap_maxKey(
    mut v_00_u03b1_3392_: *mut LeanObject,
    mut v_00_u03b2_3393_: *mut LeanObject,
    mut v_cmp_3394_: *mut LeanObject,
    mut v_t_3395_: *mut LeanObject,
    mut v_h_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    v___x_3397_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_3395_);
    return v___x_3397_;
}
pub unsafe fn l_Std_TreeMap_maxKey___boxed(
    mut v_00_u03b1_3398_: *mut LeanObject,
    mut v_00_u03b2_3399_: *mut LeanObject,
    mut v_cmp_3400_: *mut LeanObject,
    mut v_t_3401_: *mut LeanObject,
    mut v_h_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3403_: *mut LeanObject = core::ptr::null_mut();
    v_res_3403_ = l_Std_TreeMap_maxKey(
        v_00_u03b1_3398_,
        v_00_u03b2_3399_,
        v_cmp_3400_,
        v_t_3401_,
        v_h_3402_,
    );
    lean_dec(v_t_3401_);
    lean_dec_ref(v_cmp_3400_);
    return v_res_3403_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x21___redArg(
    mut v_inst_3404_: *mut LeanObject,
    mut v_t_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    v___x_3406_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_3404_, v_t_3405_);
    return v___x_3406_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x21___redArg___boxed(
    mut v_inst_3407_: *mut LeanObject,
    mut v_t_3408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3409_: *mut LeanObject = core::ptr::null_mut();
    v_res_3409_ = l_Std_TreeMap_maxKey_x21___redArg(v_inst_3407_, v_t_3408_);
    lean_dec(v_t_3408_);
    lean_dec(v_inst_3407_);
    return v_res_3409_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x21(
    mut v_00_u03b1_3410_: *mut LeanObject,
    mut v_00_u03b2_3411_: *mut LeanObject,
    mut v_cmp_3412_: *mut LeanObject,
    mut v_inst_3413_: *mut LeanObject,
    mut v_t_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_3413_, v_t_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Std_TreeMap_maxKey_x21___boxed(
    mut v_00_u03b1_3416_: *mut LeanObject,
    mut v_00_u03b2_3417_: *mut LeanObject,
    mut v_cmp_3418_: *mut LeanObject,
    mut v_inst_3419_: *mut LeanObject,
    mut v_t_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3421_: *mut LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_Std_TreeMap_maxKey_x21(
        v_00_u03b1_3416_,
        v_00_u03b2_3417_,
        v_cmp_3418_,
        v_inst_3419_,
        v_t_3420_,
    );
    lean_dec(v_t_3420_);
    lean_dec(v_inst_3419_);
    lean_dec_ref(v_cmp_3418_);
    return v_res_3421_;
}
pub unsafe fn l_Std_TreeMap_maxKeyD___redArg(
    mut v_t_3422_: *mut LeanObject,
    mut v_fallback_3423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_3422_, v_fallback_3423_);
    return v___x_3424_;
}
pub unsafe fn l_Std_TreeMap_maxKeyD___redArg___boxed(
    mut v_t_3425_: *mut LeanObject,
    mut v_fallback_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3427_: *mut LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Std_TreeMap_maxKeyD___redArg(v_t_3425_, v_fallback_3426_);
    lean_dec(v_fallback_3426_);
    lean_dec(v_t_3425_);
    return v_res_3427_;
}
pub unsafe fn l_Std_TreeMap_maxKeyD(
    mut v_00_u03b1_3428_: *mut LeanObject,
    mut v_00_u03b2_3429_: *mut LeanObject,
    mut v_cmp_3430_: *mut LeanObject,
    mut v_t_3431_: *mut LeanObject,
    mut v_fallback_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_3431_, v_fallback_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Std_TreeMap_maxKeyD___boxed(
    mut v_00_u03b1_3434_: *mut LeanObject,
    mut v_00_u03b2_3435_: *mut LeanObject,
    mut v_cmp_3436_: *mut LeanObject,
    mut v_t_3437_: *mut LeanObject,
    mut v_fallback_3438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3439_: *mut LeanObject = core::ptr::null_mut();
    v_res_3439_ = l_Std_TreeMap_maxKeyD(
        v_00_u03b1_3434_,
        v_00_u03b2_3435_,
        v_cmp_3436_,
        v_t_3437_,
        v_fallback_3438_,
    );
    lean_dec(v_fallback_3438_);
    lean_dec(v_t_3437_);
    lean_dec_ref(v_cmp_3436_);
    return v_res_3439_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x3f___redArg(
    mut v_t_3440_: *mut LeanObject,
    mut v_n_3441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    v___x_3442_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_3440_, v_n_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x3f___redArg___boxed(
    mut v_t_3443_: *mut LeanObject,
    mut v_n_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3445_: *mut LeanObject = core::ptr::null_mut();
    v_res_3445_ = l_Std_TreeMap_entryAtIdx_x3f___redArg(v_t_3443_, v_n_3444_);
    lean_dec(v_t_3443_);
    return v_res_3445_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x3f(
    mut v_00_u03b1_3446_: *mut LeanObject,
    mut v_00_u03b2_3447_: *mut LeanObject,
    mut v_cmp_3448_: *mut LeanObject,
    mut v_t_3449_: *mut LeanObject,
    mut v_n_3450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    v___x_3451_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_3449_, v_n_3450_);
    return v___x_3451_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_3452_: *mut LeanObject,
    mut v_00_u03b2_3453_: *mut LeanObject,
    mut v_cmp_3454_: *mut LeanObject,
    mut v_t_3455_: *mut LeanObject,
    mut v_n_3456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3457_: *mut LeanObject = core::ptr::null_mut();
    v_res_3457_ = l_Std_TreeMap_entryAtIdx_x3f(
        v_00_u03b1_3452_,
        v_00_u03b2_3453_,
        v_cmp_3454_,
        v_t_3455_,
        v_n_3456_,
    );
    lean_dec(v_t_3455_);
    lean_dec_ref(v_cmp_3454_);
    return v_res_3457_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx___redArg(
    mut v_t_3458_: *mut LeanObject,
    mut v_n_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    v___x_3460_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_3458_, v_n_3459_);
    return v___x_3460_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx___redArg___boxed(
    mut v_t_3461_: *mut LeanObject,
    mut v_n_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3463_: *mut LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Std_TreeMap_entryAtIdx___redArg(v_t_3461_, v_n_3462_);
    lean_dec(v_t_3461_);
    return v_res_3463_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx(
    mut v_00_u03b1_3464_: *mut LeanObject,
    mut v_00_u03b2_3465_: *mut LeanObject,
    mut v_cmp_3466_: *mut LeanObject,
    mut v_t_3467_: *mut LeanObject,
    mut v_n_3468_: *mut LeanObject,
    mut v_h_3469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    v___x_3470_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_3467_, v_n_3468_);
    return v___x_3470_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx___boxed(
    mut v_00_u03b1_3471_: *mut LeanObject,
    mut v_00_u03b2_3472_: *mut LeanObject,
    mut v_cmp_3473_: *mut LeanObject,
    mut v_t_3474_: *mut LeanObject,
    mut v_n_3475_: *mut LeanObject,
    mut v_h_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3477_: *mut LeanObject = core::ptr::null_mut();
    v_res_3477_ = l_Std_TreeMap_entryAtIdx(
        v_00_u03b1_3471_,
        v_00_u03b2_3472_,
        v_cmp_3473_,
        v_t_3474_,
        v_n_3475_,
        v_h_3476_,
    );
    lean_dec(v_t_3474_);
    lean_dec_ref(v_cmp_3473_);
    return v_res_3477_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x21___redArg(
    mut v_inst_3478_: *mut LeanObject,
    mut v_t_3479_: *mut LeanObject,
    mut v_n_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_3478_,
        v_t_3479_,
        v_n_3480_,
    );
    return v___x_3481_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x21___redArg___boxed(
    mut v_inst_3482_: *mut LeanObject,
    mut v_t_3483_: *mut LeanObject,
    mut v_n_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3485_: *mut LeanObject = core::ptr::null_mut();
    v_res_3485_ = l_Std_TreeMap_entryAtIdx_x21___redArg(v_inst_3482_, v_t_3483_, v_n_3484_);
    lean_dec(v_t_3483_);
    lean_dec_ref(v_inst_3482_);
    return v_res_3485_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x21(
    mut v_00_u03b1_3486_: *mut LeanObject,
    mut v_00_u03b2_3487_: *mut LeanObject,
    mut v_cmp_3488_: *mut LeanObject,
    mut v_inst_3489_: *mut LeanObject,
    mut v_t_3490_: *mut LeanObject,
    mut v_n_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_3492_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_3489_,
        v_t_3490_,
        v_n_3491_,
    );
    return v___x_3492_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdx_x21___boxed(
    mut v_00_u03b1_3493_: *mut LeanObject,
    mut v_00_u03b2_3494_: *mut LeanObject,
    mut v_cmp_3495_: *mut LeanObject,
    mut v_inst_3496_: *mut LeanObject,
    mut v_t_3497_: *mut LeanObject,
    mut v_n_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3499_: *mut LeanObject = core::ptr::null_mut();
    v_res_3499_ = l_Std_TreeMap_entryAtIdx_x21(
        v_00_u03b1_3493_,
        v_00_u03b2_3494_,
        v_cmp_3495_,
        v_inst_3496_,
        v_t_3497_,
        v_n_3498_,
    );
    lean_dec(v_t_3497_);
    lean_dec_ref(v_inst_3496_);
    lean_dec_ref(v_cmp_3495_);
    return v_res_3499_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdxD___redArg(
    mut v_t_3500_: *mut LeanObject,
    mut v_n_3501_: *mut LeanObject,
    mut v_fallback_3502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    v___x_3503_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_3500_,
        v_n_3501_,
        v_fallback_3502_,
    );
    return v___x_3503_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdxD___redArg___boxed(
    mut v_t_3504_: *mut LeanObject,
    mut v_n_3505_: *mut LeanObject,
    mut v_fallback_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3507_: *mut LeanObject = core::ptr::null_mut();
    v_res_3507_ = l_Std_TreeMap_entryAtIdxD___redArg(v_t_3504_, v_n_3505_, v_fallback_3506_);
    lean_dec_ref(v_fallback_3506_);
    lean_dec(v_t_3504_);
    return v_res_3507_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdxD(
    mut v_00_u03b1_3508_: *mut LeanObject,
    mut v_00_u03b2_3509_: *mut LeanObject,
    mut v_cmp_3510_: *mut LeanObject,
    mut v_t_3511_: *mut LeanObject,
    mut v_n_3512_: *mut LeanObject,
    mut v_fallback_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_3511_,
        v_n_3512_,
        v_fallback_3513_,
    );
    return v___x_3514_;
}
pub unsafe fn l_Std_TreeMap_entryAtIdxD___boxed(
    mut v_00_u03b1_3515_: *mut LeanObject,
    mut v_00_u03b2_3516_: *mut LeanObject,
    mut v_cmp_3517_: *mut LeanObject,
    mut v_t_3518_: *mut LeanObject,
    mut v_n_3519_: *mut LeanObject,
    mut v_fallback_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3521_: *mut LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Std_TreeMap_entryAtIdxD(
        v_00_u03b1_3515_,
        v_00_u03b2_3516_,
        v_cmp_3517_,
        v_t_3518_,
        v_n_3519_,
        v_fallback_3520_,
    );
    lean_dec_ref(v_fallback_3520_);
    lean_dec(v_t_3518_);
    lean_dec_ref(v_cmp_3517_);
    return v_res_3521_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x3f___redArg(
    mut v_t_3522_: *mut LeanObject,
    mut v_n_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    v___x_3524_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_3522_, v_n_3523_);
    return v___x_3524_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x3f___redArg___boxed(
    mut v_t_3525_: *mut LeanObject,
    mut v_n_3526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3527_: *mut LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_Std_TreeMap_keyAtIdx_x3f___redArg(v_t_3525_, v_n_3526_);
    lean_dec(v_t_3525_);
    return v_res_3527_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x3f(
    mut v_00_u03b1_3528_: *mut LeanObject,
    mut v_00_u03b2_3529_: *mut LeanObject,
    mut v_cmp_3530_: *mut LeanObject,
    mut v_t_3531_: *mut LeanObject,
    mut v_n_3532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    v___x_3533_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_3531_, v_n_3532_);
    return v___x_3533_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x3f___boxed(
    mut v_00_u03b1_3534_: *mut LeanObject,
    mut v_00_u03b2_3535_: *mut LeanObject,
    mut v_cmp_3536_: *mut LeanObject,
    mut v_t_3537_: *mut LeanObject,
    mut v_n_3538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3539_: *mut LeanObject = core::ptr::null_mut();
    v_res_3539_ = l_Std_TreeMap_keyAtIdx_x3f(
        v_00_u03b1_3534_,
        v_00_u03b2_3535_,
        v_cmp_3536_,
        v_t_3537_,
        v_n_3538_,
    );
    lean_dec(v_t_3537_);
    lean_dec_ref(v_cmp_3536_);
    return v_res_3539_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx___redArg(
    mut v_t_3540_: *mut LeanObject,
    mut v_n_3541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    v___x_3542_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_3540_, v_n_3541_);
    return v___x_3542_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx___redArg___boxed(
    mut v_t_3543_: *mut LeanObject,
    mut v_n_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3545_: *mut LeanObject = core::ptr::null_mut();
    v_res_3545_ = l_Std_TreeMap_keyAtIdx___redArg(v_t_3543_, v_n_3544_);
    lean_dec(v_t_3543_);
    return v_res_3545_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx(
    mut v_00_u03b1_3546_: *mut LeanObject,
    mut v_00_u03b2_3547_: *mut LeanObject,
    mut v_cmp_3548_: *mut LeanObject,
    mut v_t_3549_: *mut LeanObject,
    mut v_n_3550_: *mut LeanObject,
    mut v_h_3551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    v___x_3552_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_3549_, v_n_3550_);
    return v___x_3552_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx___boxed(
    mut v_00_u03b1_3553_: *mut LeanObject,
    mut v_00_u03b2_3554_: *mut LeanObject,
    mut v_cmp_3555_: *mut LeanObject,
    mut v_t_3556_: *mut LeanObject,
    mut v_n_3557_: *mut LeanObject,
    mut v_h_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3559_: *mut LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Std_TreeMap_keyAtIdx(
        v_00_u03b1_3553_,
        v_00_u03b2_3554_,
        v_cmp_3555_,
        v_t_3556_,
        v_n_3557_,
        v_h_3558_,
    );
    lean_dec(v_t_3556_);
    lean_dec_ref(v_cmp_3555_);
    return v_res_3559_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x21___redArg(
    mut v_inst_3560_: *mut LeanObject,
    mut v_t_3561_: *mut LeanObject,
    mut v_n_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    v___x_3563_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_3560_, v_t_3561_, v_n_3562_);
    return v___x_3563_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x21___redArg___boxed(
    mut v_inst_3564_: *mut LeanObject,
    mut v_t_3565_: *mut LeanObject,
    mut v_n_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3567_: *mut LeanObject = core::ptr::null_mut();
    v_res_3567_ = l_Std_TreeMap_keyAtIdx_x21___redArg(v_inst_3564_, v_t_3565_, v_n_3566_);
    lean_dec(v_t_3565_);
    lean_dec(v_inst_3564_);
    return v_res_3567_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x21(
    mut v_00_u03b1_3568_: *mut LeanObject,
    mut v_00_u03b2_3569_: *mut LeanObject,
    mut v_cmp_3570_: *mut LeanObject,
    mut v_inst_3571_: *mut LeanObject,
    mut v_t_3572_: *mut LeanObject,
    mut v_n_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    v___x_3574_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_3571_, v_t_3572_, v_n_3573_);
    return v___x_3574_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdx_x21___boxed(
    mut v_00_u03b1_3575_: *mut LeanObject,
    mut v_00_u03b2_3576_: *mut LeanObject,
    mut v_cmp_3577_: *mut LeanObject,
    mut v_inst_3578_: *mut LeanObject,
    mut v_t_3579_: *mut LeanObject,
    mut v_n_3580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3581_: *mut LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Std_TreeMap_keyAtIdx_x21(
        v_00_u03b1_3575_,
        v_00_u03b2_3576_,
        v_cmp_3577_,
        v_inst_3578_,
        v_t_3579_,
        v_n_3580_,
    );
    lean_dec(v_t_3579_);
    lean_dec(v_inst_3578_);
    lean_dec_ref(v_cmp_3577_);
    return v_res_3581_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdxD___redArg(
    mut v_t_3582_: *mut LeanObject,
    mut v_n_3583_: *mut LeanObject,
    mut v_fallback_3584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    v___x_3585_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_3582_, v_n_3583_, v_fallback_3584_);
    return v___x_3585_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdxD___redArg___boxed(
    mut v_t_3586_: *mut LeanObject,
    mut v_n_3587_: *mut LeanObject,
    mut v_fallback_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3589_: *mut LeanObject = core::ptr::null_mut();
    v_res_3589_ = l_Std_TreeMap_keyAtIdxD___redArg(v_t_3586_, v_n_3587_, v_fallback_3588_);
    lean_dec(v_fallback_3588_);
    lean_dec(v_t_3586_);
    return v_res_3589_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdxD(
    mut v_00_u03b1_3590_: *mut LeanObject,
    mut v_00_u03b2_3591_: *mut LeanObject,
    mut v_cmp_3592_: *mut LeanObject,
    mut v_t_3593_: *mut LeanObject,
    mut v_n_3594_: *mut LeanObject,
    mut v_fallback_3595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3596_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_3593_, v_n_3594_, v_fallback_3595_);
    return v___x_3596_;
}
pub unsafe fn l_Std_TreeMap_keyAtIdxD___boxed(
    mut v_00_u03b1_3597_: *mut LeanObject,
    mut v_00_u03b2_3598_: *mut LeanObject,
    mut v_cmp_3599_: *mut LeanObject,
    mut v_t_3600_: *mut LeanObject,
    mut v_n_3601_: *mut LeanObject,
    mut v_fallback_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3603_: *mut LeanObject = core::ptr::null_mut();
    v_res_3603_ = l_Std_TreeMap_keyAtIdxD(
        v_00_u03b1_3597_,
        v_00_u03b2_3598_,
        v_cmp_3599_,
        v_t_3600_,
        v_n_3601_,
        v_fallback_3602_,
    );
    lean_dec(v_fallback_3602_);
    lean_dec(v_t_3600_);
    lean_dec_ref(v_cmp_3599_);
    return v_res_3603_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE_x3f___redArg(
    mut v_cmp_3604_: *mut LeanObject,
    mut v_t_3605_: *mut LeanObject,
    mut v_k_3606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    v___x_3607_ = lean_box(0);
    v___x_3608_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3604_,
        v_k_3606_,
        v___x_3607_,
        v_t_3605_,
    );
    return v___x_3608_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE_x3f(
    mut v_00_u03b1_3609_: *mut LeanObject,
    mut v_00_u03b2_3610_: *mut LeanObject,
    mut v_cmp_3611_: *mut LeanObject,
    mut v_t_3612_: *mut LeanObject,
    mut v_k_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    v___x_3614_ = lean_box(0);
    v___x_3615_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3611_,
        v_k_3613_,
        v___x_3614_,
        v_t_3612_,
    );
    return v___x_3615_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT_x3f___redArg(
    mut v_cmp_3616_: *mut LeanObject,
    mut v_t_3617_: *mut LeanObject,
    mut v_k_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    v___x_3619_ = lean_box(0);
    v___x_3620_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3616_,
        v_k_3618_,
        v___x_3619_,
        v_t_3617_,
    );
    return v___x_3620_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT_x3f(
    mut v_00_u03b1_3621_: *mut LeanObject,
    mut v_00_u03b2_3622_: *mut LeanObject,
    mut v_cmp_3623_: *mut LeanObject,
    mut v_t_3624_: *mut LeanObject,
    mut v_k_3625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    v___x_3626_ = lean_box(0);
    v___x_3627_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3623_,
        v_k_3625_,
        v___x_3626_,
        v_t_3624_,
    );
    return v___x_3627_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE_x3f___redArg(
    mut v_cmp_3628_: *mut LeanObject,
    mut v_t_3629_: *mut LeanObject,
    mut v_k_3630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    v___x_3631_ = lean_box(0);
    v___x_3632_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3628_,
        v_k_3630_,
        v___x_3631_,
        v_t_3629_,
    );
    return v___x_3632_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE_x3f(
    mut v_00_u03b1_3633_: *mut LeanObject,
    mut v_00_u03b2_3634_: *mut LeanObject,
    mut v_cmp_3635_: *mut LeanObject,
    mut v_t_3636_: *mut LeanObject,
    mut v_k_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    v___x_3638_ = lean_box(0);
    v___x_3639_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3635_,
        v_k_3637_,
        v___x_3638_,
        v_t_3636_,
    );
    return v___x_3639_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT_x3f___redArg(
    mut v_cmp_3640_: *mut LeanObject,
    mut v_t_3641_: *mut LeanObject,
    mut v_k_3642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    v___x_3643_ = lean_box(0);
    v___x_3644_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3640_,
        v_k_3642_,
        v___x_3643_,
        v_t_3641_,
    );
    return v___x_3644_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT_x3f(
    mut v_00_u03b1_3645_: *mut LeanObject,
    mut v_00_u03b2_3646_: *mut LeanObject,
    mut v_cmp_3647_: *mut LeanObject,
    mut v_t_3648_: *mut LeanObject,
    mut v_k_3649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    v___x_3650_ = lean_box(0);
    v___x_3651_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3647_,
        v_k_3649_,
        v___x_3650_,
        v_t_3648_,
    );
    return v___x_3651_;
}
pub unsafe fn _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    v___x_3655_ = l_Std_TreeMap_getEntryGE_x21___redArg___closed__2;
    v___x_3656_ = lean_unsigned_to_nat(14);
    v___x_3657_ = lean_unsigned_to_nat(22);
    v___x_3658_ = l_Std_TreeMap_getEntryGE_x21___redArg___closed__1;
    v___x_3659_ = l_Std_TreeMap_getEntryGE_x21___redArg___closed__0;
    v___x_3660_ = l_mkPanicMessageWithDecl(
        v___x_3659_,
        v___x_3658_,
        v___x_3657_,
        v___x_3656_,
        v___x_3655_,
    );
    return v___x_3660_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE_x21___redArg(
    mut v_cmp_3661_: *mut LeanObject,
    mut v_inst_3662_: *mut LeanObject,
    mut v_t_3663_: *mut LeanObject,
    mut v_k_3664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    v___x_3665_ = lean_box(0);
    v___x_3666_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3661_,
        v_k_3664_,
        v___x_3665_,
        v_t_3663_,
    );
    if lean_obj_tag(v___x_3666_) == 0 {
        let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
        v___x_3667_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3668_ = l_panic___redArg(v_inst_3662_, v___x_3667_);
        return v___x_3668_;
    } else {
        let mut v_val_3669_: *mut LeanObject = core::ptr::null_mut();
        v_val_3669_ = lean_ctor_get(v___x_3666_, 0);
        lean_inc(v_val_3669_);
        lean_dec_ref_known(v___x_3666_, 1);
        return v_val_3669_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGE_x21___redArg___boxed(
    mut v_cmp_3670_: *mut LeanObject,
    mut v_inst_3671_: *mut LeanObject,
    mut v_t_3672_: *mut LeanObject,
    mut v_k_3673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3674_: *mut LeanObject = core::ptr::null_mut();
    v_res_3674_ =
        l_Std_TreeMap_getEntryGE_x21___redArg(v_cmp_3670_, v_inst_3671_, v_t_3672_, v_k_3673_);
    lean_dec_ref(v_inst_3671_);
    return v_res_3674_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE_x21(
    mut v_00_u03b1_3675_: *mut LeanObject,
    mut v_00_u03b2_3676_: *mut LeanObject,
    mut v_cmp_3677_: *mut LeanObject,
    mut v_inst_3678_: *mut LeanObject,
    mut v_t_3679_: *mut LeanObject,
    mut v_k_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    v___x_3681_ = lean_box(0);
    v___x_3682_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3677_,
        v_k_3680_,
        v___x_3681_,
        v_t_3679_,
    );
    if lean_obj_tag(v___x_3682_) == 0 {
        let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
        v___x_3683_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3684_ = l_panic___redArg(v_inst_3678_, v___x_3683_);
        return v___x_3684_;
    } else {
        let mut v_val_3685_: *mut LeanObject = core::ptr::null_mut();
        v_val_3685_ = lean_ctor_get(v___x_3682_, 0);
        lean_inc(v_val_3685_);
        lean_dec_ref_known(v___x_3682_, 1);
        return v_val_3685_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGE_x21___boxed(
    mut v_00_u03b1_3686_: *mut LeanObject,
    mut v_00_u03b2_3687_: *mut LeanObject,
    mut v_cmp_3688_: *mut LeanObject,
    mut v_inst_3689_: *mut LeanObject,
    mut v_t_3690_: *mut LeanObject,
    mut v_k_3691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3692_: *mut LeanObject = core::ptr::null_mut();
    v_res_3692_ = l_Std_TreeMap_getEntryGE_x21(
        v_00_u03b1_3686_,
        v_00_u03b2_3687_,
        v_cmp_3688_,
        v_inst_3689_,
        v_t_3690_,
        v_k_3691_,
    );
    lean_dec_ref(v_inst_3689_);
    return v_res_3692_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT_x21___redArg(
    mut v_cmp_3693_: *mut LeanObject,
    mut v_inst_3694_: *mut LeanObject,
    mut v_t_3695_: *mut LeanObject,
    mut v_k_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3697_ = lean_box(0);
    v___x_3698_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3693_,
        v_k_3696_,
        v___x_3697_,
        v_t_3695_,
    );
    if lean_obj_tag(v___x_3698_) == 0 {
        let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
        v___x_3699_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3700_ = l_panic___redArg(v_inst_3694_, v___x_3699_);
        return v___x_3700_;
    } else {
        let mut v_val_3701_: *mut LeanObject = core::ptr::null_mut();
        v_val_3701_ = lean_ctor_get(v___x_3698_, 0);
        lean_inc(v_val_3701_);
        lean_dec_ref_known(v___x_3698_, 1);
        return v_val_3701_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGT_x21___redArg___boxed(
    mut v_cmp_3702_: *mut LeanObject,
    mut v_inst_3703_: *mut LeanObject,
    mut v_t_3704_: *mut LeanObject,
    mut v_k_3705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3706_: *mut LeanObject = core::ptr::null_mut();
    v_res_3706_ =
        l_Std_TreeMap_getEntryGT_x21___redArg(v_cmp_3702_, v_inst_3703_, v_t_3704_, v_k_3705_);
    lean_dec_ref(v_inst_3703_);
    return v_res_3706_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT_x21(
    mut v_00_u03b1_3707_: *mut LeanObject,
    mut v_00_u03b2_3708_: *mut LeanObject,
    mut v_cmp_3709_: *mut LeanObject,
    mut v_inst_3710_: *mut LeanObject,
    mut v_t_3711_: *mut LeanObject,
    mut v_k_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    v___x_3713_ = lean_box(0);
    v___x_3714_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3709_,
        v_k_3712_,
        v___x_3713_,
        v_t_3711_,
    );
    if lean_obj_tag(v___x_3714_) == 0 {
        let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
        v___x_3715_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3716_ = l_panic___redArg(v_inst_3710_, v___x_3715_);
        return v___x_3716_;
    } else {
        let mut v_val_3717_: *mut LeanObject = core::ptr::null_mut();
        v_val_3717_ = lean_ctor_get(v___x_3714_, 0);
        lean_inc(v_val_3717_);
        lean_dec_ref_known(v___x_3714_, 1);
        return v_val_3717_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGT_x21___boxed(
    mut v_00_u03b1_3718_: *mut LeanObject,
    mut v_00_u03b2_3719_: *mut LeanObject,
    mut v_cmp_3720_: *mut LeanObject,
    mut v_inst_3721_: *mut LeanObject,
    mut v_t_3722_: *mut LeanObject,
    mut v_k_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3724_: *mut LeanObject = core::ptr::null_mut();
    v_res_3724_ = l_Std_TreeMap_getEntryGT_x21(
        v_00_u03b1_3718_,
        v_00_u03b2_3719_,
        v_cmp_3720_,
        v_inst_3721_,
        v_t_3722_,
        v_k_3723_,
    );
    lean_dec_ref(v_inst_3721_);
    return v_res_3724_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE_x21___redArg(
    mut v_cmp_3725_: *mut LeanObject,
    mut v_inst_3726_: *mut LeanObject,
    mut v_t_3727_: *mut LeanObject,
    mut v_k_3728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    v___x_3729_ = lean_box(0);
    v___x_3730_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3725_,
        v_k_3728_,
        v___x_3729_,
        v_t_3727_,
    );
    if lean_obj_tag(v___x_3730_) == 0 {
        let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
        v___x_3731_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3732_ = l_panic___redArg(v_inst_3726_, v___x_3731_);
        return v___x_3732_;
    } else {
        let mut v_val_3733_: *mut LeanObject = core::ptr::null_mut();
        v_val_3733_ = lean_ctor_get(v___x_3730_, 0);
        lean_inc(v_val_3733_);
        lean_dec_ref_known(v___x_3730_, 1);
        return v_val_3733_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLE_x21___redArg___boxed(
    mut v_cmp_3734_: *mut LeanObject,
    mut v_inst_3735_: *mut LeanObject,
    mut v_t_3736_: *mut LeanObject,
    mut v_k_3737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3738_: *mut LeanObject = core::ptr::null_mut();
    v_res_3738_ =
        l_Std_TreeMap_getEntryLE_x21___redArg(v_cmp_3734_, v_inst_3735_, v_t_3736_, v_k_3737_);
    lean_dec_ref(v_inst_3735_);
    return v_res_3738_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE_x21(
    mut v_00_u03b1_3739_: *mut LeanObject,
    mut v_00_u03b2_3740_: *mut LeanObject,
    mut v_cmp_3741_: *mut LeanObject,
    mut v_inst_3742_: *mut LeanObject,
    mut v_t_3743_: *mut LeanObject,
    mut v_k_3744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = lean_box(0);
    v___x_3746_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3741_,
        v_k_3744_,
        v___x_3745_,
        v_t_3743_,
    );
    if lean_obj_tag(v___x_3746_) == 0 {
        let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
        v___x_3747_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3748_ = l_panic___redArg(v_inst_3742_, v___x_3747_);
        return v___x_3748_;
    } else {
        let mut v_val_3749_: *mut LeanObject = core::ptr::null_mut();
        v_val_3749_ = lean_ctor_get(v___x_3746_, 0);
        lean_inc(v_val_3749_);
        lean_dec_ref_known(v___x_3746_, 1);
        return v_val_3749_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLE_x21___boxed(
    mut v_00_u03b1_3750_: *mut LeanObject,
    mut v_00_u03b2_3751_: *mut LeanObject,
    mut v_cmp_3752_: *mut LeanObject,
    mut v_inst_3753_: *mut LeanObject,
    mut v_t_3754_: *mut LeanObject,
    mut v_k_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3756_: *mut LeanObject = core::ptr::null_mut();
    v_res_3756_ = l_Std_TreeMap_getEntryLE_x21(
        v_00_u03b1_3750_,
        v_00_u03b2_3751_,
        v_cmp_3752_,
        v_inst_3753_,
        v_t_3754_,
        v_k_3755_,
    );
    lean_dec_ref(v_inst_3753_);
    return v_res_3756_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT_x21___redArg(
    mut v_cmp_3757_: *mut LeanObject,
    mut v_inst_3758_: *mut LeanObject,
    mut v_t_3759_: *mut LeanObject,
    mut v_k_3760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    v___x_3761_ = lean_box(0);
    v___x_3762_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3757_,
        v_k_3760_,
        v___x_3761_,
        v_t_3759_,
    );
    if lean_obj_tag(v___x_3762_) == 0 {
        let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
        v___x_3763_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3764_ = l_panic___redArg(v_inst_3758_, v___x_3763_);
        return v___x_3764_;
    } else {
        let mut v_val_3765_: *mut LeanObject = core::ptr::null_mut();
        v_val_3765_ = lean_ctor_get(v___x_3762_, 0);
        lean_inc(v_val_3765_);
        lean_dec_ref_known(v___x_3762_, 1);
        return v_val_3765_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLT_x21___redArg___boxed(
    mut v_cmp_3766_: *mut LeanObject,
    mut v_inst_3767_: *mut LeanObject,
    mut v_t_3768_: *mut LeanObject,
    mut v_k_3769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3770_: *mut LeanObject = core::ptr::null_mut();
    v_res_3770_ =
        l_Std_TreeMap_getEntryLT_x21___redArg(v_cmp_3766_, v_inst_3767_, v_t_3768_, v_k_3769_);
    lean_dec_ref(v_inst_3767_);
    return v_res_3770_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT_x21(
    mut v_00_u03b1_3771_: *mut LeanObject,
    mut v_00_u03b2_3772_: *mut LeanObject,
    mut v_cmp_3773_: *mut LeanObject,
    mut v_inst_3774_: *mut LeanObject,
    mut v_t_3775_: *mut LeanObject,
    mut v_k_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    v___x_3777_ = lean_box(0);
    v___x_3778_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3773_,
        v_k_3776_,
        v___x_3777_,
        v_t_3775_,
    );
    if lean_obj_tag(v___x_3778_) == 0 {
        let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
        v___x_3779_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3780_ = l_panic___redArg(v_inst_3774_, v___x_3779_);
        return v___x_3780_;
    } else {
        let mut v_val_3781_: *mut LeanObject = core::ptr::null_mut();
        v_val_3781_ = lean_ctor_get(v___x_3778_, 0);
        lean_inc(v_val_3781_);
        lean_dec_ref_known(v___x_3778_, 1);
        return v_val_3781_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLT_x21___boxed(
    mut v_00_u03b1_3782_: *mut LeanObject,
    mut v_00_u03b2_3783_: *mut LeanObject,
    mut v_cmp_3784_: *mut LeanObject,
    mut v_inst_3785_: *mut LeanObject,
    mut v_t_3786_: *mut LeanObject,
    mut v_k_3787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3788_: *mut LeanObject = core::ptr::null_mut();
    v_res_3788_ = l_Std_TreeMap_getEntryLT_x21(
        v_00_u03b1_3782_,
        v_00_u03b2_3783_,
        v_cmp_3784_,
        v_inst_3785_,
        v_t_3786_,
        v_k_3787_,
    );
    lean_dec_ref(v_inst_3785_);
    return v_res_3788_;
}
pub unsafe fn l_Std_TreeMap_getEntryGED___redArg(
    mut v_cmp_3789_: *mut LeanObject,
    mut v_t_3790_: *mut LeanObject,
    mut v_k_3791_: *mut LeanObject,
    mut v_fallback_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    v___x_3793_ = lean_box(0);
    v___x_3794_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3789_,
        v_k_3791_,
        v___x_3793_,
        v_t_3790_,
    );
    if lean_obj_tag(v___x_3794_) == 0 {
        lean_inc_ref(v_fallback_3792_);
        return v_fallback_3792_;
    } else {
        let mut v_val_3795_: *mut LeanObject = core::ptr::null_mut();
        v_val_3795_ = lean_ctor_get(v___x_3794_, 0);
        lean_inc(v_val_3795_);
        lean_dec_ref_known(v___x_3794_, 1);
        return v_val_3795_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGED___redArg___boxed(
    mut v_cmp_3796_: *mut LeanObject,
    mut v_t_3797_: *mut LeanObject,
    mut v_k_3798_: *mut LeanObject,
    mut v_fallback_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3800_: *mut LeanObject = core::ptr::null_mut();
    v_res_3800_ =
        l_Std_TreeMap_getEntryGED___redArg(v_cmp_3796_, v_t_3797_, v_k_3798_, v_fallback_3799_);
    lean_dec_ref(v_fallback_3799_);
    return v_res_3800_;
}
pub unsafe fn l_Std_TreeMap_getEntryGED(
    mut v_00_u03b1_3801_: *mut LeanObject,
    mut v_00_u03b2_3802_: *mut LeanObject,
    mut v_cmp_3803_: *mut LeanObject,
    mut v_t_3804_: *mut LeanObject,
    mut v_k_3805_: *mut LeanObject,
    mut v_fallback_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    v___x_3807_ = lean_box(0);
    v___x_3808_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3803_,
        v_k_3805_,
        v___x_3807_,
        v_t_3804_,
    );
    if lean_obj_tag(v___x_3808_) == 0 {
        lean_inc_ref(v_fallback_3806_);
        return v_fallback_3806_;
    } else {
        let mut v_val_3809_: *mut LeanObject = core::ptr::null_mut();
        v_val_3809_ = lean_ctor_get(v___x_3808_, 0);
        lean_inc(v_val_3809_);
        lean_dec_ref_known(v___x_3808_, 1);
        return v_val_3809_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGED___boxed(
    mut v_00_u03b1_3810_: *mut LeanObject,
    mut v_00_u03b2_3811_: *mut LeanObject,
    mut v_cmp_3812_: *mut LeanObject,
    mut v_t_3813_: *mut LeanObject,
    mut v_k_3814_: *mut LeanObject,
    mut v_fallback_3815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3816_: *mut LeanObject = core::ptr::null_mut();
    v_res_3816_ = l_Std_TreeMap_getEntryGED(
        v_00_u03b1_3810_,
        v_00_u03b2_3811_,
        v_cmp_3812_,
        v_t_3813_,
        v_k_3814_,
        v_fallback_3815_,
    );
    lean_dec_ref(v_fallback_3815_);
    return v_res_3816_;
}
pub unsafe fn l_Std_TreeMap_getEntryGTD___redArg(
    mut v_cmp_3817_: *mut LeanObject,
    mut v_t_3818_: *mut LeanObject,
    mut v_k_3819_: *mut LeanObject,
    mut v_fallback_3820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    v___x_3821_ = lean_box(0);
    v___x_3822_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3817_,
        v_k_3819_,
        v___x_3821_,
        v_t_3818_,
    );
    if lean_obj_tag(v___x_3822_) == 0 {
        lean_inc_ref(v_fallback_3820_);
        return v_fallback_3820_;
    } else {
        let mut v_val_3823_: *mut LeanObject = core::ptr::null_mut();
        v_val_3823_ = lean_ctor_get(v___x_3822_, 0);
        lean_inc(v_val_3823_);
        lean_dec_ref_known(v___x_3822_, 1);
        return v_val_3823_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGTD___redArg___boxed(
    mut v_cmp_3824_: *mut LeanObject,
    mut v_t_3825_: *mut LeanObject,
    mut v_k_3826_: *mut LeanObject,
    mut v_fallback_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3828_: *mut LeanObject = core::ptr::null_mut();
    v_res_3828_ =
        l_Std_TreeMap_getEntryGTD___redArg(v_cmp_3824_, v_t_3825_, v_k_3826_, v_fallback_3827_);
    lean_dec_ref(v_fallback_3827_);
    return v_res_3828_;
}
pub unsafe fn l_Std_TreeMap_getEntryGTD(
    mut v_00_u03b1_3829_: *mut LeanObject,
    mut v_00_u03b2_3830_: *mut LeanObject,
    mut v_cmp_3831_: *mut LeanObject,
    mut v_t_3832_: *mut LeanObject,
    mut v_k_3833_: *mut LeanObject,
    mut v_fallback_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    v___x_3835_ = lean_box(0);
    v___x_3836_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3831_,
        v_k_3833_,
        v___x_3835_,
        v_t_3832_,
    );
    if lean_obj_tag(v___x_3836_) == 0 {
        lean_inc_ref(v_fallback_3834_);
        return v_fallback_3834_;
    } else {
        let mut v_val_3837_: *mut LeanObject = core::ptr::null_mut();
        v_val_3837_ = lean_ctor_get(v___x_3836_, 0);
        lean_inc(v_val_3837_);
        lean_dec_ref_known(v___x_3836_, 1);
        return v_val_3837_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryGTD___boxed(
    mut v_00_u03b1_3838_: *mut LeanObject,
    mut v_00_u03b2_3839_: *mut LeanObject,
    mut v_cmp_3840_: *mut LeanObject,
    mut v_t_3841_: *mut LeanObject,
    mut v_k_3842_: *mut LeanObject,
    mut v_fallback_3843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3844_: *mut LeanObject = core::ptr::null_mut();
    v_res_3844_ = l_Std_TreeMap_getEntryGTD(
        v_00_u03b1_3838_,
        v_00_u03b2_3839_,
        v_cmp_3840_,
        v_t_3841_,
        v_k_3842_,
        v_fallback_3843_,
    );
    lean_dec_ref(v_fallback_3843_);
    return v_res_3844_;
}
pub unsafe fn l_Std_TreeMap_getEntryLED___redArg(
    mut v_cmp_3845_: *mut LeanObject,
    mut v_t_3846_: *mut LeanObject,
    mut v_k_3847_: *mut LeanObject,
    mut v_fallback_3848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    v___x_3849_ = lean_box(0);
    v___x_3850_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3845_,
        v_k_3847_,
        v___x_3849_,
        v_t_3846_,
    );
    if lean_obj_tag(v___x_3850_) == 0 {
        lean_inc_ref(v_fallback_3848_);
        return v_fallback_3848_;
    } else {
        let mut v_val_3851_: *mut LeanObject = core::ptr::null_mut();
        v_val_3851_ = lean_ctor_get(v___x_3850_, 0);
        lean_inc(v_val_3851_);
        lean_dec_ref_known(v___x_3850_, 1);
        return v_val_3851_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLED___redArg___boxed(
    mut v_cmp_3852_: *mut LeanObject,
    mut v_t_3853_: *mut LeanObject,
    mut v_k_3854_: *mut LeanObject,
    mut v_fallback_3855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3856_: *mut LeanObject = core::ptr::null_mut();
    v_res_3856_ =
        l_Std_TreeMap_getEntryLED___redArg(v_cmp_3852_, v_t_3853_, v_k_3854_, v_fallback_3855_);
    lean_dec_ref(v_fallback_3855_);
    return v_res_3856_;
}
pub unsafe fn l_Std_TreeMap_getEntryLED(
    mut v_00_u03b1_3857_: *mut LeanObject,
    mut v_00_u03b2_3858_: *mut LeanObject,
    mut v_cmp_3859_: *mut LeanObject,
    mut v_t_3860_: *mut LeanObject,
    mut v_k_3861_: *mut LeanObject,
    mut v_fallback_3862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    v___x_3863_ = lean_box(0);
    v___x_3864_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3859_,
        v_k_3861_,
        v___x_3863_,
        v_t_3860_,
    );
    if lean_obj_tag(v___x_3864_) == 0 {
        lean_inc_ref(v_fallback_3862_);
        return v_fallback_3862_;
    } else {
        let mut v_val_3865_: *mut LeanObject = core::ptr::null_mut();
        v_val_3865_ = lean_ctor_get(v___x_3864_, 0);
        lean_inc(v_val_3865_);
        lean_dec_ref_known(v___x_3864_, 1);
        return v_val_3865_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLED___boxed(
    mut v_00_u03b1_3866_: *mut LeanObject,
    mut v_00_u03b2_3867_: *mut LeanObject,
    mut v_cmp_3868_: *mut LeanObject,
    mut v_t_3869_: *mut LeanObject,
    mut v_k_3870_: *mut LeanObject,
    mut v_fallback_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3872_: *mut LeanObject = core::ptr::null_mut();
    v_res_3872_ = l_Std_TreeMap_getEntryLED(
        v_00_u03b1_3866_,
        v_00_u03b2_3867_,
        v_cmp_3868_,
        v_t_3869_,
        v_k_3870_,
        v_fallback_3871_,
    );
    lean_dec_ref(v_fallback_3871_);
    return v_res_3872_;
}
pub unsafe fn l_Std_TreeMap_getEntryLTD___redArg(
    mut v_cmp_3873_: *mut LeanObject,
    mut v_t_3874_: *mut LeanObject,
    mut v_k_3875_: *mut LeanObject,
    mut v_fallback_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    v___x_3877_ = lean_box(0);
    v___x_3878_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3873_,
        v_k_3875_,
        v___x_3877_,
        v_t_3874_,
    );
    if lean_obj_tag(v___x_3878_) == 0 {
        lean_inc_ref(v_fallback_3876_);
        return v_fallback_3876_;
    } else {
        let mut v_val_3879_: *mut LeanObject = core::ptr::null_mut();
        v_val_3879_ = lean_ctor_get(v___x_3878_, 0);
        lean_inc(v_val_3879_);
        lean_dec_ref_known(v___x_3878_, 1);
        return v_val_3879_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLTD___redArg___boxed(
    mut v_cmp_3880_: *mut LeanObject,
    mut v_t_3881_: *mut LeanObject,
    mut v_k_3882_: *mut LeanObject,
    mut v_fallback_3883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3884_: *mut LeanObject = core::ptr::null_mut();
    v_res_3884_ =
        l_Std_TreeMap_getEntryLTD___redArg(v_cmp_3880_, v_t_3881_, v_k_3882_, v_fallback_3883_);
    lean_dec_ref(v_fallback_3883_);
    return v_res_3884_;
}
pub unsafe fn l_Std_TreeMap_getEntryLTD(
    mut v_00_u03b1_3885_: *mut LeanObject,
    mut v_00_u03b2_3886_: *mut LeanObject,
    mut v_cmp_3887_: *mut LeanObject,
    mut v_t_3888_: *mut LeanObject,
    mut v_k_3889_: *mut LeanObject,
    mut v_fallback_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    v___x_3891_ = lean_box(0);
    v___x_3892_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3887_,
        v_k_3889_,
        v___x_3891_,
        v_t_3888_,
    );
    if lean_obj_tag(v___x_3892_) == 0 {
        lean_inc_ref(v_fallback_3890_);
        return v_fallback_3890_;
    } else {
        let mut v_val_3893_: *mut LeanObject = core::ptr::null_mut();
        v_val_3893_ = lean_ctor_get(v___x_3892_, 0);
        lean_inc(v_val_3893_);
        lean_dec_ref_known(v___x_3892_, 1);
        return v_val_3893_;
    }
}
pub unsafe fn l_Std_TreeMap_getEntryLTD___boxed(
    mut v_00_u03b1_3894_: *mut LeanObject,
    mut v_00_u03b2_3895_: *mut LeanObject,
    mut v_cmp_3896_: *mut LeanObject,
    mut v_t_3897_: *mut LeanObject,
    mut v_k_3898_: *mut LeanObject,
    mut v_fallback_3899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3900_: *mut LeanObject = core::ptr::null_mut();
    v_res_3900_ = l_Std_TreeMap_getEntryLTD(
        v_00_u03b1_3894_,
        v_00_u03b2_3895_,
        v_cmp_3896_,
        v_t_3897_,
        v_k_3898_,
        v_fallback_3899_,
    );
    lean_dec_ref(v_fallback_3899_);
    return v_res_3900_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE_x3f___redArg(
    mut v_cmp_3901_: *mut LeanObject,
    mut v_t_3902_: *mut LeanObject,
    mut v_k_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    v___x_3904_ = lean_box(0);
    v___x_3905_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3901_,
        v_k_3903_,
        v___x_3904_,
        v_t_3902_,
    );
    return v___x_3905_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE_x3f(
    mut v_00_u03b1_3906_: *mut LeanObject,
    mut v_00_u03b2_3907_: *mut LeanObject,
    mut v_cmp_3908_: *mut LeanObject,
    mut v_t_3909_: *mut LeanObject,
    mut v_k_3910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    v___x_3911_ = lean_box(0);
    v___x_3912_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3908_,
        v_k_3910_,
        v___x_3911_,
        v_t_3909_,
    );
    return v___x_3912_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT_x3f___redArg(
    mut v_cmp_3913_: *mut LeanObject,
    mut v_t_3914_: *mut LeanObject,
    mut v_k_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    v___x_3916_ = lean_box(0);
    v___x_3917_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3913_,
        v_k_3915_,
        v___x_3916_,
        v_t_3914_,
    );
    return v___x_3917_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT_x3f(
    mut v_00_u03b1_3918_: *mut LeanObject,
    mut v_00_u03b2_3919_: *mut LeanObject,
    mut v_cmp_3920_: *mut LeanObject,
    mut v_t_3921_: *mut LeanObject,
    mut v_k_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    v___x_3923_ = lean_box(0);
    v___x_3924_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3920_,
        v_k_3922_,
        v___x_3923_,
        v_t_3921_,
    );
    return v___x_3924_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE_x3f___redArg(
    mut v_cmp_3925_: *mut LeanObject,
    mut v_t_3926_: *mut LeanObject,
    mut v_k_3927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    v___x_3928_ = lean_box(0);
    v___x_3929_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3925_,
        v_k_3927_,
        v___x_3928_,
        v_t_3926_,
    );
    return v___x_3929_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE_x3f(
    mut v_00_u03b1_3930_: *mut LeanObject,
    mut v_00_u03b2_3931_: *mut LeanObject,
    mut v_cmp_3932_: *mut LeanObject,
    mut v_t_3933_: *mut LeanObject,
    mut v_k_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    v___x_3935_ = lean_box(0);
    v___x_3936_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3932_,
        v_k_3934_,
        v___x_3935_,
        v_t_3933_,
    );
    return v___x_3936_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT_x3f___redArg(
    mut v_cmp_3937_: *mut LeanObject,
    mut v_t_3938_: *mut LeanObject,
    mut v_k_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    v___x_3940_ = lean_box(0);
    v___x_3941_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3937_,
        v_k_3939_,
        v___x_3940_,
        v_t_3938_,
    );
    return v___x_3941_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT_x3f(
    mut v_00_u03b1_3942_: *mut LeanObject,
    mut v_00_u03b2_3943_: *mut LeanObject,
    mut v_cmp_3944_: *mut LeanObject,
    mut v_t_3945_: *mut LeanObject,
    mut v_k_3946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    v___x_3947_ = lean_box(0);
    v___x_3948_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3944_,
        v_k_3946_,
        v___x_3947_,
        v_t_3945_,
    );
    return v___x_3948_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE_x21___redArg(
    mut v_cmp_3949_: *mut LeanObject,
    mut v_inst_3950_: *mut LeanObject,
    mut v_t_3951_: *mut LeanObject,
    mut v_k_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    v___x_3953_ = lean_box(0);
    v___x_3954_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3949_,
        v_k_3952_,
        v___x_3953_,
        v_t_3951_,
    );
    if lean_obj_tag(v___x_3954_) == 0 {
        let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
        v___x_3955_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3956_ = l_panic___redArg(v_inst_3950_, v___x_3955_);
        return v___x_3956_;
    } else {
        let mut v_val_3957_: *mut LeanObject = core::ptr::null_mut();
        v_val_3957_ = lean_ctor_get(v___x_3954_, 0);
        lean_inc(v_val_3957_);
        lean_dec_ref_known(v___x_3954_, 1);
        return v_val_3957_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGE_x21___redArg___boxed(
    mut v_cmp_3958_: *mut LeanObject,
    mut v_inst_3959_: *mut LeanObject,
    mut v_t_3960_: *mut LeanObject,
    mut v_k_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3962_: *mut LeanObject = core::ptr::null_mut();
    v_res_3962_ =
        l_Std_TreeMap_getKeyGE_x21___redArg(v_cmp_3958_, v_inst_3959_, v_t_3960_, v_k_3961_);
    lean_dec(v_inst_3959_);
    return v_res_3962_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE_x21(
    mut v_00_u03b1_3963_: *mut LeanObject,
    mut v_00_u03b2_3964_: *mut LeanObject,
    mut v_cmp_3965_: *mut LeanObject,
    mut v_inst_3966_: *mut LeanObject,
    mut v_t_3967_: *mut LeanObject,
    mut v_k_3968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    v___x_3969_ = lean_box(0);
    v___x_3970_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3965_,
        v_k_3968_,
        v___x_3969_,
        v_t_3967_,
    );
    if lean_obj_tag(v___x_3970_) == 0 {
        let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
        v___x_3971_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3972_ = l_panic___redArg(v_inst_3966_, v___x_3971_);
        return v___x_3972_;
    } else {
        let mut v_val_3973_: *mut LeanObject = core::ptr::null_mut();
        v_val_3973_ = lean_ctor_get(v___x_3970_, 0);
        lean_inc(v_val_3973_);
        lean_dec_ref_known(v___x_3970_, 1);
        return v_val_3973_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGE_x21___boxed(
    mut v_00_u03b1_3974_: *mut LeanObject,
    mut v_00_u03b2_3975_: *mut LeanObject,
    mut v_cmp_3976_: *mut LeanObject,
    mut v_inst_3977_: *mut LeanObject,
    mut v_t_3978_: *mut LeanObject,
    mut v_k_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3980_: *mut LeanObject = core::ptr::null_mut();
    v_res_3980_ = l_Std_TreeMap_getKeyGE_x21(
        v_00_u03b1_3974_,
        v_00_u03b2_3975_,
        v_cmp_3976_,
        v_inst_3977_,
        v_t_3978_,
        v_k_3979_,
    );
    lean_dec(v_inst_3977_);
    return v_res_3980_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT_x21___redArg(
    mut v_cmp_3981_: *mut LeanObject,
    mut v_inst_3982_: *mut LeanObject,
    mut v_t_3983_: *mut LeanObject,
    mut v_k_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    v___x_3985_ = lean_box(0);
    v___x_3986_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3981_,
        v_k_3984_,
        v___x_3985_,
        v_t_3983_,
    );
    if lean_obj_tag(v___x_3986_) == 0 {
        let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
        v___x_3987_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3988_ = l_panic___redArg(v_inst_3982_, v___x_3987_);
        return v___x_3988_;
    } else {
        let mut v_val_3989_: *mut LeanObject = core::ptr::null_mut();
        v_val_3989_ = lean_ctor_get(v___x_3986_, 0);
        lean_inc(v_val_3989_);
        lean_dec_ref_known(v___x_3986_, 1);
        return v_val_3989_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGT_x21___redArg___boxed(
    mut v_cmp_3990_: *mut LeanObject,
    mut v_inst_3991_: *mut LeanObject,
    mut v_t_3992_: *mut LeanObject,
    mut v_k_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3994_: *mut LeanObject = core::ptr::null_mut();
    v_res_3994_ =
        l_Std_TreeMap_getKeyGT_x21___redArg(v_cmp_3990_, v_inst_3991_, v_t_3992_, v_k_3993_);
    lean_dec(v_inst_3991_);
    return v_res_3994_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT_x21(
    mut v_00_u03b1_3995_: *mut LeanObject,
    mut v_00_u03b2_3996_: *mut LeanObject,
    mut v_cmp_3997_: *mut LeanObject,
    mut v_inst_3998_: *mut LeanObject,
    mut v_t_3999_: *mut LeanObject,
    mut v_k_4000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    v___x_4001_ = lean_box(0);
    v___x_4002_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3997_,
        v_k_4000_,
        v___x_4001_,
        v_t_3999_,
    );
    if lean_obj_tag(v___x_4002_) == 0 {
        let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
        v___x_4003_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4004_ = l_panic___redArg(v_inst_3998_, v___x_4003_);
        return v___x_4004_;
    } else {
        let mut v_val_4005_: *mut LeanObject = core::ptr::null_mut();
        v_val_4005_ = lean_ctor_get(v___x_4002_, 0);
        lean_inc(v_val_4005_);
        lean_dec_ref_known(v___x_4002_, 1);
        return v_val_4005_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGT_x21___boxed(
    mut v_00_u03b1_4006_: *mut LeanObject,
    mut v_00_u03b2_4007_: *mut LeanObject,
    mut v_cmp_4008_: *mut LeanObject,
    mut v_inst_4009_: *mut LeanObject,
    mut v_t_4010_: *mut LeanObject,
    mut v_k_4011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4012_: *mut LeanObject = core::ptr::null_mut();
    v_res_4012_ = l_Std_TreeMap_getKeyGT_x21(
        v_00_u03b1_4006_,
        v_00_u03b2_4007_,
        v_cmp_4008_,
        v_inst_4009_,
        v_t_4010_,
        v_k_4011_,
    );
    lean_dec(v_inst_4009_);
    return v_res_4012_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE_x21___redArg(
    mut v_cmp_4013_: *mut LeanObject,
    mut v_inst_4014_: *mut LeanObject,
    mut v_t_4015_: *mut LeanObject,
    mut v_k_4016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    v___x_4017_ = lean_box(0);
    v___x_4018_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4013_,
        v_k_4016_,
        v___x_4017_,
        v_t_4015_,
    );
    if lean_obj_tag(v___x_4018_) == 0 {
        let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
        v___x_4019_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4020_ = l_panic___redArg(v_inst_4014_, v___x_4019_);
        return v___x_4020_;
    } else {
        let mut v_val_4021_: *mut LeanObject = core::ptr::null_mut();
        v_val_4021_ = lean_ctor_get(v___x_4018_, 0);
        lean_inc(v_val_4021_);
        lean_dec_ref_known(v___x_4018_, 1);
        return v_val_4021_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLE_x21___redArg___boxed(
    mut v_cmp_4022_: *mut LeanObject,
    mut v_inst_4023_: *mut LeanObject,
    mut v_t_4024_: *mut LeanObject,
    mut v_k_4025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4026_: *mut LeanObject = core::ptr::null_mut();
    v_res_4026_ =
        l_Std_TreeMap_getKeyLE_x21___redArg(v_cmp_4022_, v_inst_4023_, v_t_4024_, v_k_4025_);
    lean_dec(v_inst_4023_);
    return v_res_4026_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE_x21(
    mut v_00_u03b1_4027_: *mut LeanObject,
    mut v_00_u03b2_4028_: *mut LeanObject,
    mut v_cmp_4029_: *mut LeanObject,
    mut v_inst_4030_: *mut LeanObject,
    mut v_t_4031_: *mut LeanObject,
    mut v_k_4032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    v___x_4033_ = lean_box(0);
    v___x_4034_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4029_,
        v_k_4032_,
        v___x_4033_,
        v_t_4031_,
    );
    if lean_obj_tag(v___x_4034_) == 0 {
        let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
        v___x_4035_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4036_ = l_panic___redArg(v_inst_4030_, v___x_4035_);
        return v___x_4036_;
    } else {
        let mut v_val_4037_: *mut LeanObject = core::ptr::null_mut();
        v_val_4037_ = lean_ctor_get(v___x_4034_, 0);
        lean_inc(v_val_4037_);
        lean_dec_ref_known(v___x_4034_, 1);
        return v_val_4037_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLE_x21___boxed(
    mut v_00_u03b1_4038_: *mut LeanObject,
    mut v_00_u03b2_4039_: *mut LeanObject,
    mut v_cmp_4040_: *mut LeanObject,
    mut v_inst_4041_: *mut LeanObject,
    mut v_t_4042_: *mut LeanObject,
    mut v_k_4043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4044_: *mut LeanObject = core::ptr::null_mut();
    v_res_4044_ = l_Std_TreeMap_getKeyLE_x21(
        v_00_u03b1_4038_,
        v_00_u03b2_4039_,
        v_cmp_4040_,
        v_inst_4041_,
        v_t_4042_,
        v_k_4043_,
    );
    lean_dec(v_inst_4041_);
    return v_res_4044_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT_x21___redArg(
    mut v_cmp_4045_: *mut LeanObject,
    mut v_inst_4046_: *mut LeanObject,
    mut v_t_4047_: *mut LeanObject,
    mut v_k_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    v___x_4049_ = lean_box(0);
    v___x_4050_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4045_,
        v_k_4048_,
        v___x_4049_,
        v_t_4047_,
    );
    if lean_obj_tag(v___x_4050_) == 0 {
        let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
        v___x_4051_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4052_ = l_panic___redArg(v_inst_4046_, v___x_4051_);
        return v___x_4052_;
    } else {
        let mut v_val_4053_: *mut LeanObject = core::ptr::null_mut();
        v_val_4053_ = lean_ctor_get(v___x_4050_, 0);
        lean_inc(v_val_4053_);
        lean_dec_ref_known(v___x_4050_, 1);
        return v_val_4053_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLT_x21___redArg___boxed(
    mut v_cmp_4054_: *mut LeanObject,
    mut v_inst_4055_: *mut LeanObject,
    mut v_t_4056_: *mut LeanObject,
    mut v_k_4057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4058_: *mut LeanObject = core::ptr::null_mut();
    v_res_4058_ =
        l_Std_TreeMap_getKeyLT_x21___redArg(v_cmp_4054_, v_inst_4055_, v_t_4056_, v_k_4057_);
    lean_dec(v_inst_4055_);
    return v_res_4058_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT_x21(
    mut v_00_u03b1_4059_: *mut LeanObject,
    mut v_00_u03b2_4060_: *mut LeanObject,
    mut v_cmp_4061_: *mut LeanObject,
    mut v_inst_4062_: *mut LeanObject,
    mut v_t_4063_: *mut LeanObject,
    mut v_k_4064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    v___x_4065_ = lean_box(0);
    v___x_4066_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4061_,
        v_k_4064_,
        v___x_4065_,
        v_t_4063_,
    );
    if lean_obj_tag(v___x_4066_) == 0 {
        let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
        v___x_4067_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4068_ = l_panic___redArg(v_inst_4062_, v___x_4067_);
        return v___x_4068_;
    } else {
        let mut v_val_4069_: *mut LeanObject = core::ptr::null_mut();
        v_val_4069_ = lean_ctor_get(v___x_4066_, 0);
        lean_inc(v_val_4069_);
        lean_dec_ref_known(v___x_4066_, 1);
        return v_val_4069_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLT_x21___boxed(
    mut v_00_u03b1_4070_: *mut LeanObject,
    mut v_00_u03b2_4071_: *mut LeanObject,
    mut v_cmp_4072_: *mut LeanObject,
    mut v_inst_4073_: *mut LeanObject,
    mut v_t_4074_: *mut LeanObject,
    mut v_k_4075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4076_: *mut LeanObject = core::ptr::null_mut();
    v_res_4076_ = l_Std_TreeMap_getKeyLT_x21(
        v_00_u03b1_4070_,
        v_00_u03b2_4071_,
        v_cmp_4072_,
        v_inst_4073_,
        v_t_4074_,
        v_k_4075_,
    );
    lean_dec(v_inst_4073_);
    return v_res_4076_;
}
pub unsafe fn l_Std_TreeMap_getKeyGED___redArg(
    mut v_cmp_4077_: *mut LeanObject,
    mut v_t_4078_: *mut LeanObject,
    mut v_k_4079_: *mut LeanObject,
    mut v_fallback_4080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    v___x_4081_ = lean_box(0);
    v___x_4082_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4077_,
        v_k_4079_,
        v___x_4081_,
        v_t_4078_,
    );
    if lean_obj_tag(v___x_4082_) == 0 {
        lean_inc(v_fallback_4080_);
        return v_fallback_4080_;
    } else {
        let mut v_val_4083_: *mut LeanObject = core::ptr::null_mut();
        v_val_4083_ = lean_ctor_get(v___x_4082_, 0);
        lean_inc(v_val_4083_);
        lean_dec_ref_known(v___x_4082_, 1);
        return v_val_4083_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGED___redArg___boxed(
    mut v_cmp_4084_: *mut LeanObject,
    mut v_t_4085_: *mut LeanObject,
    mut v_k_4086_: *mut LeanObject,
    mut v_fallback_4087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4088_: *mut LeanObject = core::ptr::null_mut();
    v_res_4088_ =
        l_Std_TreeMap_getKeyGED___redArg(v_cmp_4084_, v_t_4085_, v_k_4086_, v_fallback_4087_);
    lean_dec(v_fallback_4087_);
    return v_res_4088_;
}
pub unsafe fn l_Std_TreeMap_getKeyGED(
    mut v_00_u03b1_4089_: *mut LeanObject,
    mut v_00_u03b2_4090_: *mut LeanObject,
    mut v_cmp_4091_: *mut LeanObject,
    mut v_t_4092_: *mut LeanObject,
    mut v_k_4093_: *mut LeanObject,
    mut v_fallback_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    v___x_4095_ = lean_box(0);
    v___x_4096_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4091_,
        v_k_4093_,
        v___x_4095_,
        v_t_4092_,
    );
    if lean_obj_tag(v___x_4096_) == 0 {
        lean_inc(v_fallback_4094_);
        return v_fallback_4094_;
    } else {
        let mut v_val_4097_: *mut LeanObject = core::ptr::null_mut();
        v_val_4097_ = lean_ctor_get(v___x_4096_, 0);
        lean_inc(v_val_4097_);
        lean_dec_ref_known(v___x_4096_, 1);
        return v_val_4097_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGED___boxed(
    mut v_00_u03b1_4098_: *mut LeanObject,
    mut v_00_u03b2_4099_: *mut LeanObject,
    mut v_cmp_4100_: *mut LeanObject,
    mut v_t_4101_: *mut LeanObject,
    mut v_k_4102_: *mut LeanObject,
    mut v_fallback_4103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4104_: *mut LeanObject = core::ptr::null_mut();
    v_res_4104_ = l_Std_TreeMap_getKeyGED(
        v_00_u03b1_4098_,
        v_00_u03b2_4099_,
        v_cmp_4100_,
        v_t_4101_,
        v_k_4102_,
        v_fallback_4103_,
    );
    lean_dec(v_fallback_4103_);
    return v_res_4104_;
}
pub unsafe fn l_Std_TreeMap_getKeyGTD___redArg(
    mut v_cmp_4105_: *mut LeanObject,
    mut v_t_4106_: *mut LeanObject,
    mut v_k_4107_: *mut LeanObject,
    mut v_fallback_4108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    v___x_4109_ = lean_box(0);
    v___x_4110_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4105_,
        v_k_4107_,
        v___x_4109_,
        v_t_4106_,
    );
    if lean_obj_tag(v___x_4110_) == 0 {
        lean_inc(v_fallback_4108_);
        return v_fallback_4108_;
    } else {
        let mut v_val_4111_: *mut LeanObject = core::ptr::null_mut();
        v_val_4111_ = lean_ctor_get(v___x_4110_, 0);
        lean_inc(v_val_4111_);
        lean_dec_ref_known(v___x_4110_, 1);
        return v_val_4111_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGTD___redArg___boxed(
    mut v_cmp_4112_: *mut LeanObject,
    mut v_t_4113_: *mut LeanObject,
    mut v_k_4114_: *mut LeanObject,
    mut v_fallback_4115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4116_: *mut LeanObject = core::ptr::null_mut();
    v_res_4116_ =
        l_Std_TreeMap_getKeyGTD___redArg(v_cmp_4112_, v_t_4113_, v_k_4114_, v_fallback_4115_);
    lean_dec(v_fallback_4115_);
    return v_res_4116_;
}
pub unsafe fn l_Std_TreeMap_getKeyGTD(
    mut v_00_u03b1_4117_: *mut LeanObject,
    mut v_00_u03b2_4118_: *mut LeanObject,
    mut v_cmp_4119_: *mut LeanObject,
    mut v_t_4120_: *mut LeanObject,
    mut v_k_4121_: *mut LeanObject,
    mut v_fallback_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    v___x_4123_ = lean_box(0);
    v___x_4124_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4119_,
        v_k_4121_,
        v___x_4123_,
        v_t_4120_,
    );
    if lean_obj_tag(v___x_4124_) == 0 {
        lean_inc(v_fallback_4122_);
        return v_fallback_4122_;
    } else {
        let mut v_val_4125_: *mut LeanObject = core::ptr::null_mut();
        v_val_4125_ = lean_ctor_get(v___x_4124_, 0);
        lean_inc(v_val_4125_);
        lean_dec_ref_known(v___x_4124_, 1);
        return v_val_4125_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyGTD___boxed(
    mut v_00_u03b1_4126_: *mut LeanObject,
    mut v_00_u03b2_4127_: *mut LeanObject,
    mut v_cmp_4128_: *mut LeanObject,
    mut v_t_4129_: *mut LeanObject,
    mut v_k_4130_: *mut LeanObject,
    mut v_fallback_4131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4132_: *mut LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_Std_TreeMap_getKeyGTD(
        v_00_u03b1_4126_,
        v_00_u03b2_4127_,
        v_cmp_4128_,
        v_t_4129_,
        v_k_4130_,
        v_fallback_4131_,
    );
    lean_dec(v_fallback_4131_);
    return v_res_4132_;
}
pub unsafe fn l_Std_TreeMap_getKeyLED___redArg(
    mut v_cmp_4133_: *mut LeanObject,
    mut v_t_4134_: *mut LeanObject,
    mut v_k_4135_: *mut LeanObject,
    mut v_fallback_4136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    v___x_4137_ = lean_box(0);
    v___x_4138_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4133_,
        v_k_4135_,
        v___x_4137_,
        v_t_4134_,
    );
    if lean_obj_tag(v___x_4138_) == 0 {
        lean_inc(v_fallback_4136_);
        return v_fallback_4136_;
    } else {
        let mut v_val_4139_: *mut LeanObject = core::ptr::null_mut();
        v_val_4139_ = lean_ctor_get(v___x_4138_, 0);
        lean_inc(v_val_4139_);
        lean_dec_ref_known(v___x_4138_, 1);
        return v_val_4139_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLED___redArg___boxed(
    mut v_cmp_4140_: *mut LeanObject,
    mut v_t_4141_: *mut LeanObject,
    mut v_k_4142_: *mut LeanObject,
    mut v_fallback_4143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4144_: *mut LeanObject = core::ptr::null_mut();
    v_res_4144_ =
        l_Std_TreeMap_getKeyLED___redArg(v_cmp_4140_, v_t_4141_, v_k_4142_, v_fallback_4143_);
    lean_dec(v_fallback_4143_);
    return v_res_4144_;
}
pub unsafe fn l_Std_TreeMap_getKeyLED(
    mut v_00_u03b1_4145_: *mut LeanObject,
    mut v_00_u03b2_4146_: *mut LeanObject,
    mut v_cmp_4147_: *mut LeanObject,
    mut v_t_4148_: *mut LeanObject,
    mut v_k_4149_: *mut LeanObject,
    mut v_fallback_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    v___x_4151_ = lean_box(0);
    v___x_4152_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4147_,
        v_k_4149_,
        v___x_4151_,
        v_t_4148_,
    );
    if lean_obj_tag(v___x_4152_) == 0 {
        lean_inc(v_fallback_4150_);
        return v_fallback_4150_;
    } else {
        let mut v_val_4153_: *mut LeanObject = core::ptr::null_mut();
        v_val_4153_ = lean_ctor_get(v___x_4152_, 0);
        lean_inc(v_val_4153_);
        lean_dec_ref_known(v___x_4152_, 1);
        return v_val_4153_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLED___boxed(
    mut v_00_u03b1_4154_: *mut LeanObject,
    mut v_00_u03b2_4155_: *mut LeanObject,
    mut v_cmp_4156_: *mut LeanObject,
    mut v_t_4157_: *mut LeanObject,
    mut v_k_4158_: *mut LeanObject,
    mut v_fallback_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4160_: *mut LeanObject = core::ptr::null_mut();
    v_res_4160_ = l_Std_TreeMap_getKeyLED(
        v_00_u03b1_4154_,
        v_00_u03b2_4155_,
        v_cmp_4156_,
        v_t_4157_,
        v_k_4158_,
        v_fallback_4159_,
    );
    lean_dec(v_fallback_4159_);
    return v_res_4160_;
}
pub unsafe fn l_Std_TreeMap_getKeyLTD___redArg(
    mut v_cmp_4161_: *mut LeanObject,
    mut v_t_4162_: *mut LeanObject,
    mut v_k_4163_: *mut LeanObject,
    mut v_fallback_4164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    v___x_4165_ = lean_box(0);
    v___x_4166_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4161_,
        v_k_4163_,
        v___x_4165_,
        v_t_4162_,
    );
    if lean_obj_tag(v___x_4166_) == 0 {
        lean_inc(v_fallback_4164_);
        return v_fallback_4164_;
    } else {
        let mut v_val_4167_: *mut LeanObject = core::ptr::null_mut();
        v_val_4167_ = lean_ctor_get(v___x_4166_, 0);
        lean_inc(v_val_4167_);
        lean_dec_ref_known(v___x_4166_, 1);
        return v_val_4167_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLTD___redArg___boxed(
    mut v_cmp_4168_: *mut LeanObject,
    mut v_t_4169_: *mut LeanObject,
    mut v_k_4170_: *mut LeanObject,
    mut v_fallback_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4172_: *mut LeanObject = core::ptr::null_mut();
    v_res_4172_ =
        l_Std_TreeMap_getKeyLTD___redArg(v_cmp_4168_, v_t_4169_, v_k_4170_, v_fallback_4171_);
    lean_dec(v_fallback_4171_);
    return v_res_4172_;
}
pub unsafe fn l_Std_TreeMap_getKeyLTD(
    mut v_00_u03b1_4173_: *mut LeanObject,
    mut v_00_u03b2_4174_: *mut LeanObject,
    mut v_cmp_4175_: *mut LeanObject,
    mut v_t_4176_: *mut LeanObject,
    mut v_k_4177_: *mut LeanObject,
    mut v_fallback_4178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    v___x_4179_ = lean_box(0);
    v___x_4180_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4175_,
        v_k_4177_,
        v___x_4179_,
        v_t_4176_,
    );
    if lean_obj_tag(v___x_4180_) == 0 {
        lean_inc(v_fallback_4178_);
        return v_fallback_4178_;
    } else {
        let mut v_val_4181_: *mut LeanObject = core::ptr::null_mut();
        v_val_4181_ = lean_ctor_get(v___x_4180_, 0);
        lean_inc(v_val_4181_);
        lean_dec_ref_known(v___x_4180_, 1);
        return v_val_4181_;
    }
}
pub unsafe fn l_Std_TreeMap_getKeyLTD___boxed(
    mut v_00_u03b1_4182_: *mut LeanObject,
    mut v_00_u03b2_4183_: *mut LeanObject,
    mut v_cmp_4184_: *mut LeanObject,
    mut v_t_4185_: *mut LeanObject,
    mut v_k_4186_: *mut LeanObject,
    mut v_fallback_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4188_: *mut LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Std_TreeMap_getKeyLTD(
        v_00_u03b1_4182_,
        v_00_u03b2_4183_,
        v_cmp_4184_,
        v_t_4185_,
        v_k_4186_,
        v_fallback_4187_,
    );
    lean_dec(v_fallback_4187_);
    return v_res_4188_;
}
pub unsafe fn l_Std_TreeMap_filter___redArg(
    mut v_f_4189_: *mut LeanObject,
    mut v_m_4190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    v___x_4191_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_4189_, v_m_4190_);
    return v___x_4191_;
}
pub unsafe fn l_Std_TreeMap_filter(
    mut v_00_u03b1_4192_: *mut LeanObject,
    mut v_00_u03b2_4193_: *mut LeanObject,
    mut v_cmp_4194_: *mut LeanObject,
    mut v_f_4195_: *mut LeanObject,
    mut v_m_4196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_4195_, v_m_4196_);
    return v___x_4197_;
}
pub unsafe fn l_Std_TreeMap_filter___boxed(
    mut v_00_u03b1_4198_: *mut LeanObject,
    mut v_00_u03b2_4199_: *mut LeanObject,
    mut v_cmp_4200_: *mut LeanObject,
    mut v_f_4201_: *mut LeanObject,
    mut v_m_4202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4203_: *mut LeanObject = core::ptr::null_mut();
    v_res_4203_ = l_Std_TreeMap_filter(
        v_00_u03b1_4198_,
        v_00_u03b2_4199_,
        v_cmp_4200_,
        v_f_4201_,
        v_m_4202_,
    );
    lean_dec_ref(v_cmp_4200_);
    return v_res_4203_;
}
pub unsafe fn l_Std_TreeMap_foldlM___redArg(
    mut v_inst_4204_: *mut LeanObject,
    mut v_f_4205_: *mut LeanObject,
    mut v_init_4206_: *mut LeanObject,
    mut v_t_4207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    v___x_4208_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4204_,
        v_f_4205_,
        v_init_4206_,
        v_t_4207_,
    );
    return v___x_4208_;
}
pub unsafe fn l_Std_TreeMap_foldlM(
    mut v_00_u03b1_4209_: *mut LeanObject,
    mut v_00_u03b2_4210_: *mut LeanObject,
    mut v_cmp_4211_: *mut LeanObject,
    mut v_00_u03b4_4212_: *mut LeanObject,
    mut v_m_4213_: *mut LeanObject,
    mut v_inst_4214_: *mut LeanObject,
    mut v_f_4215_: *mut LeanObject,
    mut v_init_4216_: *mut LeanObject,
    mut v_t_4217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4214_,
        v_f_4215_,
        v_init_4216_,
        v_t_4217_,
    );
    return v___x_4218_;
}
pub unsafe fn l_Std_TreeMap_foldlM___boxed(
    mut v_00_u03b1_4219_: *mut LeanObject,
    mut v_00_u03b2_4220_: *mut LeanObject,
    mut v_cmp_4221_: *mut LeanObject,
    mut v_00_u03b4_4222_: *mut LeanObject,
    mut v_m_4223_: *mut LeanObject,
    mut v_inst_4224_: *mut LeanObject,
    mut v_f_4225_: *mut LeanObject,
    mut v_init_4226_: *mut LeanObject,
    mut v_t_4227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4228_: *mut LeanObject = core::ptr::null_mut();
    v_res_4228_ = l_Std_TreeMap_foldlM(
        v_00_u03b1_4219_,
        v_00_u03b2_4220_,
        v_cmp_4221_,
        v_00_u03b4_4222_,
        v_m_4223_,
        v_inst_4224_,
        v_f_4225_,
        v_init_4226_,
        v_t_4227_,
    );
    lean_dec_ref(v_cmp_4221_);
    return v_res_4228_;
}
pub unsafe fn l_Std_TreeMap_foldl___redArg(
    mut v_f_4229_: *mut LeanObject,
    mut v_init_4230_: *mut LeanObject,
    mut v_t_4231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    v___x_4232_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_4229_, v_init_4230_, v_t_4231_);
    return v___x_4232_;
}
pub unsafe fn l_Std_TreeMap_foldl(
    mut v_00_u03b1_4233_: *mut LeanObject,
    mut v_00_u03b2_4234_: *mut LeanObject,
    mut v_cmp_4235_: *mut LeanObject,
    mut v_00_u03b4_4236_: *mut LeanObject,
    mut v_f_4237_: *mut LeanObject,
    mut v_init_4238_: *mut LeanObject,
    mut v_t_4239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    v___x_4240_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_4237_, v_init_4238_, v_t_4239_);
    return v___x_4240_;
}
pub unsafe fn l_Std_TreeMap_foldl___boxed(
    mut v_00_u03b1_4241_: *mut LeanObject,
    mut v_00_u03b2_4242_: *mut LeanObject,
    mut v_cmp_4243_: *mut LeanObject,
    mut v_00_u03b4_4244_: *mut LeanObject,
    mut v_f_4245_: *mut LeanObject,
    mut v_init_4246_: *mut LeanObject,
    mut v_t_4247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4248_: *mut LeanObject = core::ptr::null_mut();
    v_res_4248_ = l_Std_TreeMap_foldl(
        v_00_u03b1_4241_,
        v_00_u03b2_4242_,
        v_cmp_4243_,
        v_00_u03b4_4244_,
        v_f_4245_,
        v_init_4246_,
        v_t_4247_,
    );
    lean_dec_ref(v_cmp_4243_);
    return v_res_4248_;
}
pub unsafe fn l_Std_TreeMap_foldrM___redArg(
    mut v_inst_4249_: *mut LeanObject,
    mut v_f_4250_: *mut LeanObject,
    mut v_init_4251_: *mut LeanObject,
    mut v_t_4252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    v___x_4253_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_4249_,
        v_f_4250_,
        v_init_4251_,
        v_t_4252_,
    );
    return v___x_4253_;
}
pub unsafe fn l_Std_TreeMap_foldrM(
    mut v_00_u03b1_4254_: *mut LeanObject,
    mut v_00_u03b2_4255_: *mut LeanObject,
    mut v_cmp_4256_: *mut LeanObject,
    mut v_00_u03b4_4257_: *mut LeanObject,
    mut v_m_4258_: *mut LeanObject,
    mut v_inst_4259_: *mut LeanObject,
    mut v_f_4260_: *mut LeanObject,
    mut v_init_4261_: *mut LeanObject,
    mut v_t_4262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    v___x_4263_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_4259_,
        v_f_4260_,
        v_init_4261_,
        v_t_4262_,
    );
    return v___x_4263_;
}
pub unsafe fn l_Std_TreeMap_foldrM___boxed(
    mut v_00_u03b1_4264_: *mut LeanObject,
    mut v_00_u03b2_4265_: *mut LeanObject,
    mut v_cmp_4266_: *mut LeanObject,
    mut v_00_u03b4_4267_: *mut LeanObject,
    mut v_m_4268_: *mut LeanObject,
    mut v_inst_4269_: *mut LeanObject,
    mut v_f_4270_: *mut LeanObject,
    mut v_init_4271_: *mut LeanObject,
    mut v_t_4272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4273_: *mut LeanObject = core::ptr::null_mut();
    v_res_4273_ = l_Std_TreeMap_foldrM(
        v_00_u03b1_4264_,
        v_00_u03b2_4265_,
        v_cmp_4266_,
        v_00_u03b4_4267_,
        v_m_4268_,
        v_inst_4269_,
        v_f_4270_,
        v_init_4271_,
        v_t_4272_,
    );
    lean_dec_ref(v_cmp_4266_);
    return v_res_4273_;
}
pub unsafe fn l_Std_TreeMap_foldr___redArg___lam__0(
    mut v_f_4274_: *mut LeanObject,
    mut v_x1_4275_: *mut LeanObject,
    mut v_x2_4276_: *mut LeanObject,
    mut v_x3_4277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    v___x_4278_ = lean_apply_3(v_f_4274_, v_x1_4275_, v_x2_4276_, v_x3_4277_);
    return v___x_4278_;
}
pub unsafe fn l_Std_TreeMap_foldr___redArg(
    mut v_f_4298_: *mut LeanObject,
    mut v_init_4299_: *mut LeanObject,
    mut v_t_4300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    v___f_4301_ = lean_alloc_closure(
        l_Std_TreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4301_, 0, v_f_4298_);
    v___x_4302_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4303_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4302_,
        v___f_4301_,
        v_init_4299_,
        v_t_4300_,
    );
    return v___x_4303_;
}
pub unsafe fn l_Std_TreeMap_foldr(
    mut v_00_u03b1_4304_: *mut LeanObject,
    mut v_00_u03b2_4305_: *mut LeanObject,
    mut v_cmp_4306_: *mut LeanObject,
    mut v_00_u03b4_4307_: *mut LeanObject,
    mut v_f_4308_: *mut LeanObject,
    mut v_init_4309_: *mut LeanObject,
    mut v_t_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    v___f_4311_ = lean_alloc_closure(
        l_Std_TreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4311_, 0, v_f_4308_);
    v___x_4312_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4313_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4312_,
        v___f_4311_,
        v_init_4309_,
        v_t_4310_,
    );
    return v___x_4313_;
}
pub unsafe fn l_Std_TreeMap_foldr___boxed(
    mut v_00_u03b1_4314_: *mut LeanObject,
    mut v_00_u03b2_4315_: *mut LeanObject,
    mut v_cmp_4316_: *mut LeanObject,
    mut v_00_u03b4_4317_: *mut LeanObject,
    mut v_f_4318_: *mut LeanObject,
    mut v_init_4319_: *mut LeanObject,
    mut v_t_4320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4321_: *mut LeanObject = core::ptr::null_mut();
    v_res_4321_ = l_Std_TreeMap_foldr(
        v_00_u03b1_4314_,
        v_00_u03b2_4315_,
        v_cmp_4316_,
        v_00_u03b4_4317_,
        v_f_4318_,
        v_init_4319_,
        v_t_4320_,
    );
    lean_dec_ref(v_cmp_4316_);
    return v_res_4321_;
}
pub unsafe fn l_Std_TreeMap_partition___redArg___lam__0(
    mut v_f_4322_: *mut LeanObject,
    mut v_cmp_4323_: *mut LeanObject,
    mut v_x_4324_: *mut LeanObject,
    mut v_a_4325_: *mut LeanObject,
    mut v_b_4326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: u8 = 0;
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4327_ = lean_ctor_get(v_x_4324_, 0);
                v_snd_4328_ = lean_ctor_get(v_x_4324_, 1);
                v_isSharedCheck_4342_ = (!lean_is_exclusive(v_x_4324_)) as u8;
                if v_isSharedCheck_4342_ == 0 {
                    v___x_4330_ = v_x_4324_;
                    v_isShared_4331_ = v_isSharedCheck_4342_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4328_);
                    lean_inc(v_fst_4327_);
                    lean_dec(v_x_4324_);
                    v___x_4330_ = lean_box(0);
                    v_isShared_4331_ = v_isSharedCheck_4342_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_b_4326_);
                lean_inc(v_a_4325_);
                v___x_4332_ = lean_apply_2(v_f_4322_, v_a_4325_, v_b_4326_);
                v___x_4333_ = (lean_unbox(v___x_4332_) as u8);
                if v___x_4333_ == 0 {
                    v___x_4334_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_4323_,
                        v_a_4325_,
                        v_b_4326_,
                        v_snd_4328_,
                    );
                    if v_isShared_4331_ == 0 {
                        lean_ctor_set(v___x_4330_, 1, v___x_4334_);
                        v___x_4336_ = v___x_4330_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_fst_4327_);
                        lean_ctor_set(v_reuseFailAlloc_4337_, 1, v___x_4334_);
                        v___x_4336_ = v_reuseFailAlloc_4337_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4338_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_4323_,
                        v_a_4325_,
                        v_b_4326_,
                        v_fst_4327_,
                    );
                    if v_isShared_4331_ == 0 {
                        lean_ctor_set(v___x_4330_, 0, v___x_4338_);
                        v___x_4340_ = v___x_4330_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4338_);
                        lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_snd_4328_);
                        v___x_4340_ = v_reuseFailAlloc_4341_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4336_;
            }
            3 => {
                return v___x_4340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_partition___redArg(
    mut v_cmp_4345_: *mut LeanObject,
    mut v_f_4346_: *mut LeanObject,
    mut v_t_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4348_ = lean_alloc_closure(
                    l_Std_TreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_4348_, 0, v_f_4346_);
                lean_closure_set(v___f_4348_, 1, v_cmp_4345_);
                v___x_4349_ = l_Std_TreeMap_partition___redArg___closed__0;
                v_p_4350_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4348_,
                    v___x_4349_,
                    v_t_4347_,
                );
                v_fst_4351_ = lean_ctor_get(v_p_4350_, 0);
                v_snd_4352_ = lean_ctor_get(v_p_4350_, 1);
                v_isSharedCheck_4359_ = (!lean_is_exclusive(v_p_4350_)) as u8;
                if v_isSharedCheck_4359_ == 0 {
                    v___x_4354_ = v_p_4350_;
                    v_isShared_4355_ = v_isSharedCheck_4359_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4352_);
                    lean_inc(v_fst_4351_);
                    lean_dec(v_p_4350_);
                    v___x_4354_ = lean_box(0);
                    v_isShared_4355_ = v_isSharedCheck_4359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4355_ == 0 {
                    v___x_4357_ = v___x_4354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_fst_4351_);
                    lean_ctor_set(v_reuseFailAlloc_4358_, 1, v_snd_4352_);
                    v___x_4357_ = v_reuseFailAlloc_4358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_partition(
    mut v_00_u03b1_4360_: *mut LeanObject,
    mut v_00_u03b2_4361_: *mut LeanObject,
    mut v_cmp_4362_: *mut LeanObject,
    mut v_f_4363_: *mut LeanObject,
    mut v_t_4364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4372_: u8 = 0;
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4365_ = lean_alloc_closure(
                    l_Std_TreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_4365_, 0, v_f_4363_);
                lean_closure_set(v___f_4365_, 1, v_cmp_4362_);
                v___x_4366_ = l_Std_TreeMap_partition___redArg___closed__0;
                v_p_4367_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4365_,
                    v___x_4366_,
                    v_t_4364_,
                );
                v_fst_4368_ = lean_ctor_get(v_p_4367_, 0);
                v_snd_4369_ = lean_ctor_get(v_p_4367_, 1);
                v_isSharedCheck_4376_ = (!lean_is_exclusive(v_p_4367_)) as u8;
                if v_isSharedCheck_4376_ == 0 {
                    v___x_4371_ = v_p_4367_;
                    v_isShared_4372_ = v_isSharedCheck_4376_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4369_);
                    lean_inc(v_fst_4368_);
                    lean_dec(v_p_4367_);
                    v___x_4371_ = lean_box(0);
                    v_isShared_4372_ = v_isSharedCheck_4376_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4372_ == 0 {
                    v___x_4374_ = v___x_4371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_fst_4368_);
                    lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_snd_4369_);
                    v___x_4374_ = v_reuseFailAlloc_4375_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_forM___redArg___lam__0(
    mut v_f_4377_: *mut LeanObject,
    mut v_x_4378_: *mut LeanObject,
    mut v_k_4379_: *mut LeanObject,
    mut v_v_4380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    v___x_4381_ = lean_apply_2(v_f_4377_, v_k_4379_, v_v_4380_);
    return v___x_4381_;
}
pub unsafe fn l_Std_TreeMap_forM___redArg(
    mut v_inst_4382_: *mut LeanObject,
    mut v_f_4383_: *mut LeanObject,
    mut v_t_4384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    v___f_4385_ = lean_alloc_closure(
        l_Std_TreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4385_, 0, v_f_4383_);
    v___x_4386_ = lean_box(0);
    v___x_4387_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4382_,
        v___f_4385_,
        v___x_4386_,
        v_t_4384_,
    );
    return v___x_4387_;
}
pub unsafe fn l_Std_TreeMap_forM(
    mut v_00_u03b1_4388_: *mut LeanObject,
    mut v_00_u03b2_4389_: *mut LeanObject,
    mut v_cmp_4390_: *mut LeanObject,
    mut v_m_4391_: *mut LeanObject,
    mut v_inst_4392_: *mut LeanObject,
    mut v_f_4393_: *mut LeanObject,
    mut v_t_4394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    v___f_4395_ = lean_alloc_closure(
        l_Std_TreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4395_, 0, v_f_4393_);
    v___x_4396_ = lean_box(0);
    v___x_4397_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4392_,
        v___f_4395_,
        v___x_4396_,
        v_t_4394_,
    );
    return v___x_4397_;
}
pub unsafe fn l_Std_TreeMap_forM___boxed(
    mut v_00_u03b1_4398_: *mut LeanObject,
    mut v_00_u03b2_4399_: *mut LeanObject,
    mut v_cmp_4400_: *mut LeanObject,
    mut v_m_4401_: *mut LeanObject,
    mut v_inst_4402_: *mut LeanObject,
    mut v_f_4403_: *mut LeanObject,
    mut v_t_4404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4405_: *mut LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_Std_TreeMap_forM(
        v_00_u03b1_4398_,
        v_00_u03b2_4399_,
        v_cmp_4400_,
        v_m_4401_,
        v_inst_4402_,
        v_f_4403_,
        v_t_4404_,
    );
    lean_dec_ref(v_cmp_4400_);
    return v_res_4405_;
}
pub unsafe fn l_Std_TreeMap_forIn___redArg___lam__0(
    mut v_f_4406_: *mut LeanObject,
    mut v_a_4407_: *mut LeanObject,
    mut v_b_4408_: *mut LeanObject,
    mut v_c_4409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    v___x_4410_ = lean_apply_3(v_f_4406_, v_a_4407_, v_b_4408_, v_c_4409_);
    return v___x_4410_;
}
pub unsafe fn l_Std_TreeMap_forIn___redArg___lam__1(
    mut v_toPure_4411_: *mut LeanObject,
    mut v_____do__lift_4412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    v_a_4413_ = lean_ctor_get(v_____do__lift_4412_, 0);
    lean_inc(v_a_4413_);
    lean_dec_ref(v_____do__lift_4412_);
    v___x_4414_ = lean_apply_2(v_toPure_4411_, lean_box(0), v_a_4413_);
    return v___x_4414_;
}
pub unsafe fn l_Std_TreeMap_forIn___redArg(
    mut v_inst_4415_: *mut LeanObject,
    mut v_f_4416_: *mut LeanObject,
    mut v_init_4417_: *mut LeanObject,
    mut v_t_4418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4419_ = lean_ctor_get(v_inst_4415_, 0);
    v_toBind_4420_ = lean_ctor_get(v_inst_4415_, 1);
    lean_inc(v_toBind_4420_);
    v_toPure_4421_ = lean_ctor_get(v_toApplicative_4419_, 1);
    lean_inc(v_toPure_4421_);
    v___f_4422_ = lean_alloc_closure(
        l_Std_TreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4422_, 0, v_f_4416_);
    v___x_4423_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4415_,
        v___f_4422_,
        v_init_4417_,
        v_t_4418_,
    );
    v___f_4424_ = lean_alloc_closure(
        l_Std_TreeMap_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4424_, 0, v_toPure_4421_);
    v___x_4425_ = lean_apply_4(
        v_toBind_4420_,
        lean_box(0),
        lean_box(0),
        v___x_4423_,
        v___f_4424_,
    );
    return v___x_4425_;
}
pub unsafe fn l_Std_TreeMap_forIn(
    mut v_00_u03b1_4426_: *mut LeanObject,
    mut v_00_u03b2_4427_: *mut LeanObject,
    mut v_cmp_4428_: *mut LeanObject,
    mut v_00_u03b4_4429_: *mut LeanObject,
    mut v_m_4430_: *mut LeanObject,
    mut v_inst_4431_: *mut LeanObject,
    mut v_f_4432_: *mut LeanObject,
    mut v_init_4433_: *mut LeanObject,
    mut v_t_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4435_ = lean_ctor_get(v_inst_4431_, 0);
    v_toBind_4436_ = lean_ctor_get(v_inst_4431_, 1);
    lean_inc(v_toBind_4436_);
    v_toPure_4437_ = lean_ctor_get(v_toApplicative_4435_, 1);
    lean_inc(v_toPure_4437_);
    v___f_4438_ = lean_alloc_closure(
        l_Std_TreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4438_, 0, v_f_4432_);
    v___x_4439_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4431_,
        v___f_4438_,
        v_init_4433_,
        v_t_4434_,
    );
    v___f_4440_ = lean_alloc_closure(
        l_Std_TreeMap_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4440_, 0, v_toPure_4437_);
    v___x_4441_ = lean_apply_4(
        v_toBind_4436_,
        lean_box(0),
        lean_box(0),
        v___x_4439_,
        v___f_4440_,
    );
    return v___x_4441_;
}
pub unsafe fn l_Std_TreeMap_forIn___boxed(
    mut v_00_u03b1_4442_: *mut LeanObject,
    mut v_00_u03b2_4443_: *mut LeanObject,
    mut v_cmp_4444_: *mut LeanObject,
    mut v_00_u03b4_4445_: *mut LeanObject,
    mut v_m_4446_: *mut LeanObject,
    mut v_inst_4447_: *mut LeanObject,
    mut v_f_4448_: *mut LeanObject,
    mut v_init_4449_: *mut LeanObject,
    mut v_t_4450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4451_: *mut LeanObject = core::ptr::null_mut();
    v_res_4451_ = l_Std_TreeMap_forIn(
        v_00_u03b1_4442_,
        v_00_u03b2_4443_,
        v_cmp_4444_,
        v_00_u03b4_4445_,
        v_m_4446_,
        v_inst_4447_,
        v_f_4448_,
        v_init_4449_,
        v_t_4450_,
    );
    lean_dec_ref(v_cmp_4444_);
    return v_res_4451_;
}
pub unsafe fn l_Std_TreeMap_instForMProdOfMonad___redArg___lam__0(
    mut v_f_4452_: *mut LeanObject,
    mut v_x_4453_: *mut LeanObject,
    mut v_k_4454_: *mut LeanObject,
    mut v_v_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    v___x_4456_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4456_, 0, v_k_4454_);
    lean_ctor_set(v___x_4456_, 1, v_v_4455_);
    v___x_4457_ = lean_apply_1(v_f_4452_, v___x_4456_);
    return v___x_4457_;
}
pub unsafe fn l_Std_TreeMap_instForMProdOfMonad___redArg___lam__1(
    mut v_inst_4458_: *mut LeanObject,
    mut v_t_4459_: *mut LeanObject,
    mut v_f_4460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    v___f_4461_ = lean_alloc_closure(
        l_Std_TreeMap_instForMProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4461_, 0, v_f_4460_);
    v___x_4462_ = lean_box(0);
    v___x_4463_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4458_,
        v___f_4461_,
        v___x_4462_,
        v_t_4459_,
    );
    return v___x_4463_;
}
pub unsafe fn l_Std_TreeMap_instForMProdOfMonad___redArg(
    mut v_inst_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4465_: *mut LeanObject = core::ptr::null_mut();
    v___f_4465_ = lean_alloc_closure(
        l_Std_TreeMap_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4465_, 0, v_inst_4464_);
    return v___f_4465_;
}
pub unsafe fn l_Std_TreeMap_instForMProdOfMonad(
    mut v_00_u03b1_4466_: *mut LeanObject,
    mut v_00_u03b2_4467_: *mut LeanObject,
    mut v_cmp_4468_: *mut LeanObject,
    mut v_m_4469_: *mut LeanObject,
    mut v_inst_4470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4471_: *mut LeanObject = core::ptr::null_mut();
    v___f_4471_ = lean_alloc_closure(
        l_Std_TreeMap_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4471_, 0, v_inst_4470_);
    return v___f_4471_;
}
pub unsafe fn l_Std_TreeMap_instForMProdOfMonad___boxed(
    mut v_00_u03b1_4472_: *mut LeanObject,
    mut v_00_u03b2_4473_: *mut LeanObject,
    mut v_cmp_4474_: *mut LeanObject,
    mut v_m_4475_: *mut LeanObject,
    mut v_inst_4476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4477_: *mut LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Std_TreeMap_instForMProdOfMonad(
        v_00_u03b1_4472_,
        v_00_u03b2_4473_,
        v_cmp_4474_,
        v_m_4475_,
        v_inst_4476_,
    );
    lean_dec_ref(v_cmp_4474_);
    return v_res_4477_;
}
pub unsafe fn l_Std_TreeMap_instForInProdOfMonad___redArg___lam__0(
    mut v_f_4478_: *mut LeanObject,
    mut v_a_4479_: *mut LeanObject,
    mut v_b_4480_: *mut LeanObject,
    mut v_c_4481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    v___x_4482_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4482_, 0, v_a_4479_);
    lean_ctor_set(v___x_4482_, 1, v_b_4480_);
    v___x_4483_ = lean_apply_2(v_f_4478_, v___x_4482_, v_c_4481_);
    return v___x_4483_;
}
pub unsafe fn l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2(
    mut v_inst_4484_: *mut LeanObject,
    mut v_00_u03b2_4485_: *mut LeanObject,
    mut v_m_4486_: *mut LeanObject,
    mut v_init_4487_: *mut LeanObject,
    mut v_f_4488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4489_ = lean_ctor_get(v_inst_4484_, 0);
    v_toBind_4490_ = lean_ctor_get(v_inst_4484_, 1);
    lean_inc(v_toBind_4490_);
    v_toPure_4491_ = lean_ctor_get(v_toApplicative_4489_, 1);
    lean_inc(v_toPure_4491_);
    v___f_4492_ = lean_alloc_closure(
        l_Std_TreeMap_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4492_, 0, v_f_4488_);
    v___x_4493_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4484_,
        v___f_4492_,
        v_init_4487_,
        v_m_4486_,
    );
    v___f_4494_ = lean_alloc_closure(
        l_Std_TreeMap_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4494_, 0, v_toPure_4491_);
    v___x_4495_ = lean_apply_4(
        v_toBind_4490_,
        lean_box(0),
        lean_box(0),
        v___x_4493_,
        v___f_4494_,
    );
    return v___x_4495_;
}
pub unsafe fn l_Std_TreeMap_instForInProdOfMonad___redArg(
    mut v_inst_4496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4497_: *mut LeanObject = core::ptr::null_mut();
    v___f_4497_ = lean_alloc_closure(
        l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4497_, 0, v_inst_4496_);
    return v___f_4497_;
}
pub unsafe fn l_Std_TreeMap_instForInProdOfMonad(
    mut v_00_u03b1_4498_: *mut LeanObject,
    mut v_00_u03b2_4499_: *mut LeanObject,
    mut v_cmp_4500_: *mut LeanObject,
    mut v_m_4501_: *mut LeanObject,
    mut v_inst_4502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4503_: *mut LeanObject = core::ptr::null_mut();
    v___f_4503_ = lean_alloc_closure(
        l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4503_, 0, v_inst_4502_);
    return v___f_4503_;
}
pub unsafe fn l_Std_TreeMap_instForInProdOfMonad___boxed(
    mut v_00_u03b1_4504_: *mut LeanObject,
    mut v_00_u03b2_4505_: *mut LeanObject,
    mut v_cmp_4506_: *mut LeanObject,
    mut v_m_4507_: *mut LeanObject,
    mut v_inst_4508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4509_: *mut LeanObject = core::ptr::null_mut();
    v_res_4509_ = l_Std_TreeMap_instForInProdOfMonad(
        v_00_u03b1_4504_,
        v_00_u03b2_4505_,
        v_cmp_4506_,
        v_m_4507_,
        v_inst_4508_,
    );
    lean_dec_ref(v_cmp_4506_);
    return v_res_4509_;
}
pub unsafe fn l_Std_TreeMap_any___redArg___lam__0(
    mut v_p_4510_: *mut LeanObject,
    mut v___x_4511_: *mut LeanObject,
    mut v___x_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
    mut v_b_4514_: *mut LeanObject,
    mut v_acc_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: u8 = 0;
    v___x_4516_ = lean_apply_2(v_p_4510_, v_a_4513_, v_b_4514_);
    v___x_4517_ = (lean_unbox(v___x_4516_) as u8);
    if v___x_4517_ == 0 {
        let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
        v___x_4518_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4518_, 0, v___x_4511_);
        return v___x_4518_;
    } else {
        let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_4511_);
        v___x_4519_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4519_, 0, v___x_4516_);
        v___x_4520_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4520_, 0, v___x_4519_);
        lean_ctor_set(v___x_4520_, 1, v___x_4512_);
        v___x_4521_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4521_, 0, v___x_4520_);
        return v___x_4521_;
    }
}
pub unsafe fn l_Std_TreeMap_any___redArg___lam__0___boxed(
    mut v_p_4522_: *mut LeanObject,
    mut v___x_4523_: *mut LeanObject,
    mut v___x_4524_: *mut LeanObject,
    mut v_a_4525_: *mut LeanObject,
    mut v_b_4526_: *mut LeanObject,
    mut v_acc_4527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4528_: *mut LeanObject = core::ptr::null_mut();
    v_res_4528_ = l_Std_TreeMap_any___redArg___lam__0(
        v_p_4522_,
        v___x_4523_,
        v___x_4524_,
        v_a_4525_,
        v_b_4526_,
        v_acc_4527_,
    );
    lean_dec_ref(v_acc_4527_);
    return v_res_4528_;
}
pub unsafe fn l_Std_TreeMap_any___redArg(
    mut v_t_4532_: *mut LeanObject,
    mut v_p_4533_: *mut LeanObject,
) -> u8 {
    let mut v___y_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: u8 = 0;
    let mut v_val_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: u8 = 0;
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4540_ = l_Std_TreeMap_foldr___redArg___closed__9;
                v___x_4541_ = lean_box(0);
                v___x_4542_ = l_Std_TreeMap_any___redArg___closed__0;
                v___f_4543_ = lean_alloc_closure(
                    l_Std_TreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_4543_, 0, v_p_4533_);
                lean_closure_set(v___f_4543_, 1, v___x_4542_);
                lean_closure_set(v___f_4543_, 2, v___x_4541_);
                v___x_4544_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4540_,
                    v___f_4543_,
                    v___x_4542_,
                    v_t_4532_,
                );
                v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
                lean_inc(v_a_4545_);
                lean_dec(v___x_4544_);
                v___y_4535_ = v_a_4545_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4536_ = lean_ctor_get(v___y_4535_, 0);
                lean_inc(v_fst_4536_);
                lean_dec_ref(v___y_4535_);
                if lean_obj_tag(v_fst_4536_) == 0 {
                    v___x_4537_ = 0;
                    return v___x_4537_;
                } else {
                    v_val_4538_ = lean_ctor_get(v_fst_4536_, 0);
                    lean_inc(v_val_4538_);
                    lean_dec_ref_known(v_fst_4536_, 1);
                    v___x_4539_ = (lean_unbox(v_val_4538_) as u8);
                    lean_dec(v_val_4538_);
                    return v___x_4539_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_any___redArg___boxed(
    mut v_t_4546_: *mut LeanObject,
    mut v_p_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4548_: u8 = 0;
    let mut v_r_4549_: *mut LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Std_TreeMap_any___redArg(v_t_4546_, v_p_4547_);
    v_r_4549_ = lean_box((v_res_4548_) as usize);
    return v_r_4549_;
}
pub unsafe fn l_Std_TreeMap_any(
    mut v_00_u03b1_4550_: *mut LeanObject,
    mut v_00_u03b2_4551_: *mut LeanObject,
    mut v_cmp_4552_: *mut LeanObject,
    mut v_t_4553_: *mut LeanObject,
    mut v_p_4554_: *mut LeanObject,
) -> u8 {
    let mut v___y_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: u8 = 0;
    let mut v_val_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: u8 = 0;
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4561_ = l_Std_TreeMap_foldr___redArg___closed__9;
                v___x_4562_ = lean_box(0);
                v___x_4563_ = l_Std_TreeMap_any___redArg___closed__0;
                v___f_4564_ = lean_alloc_closure(
                    l_Std_TreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_4564_, 0, v_p_4554_);
                lean_closure_set(v___f_4564_, 1, v___x_4563_);
                lean_closure_set(v___f_4564_, 2, v___x_4562_);
                v___x_4565_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4561_,
                    v___f_4564_,
                    v___x_4563_,
                    v_t_4553_,
                );
                v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
                lean_inc(v_a_4566_);
                lean_dec(v___x_4565_);
                v___y_4556_ = v_a_4566_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4557_ = lean_ctor_get(v___y_4556_, 0);
                lean_inc(v_fst_4557_);
                lean_dec_ref(v___y_4556_);
                if lean_obj_tag(v_fst_4557_) == 0 {
                    v___x_4558_ = 0;
                    return v___x_4558_;
                } else {
                    v_val_4559_ = lean_ctor_get(v_fst_4557_, 0);
                    lean_inc(v_val_4559_);
                    lean_dec_ref_known(v_fst_4557_, 1);
                    v___x_4560_ = (lean_unbox(v_val_4559_) as u8);
                    lean_dec(v_val_4559_);
                    return v___x_4560_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_any___boxed(
    mut v_00_u03b1_4567_: *mut LeanObject,
    mut v_00_u03b2_4568_: *mut LeanObject,
    mut v_cmp_4569_: *mut LeanObject,
    mut v_t_4570_: *mut LeanObject,
    mut v_p_4571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4572_: u8 = 0;
    let mut v_r_4573_: *mut LeanObject = core::ptr::null_mut();
    v_res_4572_ = l_Std_TreeMap_any(
        v_00_u03b1_4567_,
        v_00_u03b2_4568_,
        v_cmp_4569_,
        v_t_4570_,
        v_p_4571_,
    );
    lean_dec_ref(v_cmp_4569_);
    v_r_4573_ = lean_box((v_res_4572_) as usize);
    return v_r_4573_;
}
pub unsafe fn l_Std_TreeMap_all___redArg___lam__0(
    mut v_p_4574_: *mut LeanObject,
    mut v___x_4575_: *mut LeanObject,
    mut v___x_4576_: *mut LeanObject,
    mut v_a_4577_: *mut LeanObject,
    mut v_b_4578_: *mut LeanObject,
    mut v_acc_4579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: u8 = 0;
    v___x_4580_ = lean_apply_2(v_p_4574_, v_a_4577_, v_b_4578_);
    v___x_4581_ = (lean_unbox(v___x_4580_) as u8);
    if v___x_4581_ == 0 {
        let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_4576_);
        v___x_4582_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4582_, 0, v___x_4580_);
        v___x_4583_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4583_, 0, v___x_4582_);
        lean_ctor_set(v___x_4583_, 1, v___x_4575_);
        v___x_4584_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4584_, 0, v___x_4583_);
        return v___x_4584_;
    } else {
        let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
        v___x_4585_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4585_, 0, v___x_4576_);
        return v___x_4585_;
    }
}
pub unsafe fn l_Std_TreeMap_all___redArg___lam__0___boxed(
    mut v_p_4586_: *mut LeanObject,
    mut v___x_4587_: *mut LeanObject,
    mut v___x_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
    mut v_b_4590_: *mut LeanObject,
    mut v_acc_4591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4592_: *mut LeanObject = core::ptr::null_mut();
    v_res_4592_ = l_Std_TreeMap_all___redArg___lam__0(
        v_p_4586_,
        v___x_4587_,
        v___x_4588_,
        v_a_4589_,
        v_b_4590_,
        v_acc_4591_,
    );
    lean_dec_ref(v_acc_4591_);
    return v_res_4592_;
}
pub unsafe fn l_Std_TreeMap_all___redArg(
    mut v_t_4593_: *mut LeanObject,
    mut v_p_4594_: *mut LeanObject,
) -> u8 {
    let mut v___y_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    let mut v_val_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: u8 = 0;
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4601_ = l_Std_TreeMap_foldr___redArg___closed__9;
                v___x_4602_ = lean_box(0);
                v___x_4603_ = l_Std_TreeMap_any___redArg___closed__0;
                v___f_4604_ = lean_alloc_closure(
                    l_Std_TreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_4604_, 0, v_p_4594_);
                lean_closure_set(v___f_4604_, 1, v___x_4602_);
                lean_closure_set(v___f_4604_, 2, v___x_4603_);
                v___x_4605_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4601_,
                    v___f_4604_,
                    v___x_4603_,
                    v_t_4593_,
                );
                v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
                lean_inc(v_a_4606_);
                lean_dec(v___x_4605_);
                v___y_4596_ = v_a_4606_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4597_ = lean_ctor_get(v___y_4596_, 0);
                lean_inc(v_fst_4597_);
                lean_dec_ref(v___y_4596_);
                if lean_obj_tag(v_fst_4597_) == 0 {
                    v___x_4598_ = 1;
                    return v___x_4598_;
                } else {
                    v_val_4599_ = lean_ctor_get(v_fst_4597_, 0);
                    lean_inc(v_val_4599_);
                    lean_dec_ref_known(v_fst_4597_, 1);
                    v___x_4600_ = (lean_unbox(v_val_4599_) as u8);
                    lean_dec(v_val_4599_);
                    return v___x_4600_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_all___redArg___boxed(
    mut v_t_4607_: *mut LeanObject,
    mut v_p_4608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4609_: u8 = 0;
    let mut v_r_4610_: *mut LeanObject = core::ptr::null_mut();
    v_res_4609_ = l_Std_TreeMap_all___redArg(v_t_4607_, v_p_4608_);
    v_r_4610_ = lean_box((v_res_4609_) as usize);
    return v_r_4610_;
}
pub unsafe fn l_Std_TreeMap_all(
    mut v_00_u03b1_4611_: *mut LeanObject,
    mut v_00_u03b2_4612_: *mut LeanObject,
    mut v_cmp_4613_: *mut LeanObject,
    mut v_t_4614_: *mut LeanObject,
    mut v_p_4615_: *mut LeanObject,
) -> u8 {
    let mut v___y_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: u8 = 0;
    let mut v_val_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4622_ = l_Std_TreeMap_foldr___redArg___closed__9;
                v___x_4623_ = lean_box(0);
                v___x_4624_ = l_Std_TreeMap_any___redArg___closed__0;
                v___f_4625_ = lean_alloc_closure(
                    l_Std_TreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_4625_, 0, v_p_4615_);
                lean_closure_set(v___f_4625_, 1, v___x_4623_);
                lean_closure_set(v___f_4625_, 2, v___x_4624_);
                v___x_4626_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4622_,
                    v___f_4625_,
                    v___x_4624_,
                    v_t_4614_,
                );
                v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
                lean_inc(v_a_4627_);
                lean_dec(v___x_4626_);
                v___y_4617_ = v_a_4627_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4618_ = lean_ctor_get(v___y_4617_, 0);
                lean_inc(v_fst_4618_);
                lean_dec_ref(v___y_4617_);
                if lean_obj_tag(v_fst_4618_) == 0 {
                    v___x_4619_ = 1;
                    return v___x_4619_;
                } else {
                    v_val_4620_ = lean_ctor_get(v_fst_4618_, 0);
                    lean_inc(v_val_4620_);
                    lean_dec_ref_known(v_fst_4618_, 1);
                    v___x_4621_ = (lean_unbox(v_val_4620_) as u8);
                    lean_dec(v_val_4620_);
                    return v___x_4621_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_all___boxed(
    mut v_00_u03b1_4628_: *mut LeanObject,
    mut v_00_u03b2_4629_: *mut LeanObject,
    mut v_cmp_4630_: *mut LeanObject,
    mut v_t_4631_: *mut LeanObject,
    mut v_p_4632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4633_: u8 = 0;
    let mut v_r_4634_: *mut LeanObject = core::ptr::null_mut();
    v_res_4633_ = l_Std_TreeMap_all(
        v_00_u03b1_4628_,
        v_00_u03b2_4629_,
        v_cmp_4630_,
        v_t_4631_,
        v_p_4632_,
    );
    lean_dec_ref(v_cmp_4630_);
    v_r_4634_ = lean_box((v_res_4633_) as usize);
    return v_r_4634_;
}
pub unsafe fn l_Std_TreeMap_keys___redArg___lam__0(
    mut v_x1_4635_: *mut LeanObject,
    mut v_x2_4636_: *mut LeanObject,
    mut v_x3_4637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    v___x_4638_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4638_, 0, v_x1_4635_);
    lean_ctor_set(v___x_4638_, 1, v_x3_4637_);
    return v___x_4638_;
}
pub unsafe fn l_Std_TreeMap_keys___redArg___lam__0___boxed(
    mut v_x1_4639_: *mut LeanObject,
    mut v_x2_4640_: *mut LeanObject,
    mut v_x3_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4642_: *mut LeanObject = core::ptr::null_mut();
    v_res_4642_ = l_Std_TreeMap_keys___redArg___lam__0(v_x1_4639_, v_x2_4640_, v_x3_4641_);
    lean_dec(v_x2_4640_);
    return v_res_4642_;
}
pub unsafe fn l_Std_TreeMap_keys___redArg(mut v_t_4644_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    v___f_4645_ = l_Std_TreeMap_keys___redArg___closed__0;
    v___x_4646_ = lean_box(0);
    v___x_4647_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4648_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4647_,
        v___f_4645_,
        v___x_4646_,
        v_t_4644_,
    );
    return v___x_4648_;
}
pub unsafe fn l_Std_TreeMap_keys(
    mut v_00_u03b1_4649_: *mut LeanObject,
    mut v_00_u03b2_4650_: *mut LeanObject,
    mut v_cmp_4651_: *mut LeanObject,
    mut v_t_4652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    v___f_4653_ = l_Std_TreeMap_keys___redArg___closed__0;
    v___x_4654_ = lean_box(0);
    v___x_4655_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4656_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4655_,
        v___f_4653_,
        v___x_4654_,
        v_t_4652_,
    );
    return v___x_4656_;
}
pub unsafe fn l_Std_TreeMap_keys___boxed(
    mut v_00_u03b1_4657_: *mut LeanObject,
    mut v_00_u03b2_4658_: *mut LeanObject,
    mut v_cmp_4659_: *mut LeanObject,
    mut v_t_4660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4661_: *mut LeanObject = core::ptr::null_mut();
    v_res_4661_ = l_Std_TreeMap_keys(v_00_u03b1_4657_, v_00_u03b2_4658_, v_cmp_4659_, v_t_4660_);
    lean_dec_ref(v_cmp_4659_);
    return v_res_4661_;
}
pub unsafe fn l_Std_TreeMap_keysArray___redArg___lam__0(
    mut v_l_4662_: *mut LeanObject,
    mut v_k_4663_: *mut LeanObject,
    mut v_x_4664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    v___x_4665_ = lean_array_push(v_l_4662_, v_k_4663_);
    return v___x_4665_;
}
pub unsafe fn l_Std_TreeMap_keysArray___redArg___lam__0___boxed(
    mut v_l_4666_: *mut LeanObject,
    mut v_k_4667_: *mut LeanObject,
    mut v_x_4668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4669_: *mut LeanObject = core::ptr::null_mut();
    v_res_4669_ = l_Std_TreeMap_keysArray___redArg___lam__0(v_l_4666_, v_k_4667_, v_x_4668_);
    lean_dec(v_x_4668_);
    return v_res_4669_;
}
pub unsafe fn l_Std_TreeMap_keysArray___redArg(mut v_t_4671_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4672_ = l_Std_TreeMap_keysArray___redArg___closed__0;
                if lean_obj_tag(v_t_4671_) == 0 {
                    v_size_4677_ = lean_ctor_get(v_t_4671_, 0);
                    lean_inc(v_size_4677_);
                    v___y_4674_ = v_size_4677_;
                    state = 1;
                    continue;
                } else {
                    v___x_4678_ = lean_unsigned_to_nat(0);
                    v___y_4674_ = v___x_4678_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4675_ = lean_mk_empty_array_with_capacity(v___y_4674_);
                lean_dec(v___y_4674_);
                v___x_4676_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4672_,
                    v___x_4675_,
                    v_t_4671_,
                );
                return v___x_4676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_keysArray(
    mut v_00_u03b1_4679_: *mut LeanObject,
    mut v_00_u03b2_4680_: *mut LeanObject,
    mut v_cmp_4681_: *mut LeanObject,
    mut v_t_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4683_ = l_Std_TreeMap_keysArray___redArg___closed__0;
                if lean_obj_tag(v_t_4682_) == 0 {
                    v_size_4688_ = lean_ctor_get(v_t_4682_, 0);
                    lean_inc(v_size_4688_);
                    v___y_4685_ = v_size_4688_;
                    state = 1;
                    continue;
                } else {
                    v___x_4689_ = lean_unsigned_to_nat(0);
                    v___y_4685_ = v___x_4689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4686_ = lean_mk_empty_array_with_capacity(v___y_4685_);
                lean_dec(v___y_4685_);
                v___x_4687_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4683_,
                    v___x_4686_,
                    v_t_4682_,
                );
                return v___x_4687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_keysArray___boxed(
    mut v_00_u03b1_4690_: *mut LeanObject,
    mut v_00_u03b2_4691_: *mut LeanObject,
    mut v_cmp_4692_: *mut LeanObject,
    mut v_t_4693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4694_: *mut LeanObject = core::ptr::null_mut();
    v_res_4694_ =
        l_Std_TreeMap_keysArray(v_00_u03b1_4690_, v_00_u03b2_4691_, v_cmp_4692_, v_t_4693_);
    lean_dec_ref(v_cmp_4692_);
    return v_res_4694_;
}
pub unsafe fn l_Std_TreeMap_values___redArg___lam__0(
    mut v_x1_4695_: *mut LeanObject,
    mut v_x2_4696_: *mut LeanObject,
    mut v_x3_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    v___x_4698_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4698_, 0, v_x2_4696_);
    lean_ctor_set(v___x_4698_, 1, v_x3_4697_);
    return v___x_4698_;
}
pub unsafe fn l_Std_TreeMap_values___redArg___lam__0___boxed(
    mut v_x1_4699_: *mut LeanObject,
    mut v_x2_4700_: *mut LeanObject,
    mut v_x3_4701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4702_: *mut LeanObject = core::ptr::null_mut();
    v_res_4702_ = l_Std_TreeMap_values___redArg___lam__0(v_x1_4699_, v_x2_4700_, v_x3_4701_);
    lean_dec(v_x1_4699_);
    return v_res_4702_;
}
pub unsafe fn l_Std_TreeMap_values___redArg(mut v_t_4704_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    v___f_4705_ = l_Std_TreeMap_values___redArg___closed__0;
    v___x_4706_ = lean_box(0);
    v___x_4707_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4708_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4707_,
        v___f_4705_,
        v___x_4706_,
        v_t_4704_,
    );
    return v___x_4708_;
}
pub unsafe fn l_Std_TreeMap_values(
    mut v_00_u03b1_4709_: *mut LeanObject,
    mut v_00_u03b2_4710_: *mut LeanObject,
    mut v_cmp_4711_: *mut LeanObject,
    mut v_t_4712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    v___f_4713_ = l_Std_TreeMap_values___redArg___closed__0;
    v___x_4714_ = lean_box(0);
    v___x_4715_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4716_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4715_,
        v___f_4713_,
        v___x_4714_,
        v_t_4712_,
    );
    return v___x_4716_;
}
pub unsafe fn l_Std_TreeMap_values___boxed(
    mut v_00_u03b1_4717_: *mut LeanObject,
    mut v_00_u03b2_4718_: *mut LeanObject,
    mut v_cmp_4719_: *mut LeanObject,
    mut v_t_4720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4721_: *mut LeanObject = core::ptr::null_mut();
    v_res_4721_ = l_Std_TreeMap_values(v_00_u03b1_4717_, v_00_u03b2_4718_, v_cmp_4719_, v_t_4720_);
    lean_dec_ref(v_cmp_4719_);
    return v_res_4721_;
}
pub unsafe fn l_Std_TreeMap_valuesArray___redArg___lam__0(
    mut v_l_4722_: *mut LeanObject,
    mut v_x_4723_: *mut LeanObject,
    mut v_v_4724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    v___x_4725_ = lean_array_push(v_l_4722_, v_v_4724_);
    return v___x_4725_;
}
pub unsafe fn l_Std_TreeMap_valuesArray___redArg___lam__0___boxed(
    mut v_l_4726_: *mut LeanObject,
    mut v_x_4727_: *mut LeanObject,
    mut v_v_4728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4729_: *mut LeanObject = core::ptr::null_mut();
    v_res_4729_ = l_Std_TreeMap_valuesArray___redArg___lam__0(v_l_4726_, v_x_4727_, v_v_4728_);
    lean_dec(v_x_4727_);
    return v_res_4729_;
}
pub unsafe fn l_Std_TreeMap_valuesArray___redArg(
    mut v_t_4731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4732_ = l_Std_TreeMap_valuesArray___redArg___closed__0;
                if lean_obj_tag(v_t_4731_) == 0 {
                    v_size_4737_ = lean_ctor_get(v_t_4731_, 0);
                    lean_inc(v_size_4737_);
                    v___y_4734_ = v_size_4737_;
                    state = 1;
                    continue;
                } else {
                    v___x_4738_ = lean_unsigned_to_nat(0);
                    v___y_4734_ = v___x_4738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4735_ = lean_mk_empty_array_with_capacity(v___y_4734_);
                lean_dec(v___y_4734_);
                v___x_4736_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4732_,
                    v___x_4735_,
                    v_t_4731_,
                );
                return v___x_4736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_valuesArray(
    mut v_00_u03b1_4739_: *mut LeanObject,
    mut v_00_u03b2_4740_: *mut LeanObject,
    mut v_cmp_4741_: *mut LeanObject,
    mut v_t_4742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4743_ = l_Std_TreeMap_valuesArray___redArg___closed__0;
                if lean_obj_tag(v_t_4742_) == 0 {
                    v_size_4748_ = lean_ctor_get(v_t_4742_, 0);
                    lean_inc(v_size_4748_);
                    v___y_4745_ = v_size_4748_;
                    state = 1;
                    continue;
                } else {
                    v___x_4749_ = lean_unsigned_to_nat(0);
                    v___y_4745_ = v___x_4749_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4746_ = lean_mk_empty_array_with_capacity(v___y_4745_);
                lean_dec(v___y_4745_);
                v___x_4747_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4743_,
                    v___x_4746_,
                    v_t_4742_,
                );
                return v___x_4747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_valuesArray___boxed(
    mut v_00_u03b1_4750_: *mut LeanObject,
    mut v_00_u03b2_4751_: *mut LeanObject,
    mut v_cmp_4752_: *mut LeanObject,
    mut v_t_4753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4754_: *mut LeanObject = core::ptr::null_mut();
    v_res_4754_ =
        l_Std_TreeMap_valuesArray(v_00_u03b1_4750_, v_00_u03b2_4751_, v_cmp_4752_, v_t_4753_);
    lean_dec_ref(v_cmp_4752_);
    return v_res_4754_;
}
pub unsafe fn l_Std_TreeMap_toList___redArg___lam__0(
    mut v_x1_4755_: *mut LeanObject,
    mut v_x2_4756_: *mut LeanObject,
    mut v_x3_4757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    v___x_4758_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4758_, 0, v_x1_4755_);
    lean_ctor_set(v___x_4758_, 1, v_x2_4756_);
    v___x_4759_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4759_, 0, v___x_4758_);
    lean_ctor_set(v___x_4759_, 1, v_x3_4757_);
    return v___x_4759_;
}
pub unsafe fn l_Std_TreeMap_toList___redArg(mut v_t_4761_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    v___f_4762_ = l_Std_TreeMap_toList___redArg___closed__0;
    v___x_4763_ = lean_box(0);
    v___x_4764_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4765_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4764_,
        v___f_4762_,
        v___x_4763_,
        v_t_4761_,
    );
    return v___x_4765_;
}
pub unsafe fn l_Std_TreeMap_toList(
    mut v_00_u03b1_4766_: *mut LeanObject,
    mut v_00_u03b2_4767_: *mut LeanObject,
    mut v_cmp_4768_: *mut LeanObject,
    mut v_t_4769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    v___f_4770_ = l_Std_TreeMap_toList___redArg___closed__0;
    v___x_4771_ = lean_box(0);
    v___x_4772_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_4773_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4772_,
        v___f_4770_,
        v___x_4771_,
        v_t_4769_,
    );
    return v___x_4773_;
}
pub unsafe fn l_Std_TreeMap_toList___boxed(
    mut v_00_u03b1_4774_: *mut LeanObject,
    mut v_00_u03b2_4775_: *mut LeanObject,
    mut v_cmp_4776_: *mut LeanObject,
    mut v_t_4777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4778_: *mut LeanObject = core::ptr::null_mut();
    v_res_4778_ = l_Std_TreeMap_toList(v_00_u03b1_4774_, v_00_u03b2_4775_, v_cmp_4776_, v_t_4777_);
    lean_dec_ref(v_cmp_4776_);
    return v_res_4778_;
}
pub unsafe fn _init_l_Std_TreeMap_ofList___auto__1() -> *mut LeanObject {
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    v___x_4779_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26_once),
        _init_l_Std_TreeMap___auto__1___closed__26,
    );
    return v___x_4779_;
}
pub unsafe fn l_Std_TreeMap_ofList___redArg___lam__0(
    mut v_cmp_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_x_4782_: *mut LeanObject,
    mut v___y_4783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4784_ = lean_ctor_get(v_a_4781_, 0);
    lean_inc(v_fst_4784_);
    v_snd_4785_ = lean_ctor_get(v_a_4781_, 1);
    lean_inc(v_snd_4785_);
    lean_dec_ref(v_a_4781_);
    v_r_4786_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_4780_,
        v_fst_4784_,
        v_snd_4785_,
        v___y_4783_,
    );
    v___x_4787_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4787_, 0, v_r_4786_);
    return v___x_4787_;
}
pub unsafe fn l_Std_TreeMap_ofList___redArg(
    mut v_l_4788_: *mut LeanObject,
    mut v_cmp_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    v___f_4790_ = lean_alloc_closure(
        l_Std_TreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4790_, 0, v_cmp_4789_);
    v___x_4791_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4792_ = lean_box(1);
    v___x_4793_ = l_List_forIn_x27_loop___redArg(v___x_4791_, v___f_4790_, v_l_4788_, v_r_4792_);
    return v___x_4793_;
}
pub unsafe fn l_Std_TreeMap_ofList___redArg___boxed(
    mut v_l_4794_: *mut LeanObject,
    mut v_cmp_4795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4796_: *mut LeanObject = core::ptr::null_mut();
    v_res_4796_ = l_Std_TreeMap_ofList___redArg(v_l_4794_, v_cmp_4795_);
    lean_dec(v_l_4794_);
    return v_res_4796_;
}
pub unsafe fn l_Std_TreeMap_ofList(
    mut v_00_u03b1_4797_: *mut LeanObject,
    mut v_00_u03b2_4798_: *mut LeanObject,
    mut v_l_4799_: *mut LeanObject,
    mut v_cmp_4800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    v___f_4801_ = lean_alloc_closure(
        l_Std_TreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4801_, 0, v_cmp_4800_);
    v___x_4802_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4803_ = lean_box(1);
    v___x_4804_ = l_List_forIn_x27_loop___redArg(v___x_4802_, v___f_4801_, v_l_4799_, v_r_4803_);
    return v___x_4804_;
}
pub unsafe fn l_Std_TreeMap_ofList___boxed(
    mut v_00_u03b1_4805_: *mut LeanObject,
    mut v_00_u03b2_4806_: *mut LeanObject,
    mut v_l_4807_: *mut LeanObject,
    mut v_cmp_4808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4809_: *mut LeanObject = core::ptr::null_mut();
    v_res_4809_ = l_Std_TreeMap_ofList(v_00_u03b1_4805_, v_00_u03b2_4806_, v_l_4807_, v_cmp_4808_);
    lean_dec(v_l_4807_);
    return v_res_4809_;
}
pub unsafe fn _init_l_Std_TreeMap_unitOfList___auto__1() -> *mut LeanObject {
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    v___x_4810_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26_once),
        _init_l_Std_TreeMap___auto__1___closed__26,
    );
    return v___x_4810_;
}
pub unsafe fn l_Std_TreeMap_unitOfList___redArg___lam__0(
    mut v_cmp_4811_: *mut LeanObject,
    mut v_a_4812_: *mut LeanObject,
    mut v_x_4813_: *mut LeanObject,
    mut v___y_4814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4815_: u8 = 0;
    lean_inc(v___y_4814_);
    lean_inc(v_a_4812_);
    lean_inc_ref(v_cmp_4811_);
    v___x_4815_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4811_, v_a_4812_, v___y_4814_);
    if v___x_4815_ == 0 {
        let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
        v___x_4816_ = lean_box(0);
        v___x_4817_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4811_,
            v_a_4812_,
            v___x_4816_,
            v___y_4814_,
        );
        v___x_4818_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4818_, 0, v___x_4817_);
        return v___x_4818_;
    } else {
        let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_4812_);
        lean_dec_ref(v_cmp_4811_);
        v___x_4819_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4819_, 0, v___y_4814_);
        return v___x_4819_;
    }
}
pub unsafe fn l_Std_TreeMap_unitOfList___redArg(
    mut v_l_4820_: *mut LeanObject,
    mut v_cmp_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    v___f_4822_ = lean_alloc_closure(
        l_Std_TreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4822_, 0, v_cmp_4821_);
    v___x_4823_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4824_ = lean_box(1);
    v___x_4825_ = l_List_forIn_x27_loop___redArg(v___x_4823_, v___f_4822_, v_l_4820_, v_r_4824_);
    return v___x_4825_;
}
pub unsafe fn l_Std_TreeMap_unitOfList___redArg___boxed(
    mut v_l_4826_: *mut LeanObject,
    mut v_cmp_4827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4828_: *mut LeanObject = core::ptr::null_mut();
    v_res_4828_ = l_Std_TreeMap_unitOfList___redArg(v_l_4826_, v_cmp_4827_);
    lean_dec(v_l_4826_);
    return v_res_4828_;
}
pub unsafe fn l_Std_TreeMap_unitOfList(
    mut v_00_u03b1_4829_: *mut LeanObject,
    mut v_l_4830_: *mut LeanObject,
    mut v_cmp_4831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    v___f_4832_ = lean_alloc_closure(
        l_Std_TreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4832_, 0, v_cmp_4831_);
    v___x_4833_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4834_ = lean_box(1);
    v___x_4835_ = l_List_forIn_x27_loop___redArg(v___x_4833_, v___f_4832_, v_l_4830_, v_r_4834_);
    return v___x_4835_;
}
pub unsafe fn l_Std_TreeMap_unitOfList___boxed(
    mut v_00_u03b1_4836_: *mut LeanObject,
    mut v_l_4837_: *mut LeanObject,
    mut v_cmp_4838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4839_: *mut LeanObject = core::ptr::null_mut();
    v_res_4839_ = l_Std_TreeMap_unitOfList(v_00_u03b1_4836_, v_l_4837_, v_cmp_4838_);
    lean_dec(v_l_4837_);
    return v_res_4839_;
}
pub unsafe fn l_Std_TreeMap_toArray___redArg___lam__0(
    mut v_acc_4840_: *mut LeanObject,
    mut v_k_4841_: *mut LeanObject,
    mut v_v_4842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    v___x_4843_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4843_, 0, v_k_4841_);
    lean_ctor_set(v___x_4843_, 1, v_v_4842_);
    v___x_4844_ = lean_array_push(v_acc_4840_, v___x_4843_);
    return v___x_4844_;
}
pub unsafe fn l_Std_TreeMap_toArray___redArg(mut v_t_4848_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___f_4849_ = l_Std_TreeMap_toArray___redArg___closed__0;
    v___x_4850_ = l_Std_TreeMap_toArray___redArg___closed__1;
    v___x_4851_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_4849_, v___x_4850_, v_t_4848_);
    return v___x_4851_;
}
pub unsafe fn l_Std_TreeMap_toArray(
    mut v_00_u03b1_4852_: *mut LeanObject,
    mut v_00_u03b2_4853_: *mut LeanObject,
    mut v_cmp_4854_: *mut LeanObject,
    mut v_t_4855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    v___f_4856_ = l_Std_TreeMap_toArray___redArg___closed__0;
    v___x_4857_ = l_Std_TreeMap_toArray___redArg___closed__1;
    v___x_4858_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_4856_, v___x_4857_, v_t_4855_);
    return v___x_4858_;
}
pub unsafe fn l_Std_TreeMap_toArray___boxed(
    mut v_00_u03b1_4859_: *mut LeanObject,
    mut v_00_u03b2_4860_: *mut LeanObject,
    mut v_cmp_4861_: *mut LeanObject,
    mut v_t_4862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4863_: *mut LeanObject = core::ptr::null_mut();
    v_res_4863_ = l_Std_TreeMap_toArray(v_00_u03b1_4859_, v_00_u03b2_4860_, v_cmp_4861_, v_t_4862_);
    lean_dec_ref(v_cmp_4861_);
    return v_res_4863_;
}
pub unsafe fn _init_l_Std_TreeMap_ofArray___auto__1() -> *mut LeanObject {
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    v___x_4864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26_once),
        _init_l_Std_TreeMap___auto__1___closed__26,
    );
    return v___x_4864_;
}
pub unsafe fn l_Std_TreeMap_ofArray___redArg(
    mut v_a_4865_: *mut LeanObject,
    mut v_cmp_4866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4870_: usize = 0;
    let mut v___x_4871_: usize = 0;
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    v___f_4867_ = lean_alloc_closure(
        l_Std_TreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4867_, 0, v_cmp_4866_);
    v___x_4868_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4869_ = lean_box(1);
    v_sz_4870_ = lean_array_size(v_a_4865_);
    v___x_4871_ = 0usize;
    v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_4868_,
        v_a_4865_,
        v___f_4867_,
        v_sz_4870_,
        v___x_4871_,
        v_r_4869_,
    );
    return v___x_4872_;
}
pub unsafe fn l_Std_TreeMap_ofArray(
    mut v_00_u03b1_4873_: *mut LeanObject,
    mut v_00_u03b2_4874_: *mut LeanObject,
    mut v_a_4875_: *mut LeanObject,
    mut v_cmp_4876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4880_: usize = 0;
    let mut v___x_4881_: usize = 0;
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    v___f_4877_ = lean_alloc_closure(
        l_Std_TreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4877_, 0, v_cmp_4876_);
    v___x_4878_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4879_ = lean_box(1);
    v_sz_4880_ = lean_array_size(v_a_4875_);
    v___x_4881_ = 0usize;
    v___x_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_4878_,
        v_a_4875_,
        v___f_4877_,
        v_sz_4880_,
        v___x_4881_,
        v_r_4879_,
    );
    return v___x_4882_;
}
pub unsafe fn _init_l_Std_TreeMap_unitOfArray___auto__1() -> *mut LeanObject {
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    v___x_4883_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap___auto__1___closed__26_once),
        _init_l_Std_TreeMap___auto__1___closed__26,
    );
    return v___x_4883_;
}
pub unsafe fn l_Std_TreeMap_unitOfArray___redArg(
    mut v_a_4884_: *mut LeanObject,
    mut v_cmp_4885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4889_: usize = 0;
    let mut v___x_4890_: usize = 0;
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v___f_4886_ = lean_alloc_closure(
        l_Std_TreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4886_, 0, v_cmp_4885_);
    v___x_4887_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4888_ = lean_box(1);
    v_sz_4889_ = lean_array_size(v_a_4884_);
    v___x_4890_ = 0usize;
    v___x_4891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_4887_,
        v_a_4884_,
        v___f_4886_,
        v_sz_4889_,
        v___x_4890_,
        v_r_4888_,
    );
    return v___x_4891_;
}
pub unsafe fn l_Std_TreeMap_unitOfArray(
    mut v_00_u03b1_4892_: *mut LeanObject,
    mut v_a_4893_: *mut LeanObject,
    mut v_cmp_4894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4898_: usize = 0;
    let mut v___x_4899_: usize = 0;
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    v___f_4895_ = lean_alloc_closure(
        l_Std_TreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4895_, 0, v_cmp_4894_);
    v___x_4896_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v_r_4897_ = lean_box(1);
    v_sz_4898_ = lean_array_size(v_a_4893_);
    v___x_4899_ = 0usize;
    v___x_4900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_4896_,
        v_a_4893_,
        v___f_4895_,
        v_sz_4898_,
        v___x_4899_,
        v_r_4897_,
    );
    return v___x_4900_;
}
pub unsafe fn l_Std_TreeMap_modify___redArg(
    mut v_cmp_4901_: *mut LeanObject,
    mut v_t_4902_: *mut LeanObject,
    mut v_a_4903_: *mut LeanObject,
    mut v_f_4904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    v___x_4905_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_4901_,
        v_a_4903_,
        v_f_4904_,
        v_t_4902_,
    );
    return v___x_4905_;
}
pub unsafe fn l_Std_TreeMap_modify(
    mut v_00_u03b1_4906_: *mut LeanObject,
    mut v_00_u03b2_4907_: *mut LeanObject,
    mut v_cmp_4908_: *mut LeanObject,
    mut v_t_4909_: *mut LeanObject,
    mut v_a_4910_: *mut LeanObject,
    mut v_f_4911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    v___x_4912_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_4908_,
        v_a_4910_,
        v_f_4911_,
        v_t_4909_,
    );
    return v___x_4912_;
}
pub unsafe fn l_Std_TreeMap_alter___redArg(
    mut v_cmp_4913_: *mut LeanObject,
    mut v_t_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_f_4916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    v___x_4917_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_4913_,
        v_a_4915_,
        v_f_4916_,
        v_t_4914_,
    );
    return v___x_4917_;
}
pub unsafe fn l_Std_TreeMap_alter(
    mut v_00_u03b1_4918_: *mut LeanObject,
    mut v_00_u03b2_4919_: *mut LeanObject,
    mut v_cmp_4920_: *mut LeanObject,
    mut v_t_4921_: *mut LeanObject,
    mut v_a_4922_: *mut LeanObject,
    mut v_f_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    v___x_4924_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_4920_,
        v_a_4922_,
        v_f_4923_,
        v_t_4921_,
    );
    return v___x_4924_;
}
pub unsafe fn l_Std_TreeMap_mergeWith___redArg___lam__0(
    mut v_b_u2082_4925_: *mut LeanObject,
    mut v_mergeFn_4926_: *mut LeanObject,
    mut v_a_4927_: *mut LeanObject,
    mut v_x_4928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4928_) == 0 {
                    lean_dec(v_a_4927_);
                    lean_dec(v_mergeFn_4926_);
                    v___x_4929_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4929_, 0, v_b_u2082_4925_);
                    return v___x_4929_;
                } else {
                    v_val_4930_ = lean_ctor_get(v_x_4928_, 0);
                    v_isSharedCheck_4938_ = (!lean_is_exclusive(v_x_4928_)) as u8;
                    if v_isSharedCheck_4938_ == 0 {
                        v___x_4932_ = v_x_4928_;
                        v_isShared_4933_ = v_isSharedCheck_4938_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4930_);
                        lean_dec(v_x_4928_);
                        v___x_4932_ = lean_box(0);
                        v_isShared_4933_ = v_isSharedCheck_4938_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4934_ =
                    lean_apply_3(v_mergeFn_4926_, v_a_4927_, v_val_4930_, v_b_u2082_4925_);
                if v_isShared_4933_ == 0 {
                    lean_ctor_set(v___x_4932_, 0, v___x_4934_);
                    v___x_4936_ = v___x_4932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_mergeWith___redArg___lam__1(
    mut v_mergeFn_4939_: *mut LeanObject,
    mut v_cmp_4940_: *mut LeanObject,
    mut v_t_4941_: *mut LeanObject,
    mut v_a_4942_: *mut LeanObject,
    mut v_b_u2082_4943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4942_);
    v___f_4944_ = lean_alloc_closure(
        l_Std_TreeMap_mergeWith___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4944_, 0, v_b_u2082_4943_);
    lean_closure_set(v___f_4944_, 1, v_mergeFn_4939_);
    lean_closure_set(v___f_4944_, 2, v_a_4942_);
    v___x_4945_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_4940_,
        v_a_4942_,
        v___f_4944_,
        v_t_4941_,
    );
    return v___x_4945_;
}
pub unsafe fn l_Std_TreeMap_mergeWith___redArg(
    mut v_cmp_4946_: *mut LeanObject,
    mut v_mergeFn_4947_: *mut LeanObject,
    mut v_t_u2081_4948_: *mut LeanObject,
    mut v_t_u2082_4949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    v___f_4950_ = lean_alloc_closure(
        l_Std_TreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_4950_, 0, v_mergeFn_4947_);
    lean_closure_set(v___f_4950_, 1, v_cmp_4946_);
    v___x_4951_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_4950_, v_t_u2081_4948_, v_t_u2082_4949_);
    return v___x_4951_;
}
pub unsafe fn l_Std_TreeMap_mergeWith(
    mut v_00_u03b1_4952_: *mut LeanObject,
    mut v_00_u03b2_4953_: *mut LeanObject,
    mut v_cmp_4954_: *mut LeanObject,
    mut v_mergeFn_4955_: *mut LeanObject,
    mut v_t_u2081_4956_: *mut LeanObject,
    mut v_t_u2082_4957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    v___f_4958_ = lean_alloc_closure(
        l_Std_TreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_4958_, 0, v_mergeFn_4955_);
    lean_closure_set(v___f_4958_, 1, v_cmp_4954_);
    v___x_4959_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_4958_, v_t_u2081_4956_, v_t_u2082_4957_);
    return v___x_4959_;
}
pub unsafe fn l_Std_TreeMap_insertMany___redArg___lam__0(
    mut v_cmp_4960_: *mut LeanObject,
    mut v_x_4961_: *mut LeanObject,
    mut v_____s_4962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4963_ = lean_ctor_get(v_x_4961_, 0);
    lean_inc(v_fst_4963_);
    v_snd_4964_ = lean_ctor_get(v_x_4961_, 1);
    lean_inc(v_snd_4964_);
    lean_dec_ref(v_x_4961_);
    v_r_4965_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_4960_,
        v_fst_4963_,
        v_snd_4964_,
        v_____s_4962_,
    );
    v___x_4966_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4966_, 0, v_r_4965_);
    return v___x_4966_;
}
pub unsafe fn l_Std_TreeMap_insertMany___redArg(
    mut v_cmp_4967_: *mut LeanObject,
    mut v_inst_4968_: *mut LeanObject,
    mut v_t_4969_: *mut LeanObject,
    mut v_l_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    v___f_4971_ = lean_alloc_closure(
        l_Std_TreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4971_, 0, v_cmp_4967_);
    v___x_4972_ = lean_apply_4(v_inst_4968_, lean_box(0), v_l_4970_, v_t_4969_, v___f_4971_);
    return v___x_4972_;
}
pub unsafe fn l_Std_TreeMap_insertMany(
    mut v_00_u03b1_4973_: *mut LeanObject,
    mut v_00_u03b2_4974_: *mut LeanObject,
    mut v_cmp_4975_: *mut LeanObject,
    mut v_00_u03c1_4976_: *mut LeanObject,
    mut v_inst_4977_: *mut LeanObject,
    mut v_t_4978_: *mut LeanObject,
    mut v_l_4979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    v___f_4980_ = lean_alloc_closure(
        l_Std_TreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4980_, 0, v_cmp_4975_);
    v___x_4981_ = lean_apply_4(v_inst_4977_, lean_box(0), v_l_4979_, v_t_4978_, v___f_4980_);
    return v___x_4981_;
}
pub unsafe fn l_Std_TreeMap_union___redArg(
    mut v_cmp_4982_: *mut LeanObject,
    mut v_t_u2081_4983_: *mut LeanObject,
    mut v_t_u2082_4984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    v___x_4985_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_4982_,
        v_t_u2081_4983_,
        v_t_u2082_4984_,
    );
    return v___x_4985_;
}
pub unsafe fn l_Std_TreeMap_union(
    mut v_00_u03b1_4986_: *mut LeanObject,
    mut v_00_u03b2_4987_: *mut LeanObject,
    mut v_cmp_4988_: *mut LeanObject,
    mut v_t_u2081_4989_: *mut LeanObject,
    mut v_t_u2082_4990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    v___x_4991_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_4988_,
        v_t_u2081_4989_,
        v_t_u2082_4990_,
    );
    return v___x_4991_;
}
pub unsafe fn l_Std_TreeMap_instUnion___redArg(
    mut v_cmp_4992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    v___x_4993_ = lean_alloc_closure(l_Std_TreeMap_union as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_4993_, 0, lean_box(0));
    lean_closure_set(v___x_4993_, 1, lean_box(0));
    lean_closure_set(v___x_4993_, 2, v_cmp_4992_);
    return v___x_4993_;
}
pub unsafe fn l_Std_TreeMap_instUnion(
    mut v_00_u03b1_4994_: *mut LeanObject,
    mut v_00_u03b2_4995_: *mut LeanObject,
    mut v_cmp_4996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    v___x_4997_ = lean_alloc_closure(l_Std_TreeMap_union as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_4997_, 0, lean_box(0));
    lean_closure_set(v___x_4997_, 1, lean_box(0));
    lean_closure_set(v___x_4997_, 2, v_cmp_4996_);
    return v___x_4997_;
}
pub unsafe fn l_Std_TreeMap_inter___redArg(
    mut v_cmp_4998_: *mut LeanObject,
    mut v_t_u2081_4999_: *mut LeanObject,
    mut v_t_u2082_5000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    v___x_5001_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_4998_,
        v_t_u2081_4999_,
        v_t_u2082_5000_,
    );
    return v___x_5001_;
}
pub unsafe fn l_Std_TreeMap_inter(
    mut v_00_u03b1_5002_: *mut LeanObject,
    mut v_00_u03b2_5003_: *mut LeanObject,
    mut v_cmp_5004_: *mut LeanObject,
    mut v_t_u2081_5005_: *mut LeanObject,
    mut v_t_u2082_5006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    v___x_5007_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_5004_,
        v_t_u2081_5005_,
        v_t_u2082_5006_,
    );
    return v___x_5007_;
}
pub unsafe fn l_Std_TreeMap_instInter___redArg(
    mut v_cmp_5008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    v___x_5009_ = lean_alloc_closure(l_Std_TreeMap_inter as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_5009_, 0, lean_box(0));
    lean_closure_set(v___x_5009_, 1, lean_box(0));
    lean_closure_set(v___x_5009_, 2, v_cmp_5008_);
    return v___x_5009_;
}
pub unsafe fn l_Std_TreeMap_instInter(
    mut v_00_u03b1_5010_: *mut LeanObject,
    mut v_00_u03b2_5011_: *mut LeanObject,
    mut v_cmp_5012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    v___x_5013_ = lean_alloc_closure(l_Std_TreeMap_inter as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_5013_, 0, lean_box(0));
    lean_closure_set(v___x_5013_, 1, lean_box(0));
    lean_closure_set(v___x_5013_, 2, v_cmp_5012_);
    return v___x_5013_;
}
pub unsafe fn l_Std_TreeMap_beq___redArg(
    mut v_cmp_5014_: *mut LeanObject,
    mut v_inst_5015_: *mut LeanObject,
    mut v_t_u2081_5016_: *mut LeanObject,
    mut v_t_u2082_5017_: *mut LeanObject,
) -> u8 {
    let mut v___x_5018_: u8 = 0;
    v___x_5018_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_5014_,
        v_inst_5015_,
        v_t_u2081_5016_,
        v_t_u2082_5017_,
    );
    return v___x_5018_;
}
pub unsafe fn l_Std_TreeMap_beq___redArg___boxed(
    mut v_cmp_5019_: *mut LeanObject,
    mut v_inst_5020_: *mut LeanObject,
    mut v_t_u2081_5021_: *mut LeanObject,
    mut v_t_u2082_5022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5023_: u8 = 0;
    let mut v_r_5024_: *mut LeanObject = core::ptr::null_mut();
    v_res_5023_ =
        l_Std_TreeMap_beq___redArg(v_cmp_5019_, v_inst_5020_, v_t_u2081_5021_, v_t_u2082_5022_);
    v_r_5024_ = lean_box((v_res_5023_) as usize);
    return v_r_5024_;
}
pub unsafe fn l_Std_TreeMap_beq(
    mut v_00_u03b1_5025_: *mut LeanObject,
    mut v_00_u03b2_5026_: *mut LeanObject,
    mut v_cmp_5027_: *mut LeanObject,
    mut v_inst_5028_: *mut LeanObject,
    mut v_t_u2081_5029_: *mut LeanObject,
    mut v_t_u2082_5030_: *mut LeanObject,
) -> u8 {
    let mut v___x_5031_: u8 = 0;
    v___x_5031_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_5027_,
        v_inst_5028_,
        v_t_u2081_5029_,
        v_t_u2082_5030_,
    );
    return v___x_5031_;
}
pub unsafe fn l_Std_TreeMap_beq___boxed(
    mut v_00_u03b1_5032_: *mut LeanObject,
    mut v_00_u03b2_5033_: *mut LeanObject,
    mut v_cmp_5034_: *mut LeanObject,
    mut v_inst_5035_: *mut LeanObject,
    mut v_t_u2081_5036_: *mut LeanObject,
    mut v_t_u2082_5037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5038_: u8 = 0;
    let mut v_r_5039_: *mut LeanObject = core::ptr::null_mut();
    v_res_5038_ = l_Std_TreeMap_beq(
        v_00_u03b1_5032_,
        v_00_u03b2_5033_,
        v_cmp_5034_,
        v_inst_5035_,
        v_t_u2081_5036_,
        v_t_u2082_5037_,
    );
    v_r_5039_ = lean_box((v_res_5038_) as usize);
    return v_r_5039_;
}
pub unsafe fn l_Std_TreeMap_instBEq___redArg(
    mut v_cmp_5040_: *mut LeanObject,
    mut v_inst_5041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    v___x_5042_ = lean_alloc_closure(l_Std_TreeMap_beq___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_5042_, 0, lean_box(0));
    lean_closure_set(v___x_5042_, 1, lean_box(0));
    lean_closure_set(v___x_5042_, 2, v_cmp_5040_);
    lean_closure_set(v___x_5042_, 3, v_inst_5041_);
    return v___x_5042_;
}
pub unsafe fn l_Std_TreeMap_instBEq(
    mut v_00_u03b1_5043_: *mut LeanObject,
    mut v_00_u03b2_5044_: *mut LeanObject,
    mut v_cmp_5045_: *mut LeanObject,
    mut v_inst_5046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    v___x_5047_ = lean_alloc_closure(l_Std_TreeMap_beq___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_5047_, 0, lean_box(0));
    lean_closure_set(v___x_5047_, 1, lean_box(0));
    lean_closure_set(v___x_5047_, 2, v_cmp_5045_);
    lean_closure_set(v___x_5047_, 3, v_inst_5046_);
    return v___x_5047_;
}
pub unsafe fn l_Std_TreeMap_diff___redArg(
    mut v_cmp_5048_: *mut LeanObject,
    mut v_t_u2081_5049_: *mut LeanObject,
    mut v_t_u2082_5050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    v___x_5051_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_5048_,
        v_t_u2081_5049_,
        v_t_u2082_5050_,
    );
    return v___x_5051_;
}
pub unsafe fn l_Std_TreeMap_diff(
    mut v_00_u03b1_5052_: *mut LeanObject,
    mut v_00_u03b2_5053_: *mut LeanObject,
    mut v_cmp_5054_: *mut LeanObject,
    mut v_t_u2081_5055_: *mut LeanObject,
    mut v_t_u2082_5056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    v___x_5057_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_5054_,
        v_t_u2081_5055_,
        v_t_u2082_5056_,
    );
    return v___x_5057_;
}
pub unsafe fn l_Std_TreeMap_instSDiff___redArg(
    mut v_cmp_5058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    v___x_5059_ = lean_alloc_closure(l_Std_TreeMap_diff as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_5059_, 0, lean_box(0));
    lean_closure_set(v___x_5059_, 1, lean_box(0));
    lean_closure_set(v___x_5059_, 2, v_cmp_5058_);
    return v___x_5059_;
}
pub unsafe fn l_Std_TreeMap_instSDiff(
    mut v_00_u03b1_5060_: *mut LeanObject,
    mut v_00_u03b2_5061_: *mut LeanObject,
    mut v_cmp_5062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    v___x_5063_ = lean_alloc_closure(l_Std_TreeMap_diff as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_5063_, 0, lean_box(0));
    lean_closure_set(v___x_5063_, 1, lean_box(0));
    lean_closure_set(v___x_5063_, 2, v_cmp_5062_);
    return v___x_5063_;
}
pub unsafe fn l_Std_TreeMap_insertManyIfNewUnit___redArg___lam__0(
    mut v_cmp_5064_: *mut LeanObject,
    mut v_a_5065_: *mut LeanObject,
    mut v_____s_5066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5067_: u8 = 0;
    lean_inc(v_____s_5066_);
    lean_inc(v_a_5065_);
    lean_inc_ref(v_cmp_5064_);
    v___x_5067_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5064_, v_a_5065_, v_____s_5066_);
    if v___x_5067_ == 0 {
        let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
        v___x_5068_ = lean_box(0);
        v___x_5069_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_5064_,
            v_a_5065_,
            v___x_5068_,
            v_____s_5066_,
        );
        v___x_5070_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5070_, 0, v___x_5069_);
        return v___x_5070_;
    } else {
        let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_5065_);
        lean_dec_ref(v_cmp_5064_);
        v___x_5071_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5071_, 0, v_____s_5066_);
        return v___x_5071_;
    }
}
pub unsafe fn l_Std_TreeMap_insertManyIfNewUnit___redArg(
    mut v_cmp_5072_: *mut LeanObject,
    mut v_inst_5073_: *mut LeanObject,
    mut v_t_5074_: *mut LeanObject,
    mut v_l_5075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    v___f_5076_ = lean_alloc_closure(
        l_Std_TreeMap_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5076_, 0, v_cmp_5072_);
    v___x_5077_ = lean_apply_4(v_inst_5073_, lean_box(0), v_l_5075_, v_t_5074_, v___f_5076_);
    return v___x_5077_;
}
pub unsafe fn l_Std_TreeMap_insertManyIfNewUnit(
    mut v_00_u03b1_5078_: *mut LeanObject,
    mut v_cmp_5079_: *mut LeanObject,
    mut v_00_u03c1_5080_: *mut LeanObject,
    mut v_inst_5081_: *mut LeanObject,
    mut v_t_5082_: *mut LeanObject,
    mut v_l_5083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    v___f_5084_ = lean_alloc_closure(
        l_Std_TreeMap_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5084_, 0, v_cmp_5079_);
    v___x_5085_ = lean_apply_4(v_inst_5081_, lean_box(0), v_l_5083_, v_t_5082_, v___f_5084_);
    return v___x_5085_;
}
pub unsafe fn l_Std_TreeMap_eraseMany___redArg___lam__0(
    mut v_cmp_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_____s_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    v_r_5089_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_5086_, v_a_5087_, v_____s_5088_);
    v___x_5090_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5090_, 0, v_r_5089_);
    return v___x_5090_;
}
pub unsafe fn l_Std_TreeMap_eraseMany___redArg(
    mut v_cmp_5091_: *mut LeanObject,
    mut v_inst_5092_: *mut LeanObject,
    mut v_t_5093_: *mut LeanObject,
    mut v_l_5094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    v___f_5095_ = lean_alloc_closure(
        l_Std_TreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5095_, 0, v_cmp_5091_);
    v___x_5096_ = lean_apply_4(v_inst_5092_, lean_box(0), v_l_5094_, v_t_5093_, v___f_5095_);
    return v___x_5096_;
}
pub unsafe fn l_Std_TreeMap_eraseMany(
    mut v_00_u03b1_5097_: *mut LeanObject,
    mut v_00_u03b2_5098_: *mut LeanObject,
    mut v_cmp_5099_: *mut LeanObject,
    mut v_00_u03c1_5100_: *mut LeanObject,
    mut v_inst_5101_: *mut LeanObject,
    mut v_t_5102_: *mut LeanObject,
    mut v_l_5103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    v___f_5104_ = lean_alloc_closure(
        l_Std_TreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5104_, 0, v_cmp_5099_);
    v___x_5105_ = lean_apply_4(v_inst_5101_, lean_box(0), v_l_5103_, v_t_5102_, v___f_5104_);
    return v___x_5105_;
}
pub unsafe fn l_Std_TreeMap_instRepr___redArg___lam__1(
    mut v___f_5109_: *mut LeanObject,
    mut v___x_5110_: *mut LeanObject,
    mut v_m_5111_: *mut LeanObject,
    mut v_prec_5112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    v___x_5113_ = l_Std_TreeMap_instRepr___redArg___lam__1___closed__1;
    v___x_5114_ = lean_box(0);
    v___x_5115_ = l_Std_TreeMap_foldr___redArg___closed__9;
    v___x_5116_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5115_,
        v___f_5109_,
        v___x_5114_,
        v_m_5111_,
    );
    v___x_5117_ = l_List_repr___redArg(v___x_5110_, v___x_5116_);
    v___x_5118_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5118_, 0, v___x_5113_);
    lean_ctor_set(v___x_5118_, 1, v___x_5117_);
    v___x_5119_ = l_Repr_addAppParen(v___x_5118_, v_prec_5112_);
    return v___x_5119_;
}
pub unsafe fn l_Std_TreeMap_instRepr___redArg___lam__1___boxed(
    mut v___f_5120_: *mut LeanObject,
    mut v___x_5121_: *mut LeanObject,
    mut v_m_5122_: *mut LeanObject,
    mut v_prec_5123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5124_: *mut LeanObject = core::ptr::null_mut();
    v_res_5124_ =
        l_Std_TreeMap_instRepr___redArg___lam__1(v___f_5120_, v___x_5121_, v_m_5122_, v_prec_5123_);
    lean_dec(v_prec_5123_);
    return v_res_5124_;
}
pub unsafe fn l_Std_TreeMap_instRepr___redArg(
    mut v_inst_5125_: *mut LeanObject,
    mut v_inst_5126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5130_: *mut LeanObject = core::ptr::null_mut();
    v___f_5127_ = l_Std_TreeMap_toList___redArg___closed__0;
    v___f_5128_ = lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5128_, 0, v_inst_5126_);
    v___x_5129_ = lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_5129_, 0, lean_box(0));
    lean_closure_set(v___x_5129_, 1, lean_box(0));
    lean_closure_set(v___x_5129_, 2, v_inst_5125_);
    lean_closure_set(v___x_5129_, 3, v___f_5128_);
    v___f_5130_ = lean_alloc_closure(
        l_Std_TreeMap_instRepr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5130_, 0, v___f_5127_);
    lean_closure_set(v___f_5130_, 1, v___x_5129_);
    return v___f_5130_;
}
pub unsafe fn l_Std_TreeMap_instRepr(
    mut v_00_u03b1_5131_: *mut LeanObject,
    mut v_00_u03b2_5132_: *mut LeanObject,
    mut v_cmp_5133_: *mut LeanObject,
    mut v_inst_5134_: *mut LeanObject,
    mut v_inst_5135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    v___x_5136_ = l_Std_TreeMap_instRepr___redArg(v_inst_5134_, v_inst_5135_);
    return v___x_5136_;
}
pub unsafe fn l_Std_TreeMap_instRepr___boxed(
    mut v_00_u03b1_5137_: *mut LeanObject,
    mut v_00_u03b2_5138_: *mut LeanObject,
    mut v_cmp_5139_: *mut LeanObject,
    mut v_inst_5140_: *mut LeanObject,
    mut v_inst_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5142_: *mut LeanObject = core::ptr::null_mut();
    v_res_5142_ = l_Std_TreeMap_instRepr(
        v_00_u03b1_5137_,
        v_00_u03b2_5138_,
        v_cmp_5139_,
        v_inst_5140_,
        v_inst_5141_,
    );
    lean_dec_ref(v_cmp_5139_);
    return v_res_5142_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeMap___auto__1 = _init_l_Std_TreeMap___auto__1();
    lean_mark_persistent(l_Std_TreeMap___auto__1);
    l_Std_TreeMap_ofList___auto__1 = _init_l_Std_TreeMap_ofList___auto__1();
    lean_mark_persistent(l_Std_TreeMap_ofList___auto__1);
    l_Std_TreeMap_unitOfList___auto__1 = _init_l_Std_TreeMap_unitOfList___auto__1();
    lean_mark_persistent(l_Std_TreeMap_unitOfList___auto__1);
    l_Std_TreeMap_ofArray___auto__1 = _init_l_Std_TreeMap_ofArray___auto__1();
    lean_mark_persistent(l_Std_TreeMap_ofArray___auto__1);
    l_Std_TreeMap_unitOfArray___auto__1 = _init_l_Std_TreeMap_unitOfArray___auto__1();
    lean_mark_persistent(l_Std_TreeMap_unitOfArray___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Basic(builtin);
}
