// Lean compiler output
// Module: Std.Data.TreeSet.Raw.Basic
// Imports: Std.Data.TreeMap.Raw.Basic Std.Data.TreeSet.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::List::Control::l_List_forIn_x27_loop___redArg;
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_mkAtom, l_Lean_replaceRef, l_String_toRawSubstring_x27,
    l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_erase_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_filter_x21___redArg, l_Std_DTreeMap_Internal_Impl_insert___redArg,
    l_Std_DTreeMap_Internal_Impl_insert_x21___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
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
    l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_minKeyD___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::Basic::{
    l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg,
};
use crate::r#gen::Std::Data::TreeMap::Raw::Basic::{
    initialize_Std_Data_TreeMap_Raw_Basic, runtime_initialize_Std_Data_TreeMap_Raw_Basic,
};
use crate::r#gen::Std::Data::TreeSet::Basic::{
    initialize_Std_Data_TreeSet_Basic, runtime_initialize_Std_Data_TreeSet_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_TreeSet_Raw___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__3_value) as *mut LeanObject;
static l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeSet_Raw___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__6_value) as *mut LeanObject;
static l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeSet_Raw___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__10_value) as *mut LeanObject;
static l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeSet_Raw___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__10_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Std_TreeSet_Raw___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw___auto__1___closed__14_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Std_TreeSet_Raw___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__14_value) as *mut LeanObject;
static mut l_Std_TreeSet_Raw___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw___auto__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__14_value) as *mut LeanObject,
        16710690322389477741 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__17_value) as *mut LeanObject;
static mut l_Std_TreeSet_Raw___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_Raw___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__0_value: LeanStringObject<4> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__1_value: LeanStringObject<8> =
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
        m_data: [84, 114, 101, 101, 83, 101, 116, 0],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__2_value: LeanStringObject<4> =
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
        m_data: [82, 97, 119, 0],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__2_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__3_value: LeanStringObject<9> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__3_value) as *mut LeanObject;
static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__1_value)
                as *mut LeanObject,
            206985604220839926 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__2_value)
                as *mut LeanObject,
            9795449845313637869 as *mut LeanObject,
        ],
    };
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__3_value)
                as *mut LeanObject,
            2456139370004573775 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__5_value: LeanStringObject<8> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__5_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__5_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__6_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__7_value: LeanStringObject<5> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__9_value: LeanStringObject<5> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__9_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__10_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__11_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__10_value)
                as *mut LeanObject,
            (((51 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__11_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__12_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__13_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value)
                as *mut LeanObject,
            (((50 as usize) << 1) | 1) as *mut LeanObject,
            (((51 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__13_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_Raw_term___x7em__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__13_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value) as *mut LeanObject;
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value) as *mut LeanObject;
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value) as *mut LeanObject,6049842283740396800 as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5_value) as *mut LeanObject;
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__1_value) as *mut LeanObject,206985604220839926 as *mut LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__2_value) as *mut LeanObject,9795449845313637869 as *mut LeanObject] };
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value) as *mut LeanObject,14075073652097311246 as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value) as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value) as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0_value: LeanStringObject<26> =
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
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1_value: LeanStringObject<12> =
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
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2_value: LeanStringObject<14> =
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
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_partition___redArg___closed__0_value: LeanCtorObject<2> =
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
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_partition___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_partition___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_any___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Std_TreeSet_Raw_any___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_any___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_toList___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_Raw_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_toList___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_Raw_ofList___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_toArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_Raw_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_Raw_toArray___redArg___closed__1_value: LeanArrayObject<0> =
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
static mut l_Std_TreeSet_Raw_toArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_toArray___redArg___closed__1_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_Raw_ofArray___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value: LeanStringObject<24> =
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
            83, 116, 100, 46, 84, 114, 101, 101, 83, 101, 116, 46, 82, 97, 119, 46, 111, 102, 76,
            105, 115, 116, 32, 0,
        ],
    };
static mut l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v___x_1710_ = l_Std_TreeSet_Raw___auto__1___closed__10;
    v___x_1711_ = l_Lean_mkAtom(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    v___x_1712_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__12_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__12,
    );
    v___x_1713_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1714_ = lean_array_push(v___x_1713_, v___x_1712_);
    return v___x_1714_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Std_TreeSet_Raw___auto__1___closed__14;
    v___x_1717_ = lean_string_utf8_byte_size(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__15_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__15,
    );
    v___x_1719_ = lean_unsigned_to_nat(0);
    v___x_1720_ = l_Std_TreeSet_Raw___auto__1___closed__14;
    v___x_1721_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1721_, 0, v___x_1720_);
    lean_ctor_set(v___x_1721_, 1, v___x_1719_);
    lean_ctor_set(v___x_1721_, 2, v___x_1718_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1724_ = lean_box(0);
    v___x_1725_ = l_Std_TreeSet_Raw___auto__1___closed__17;
    v___x_1726_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__16_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__16,
    );
    v___x_1727_ = lean_box(2);
    v___x_1728_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_1728_, 0, v___x_1727_);
    lean_ctor_set(v___x_1728_, 1, v___x_1726_);
    lean_ctor_set(v___x_1728_, 2, v___x_1725_);
    lean_ctor_set(v___x_1728_, 3, v___x_1724_);
    return v___x_1728_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    v___x_1729_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__18_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__18,
    );
    v___x_1730_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__13_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__13,
    );
    v___x_1731_ = lean_array_push(v___x_1730_, v___x_1729_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    v___x_1732_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__19_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__19,
    );
    v___x_1733_ = l_Std_TreeSet_Raw___auto__1___closed__11;
    v___x_1734_ = lean_box(2);
    v___x_1735_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1735_, 0, v___x_1734_);
    lean_ctor_set(v___x_1735_, 1, v___x_1733_);
    lean_ctor_set(v___x_1735_, 2, v___x_1732_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    v___x_1736_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__20_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__20,
    );
    v___x_1737_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1738_ = lean_array_push(v___x_1737_, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    v___x_1739_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__21_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__21,
    );
    v___x_1740_ = l_Std_TreeSet_Raw___auto__1___closed__9;
    v___x_1741_ = lean_box(2);
    v___x_1742_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1742_, 0, v___x_1741_);
    lean_ctor_set(v___x_1742_, 1, v___x_1740_);
    lean_ctor_set(v___x_1742_, 2, v___x_1739_);
    return v___x_1742_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    v___x_1743_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__22_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__22,
    );
    v___x_1744_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1745_ = lean_array_push(v___x_1744_, v___x_1743_);
    return v___x_1745_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__23_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__23,
    );
    v___x_1747_ = l_Std_TreeSet_Raw___auto__1___closed__7;
    v___x_1748_ = lean_box(2);
    v___x_1749_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1749_, 0, v___x_1748_);
    lean_ctor_set(v___x_1749_, 1, v___x_1747_);
    lean_ctor_set(v___x_1749_, 2, v___x_1746_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    v___x_1750_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__24_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__24,
    );
    v___x_1751_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1752_ = lean_array_push(v___x_1751_, v___x_1750_);
    return v___x_1752_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    v___x_1753_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__25_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__25,
    );
    v___x_1754_ = l_Std_TreeSet_Raw___auto__1___closed__4;
    v___x_1755_ = lean_box(2);
    v___x_1756_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1756_, 0, v___x_1755_);
    lean_ctor_set(v___x_1756_, 1, v___x_1754_);
    lean_ctor_set(v___x_1756_, 2, v___x_1753_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1() -> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__26,
    );
    return v___x_1757_;
}
pub unsafe fn l_Std_TreeSet_Raw_instCoeWFWFUnitInner(
    mut v_00_u03b1_1758_: *mut LeanObject,
    mut v_cmp_1759_: *mut LeanObject,
    mut v_t_1760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    v___x_1761_ = lean_box(0);
    return v___x_1761_;
}
pub unsafe fn l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(
    mut v_00_u03b1_1762_: *mut LeanObject,
    mut v_cmp_1763_: *mut LeanObject,
    mut v_t_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1765_: *mut LeanObject = core::ptr::null_mut();
    v_res_1765_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner(v_00_u03b1_1762_, v_cmp_1763_, v_t_1764_);
    lean_dec(v_t_1764_);
    lean_dec_ref(v_cmp_1763_);
    return v_res_1765_;
}
pub unsafe fn l_Std_TreeSet_Raw_empty(
    mut v_00_u03b1_1766_: *mut LeanObject,
    mut v_cmp_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    v___x_1768_ = lean_box(1);
    return v___x_1768_;
}
pub unsafe fn l_Std_TreeSet_Raw_empty___boxed(
    mut v_00_u03b1_1769_: *mut LeanObject,
    mut v_cmp_1770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1771_: *mut LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Std_TreeSet_Raw_empty(v_00_u03b1_1769_, v_cmp_1770_);
    lean_dec_ref(v_cmp_1770_);
    return v_res_1771_;
}
pub unsafe fn l_Std_TreeSet_Raw_instEmptyCollection(
    mut v_00_u03b1_1772_: *mut LeanObject,
    mut v_cmp_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    v___x_1774_ = lean_box(1);
    return v___x_1774_;
}
pub unsafe fn l_Std_TreeSet_Raw_instEmptyCollection___boxed(
    mut v_00_u03b1_1775_: *mut LeanObject,
    mut v_cmp_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1777_: *mut LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Std_TreeSet_Raw_instEmptyCollection(v_00_u03b1_1775_, v_cmp_1776_);
    lean_dec_ref(v_cmp_1776_);
    return v_res_1777_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInhabited(
    mut v_00_u03b1_1778_: *mut LeanObject,
    mut v_cmp_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    v___x_1780_ = lean_box(1);
    return v___x_1780_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInhabited___boxed(
    mut v_00_u03b1_1781_: *mut LeanObject,
    mut v_cmp_1782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1783_: *mut LeanObject = core::ptr::null_mut();
    v_res_1783_ = l_Std_TreeSet_Raw_instInhabited(v_00_u03b1_1781_, v_cmp_1782_);
    lean_dec_ref(v_cmp_1782_);
    return v_res_1783_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4()
-> *mut LeanObject {
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    v___x_1823_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3;
    v___x_1824_ = l_String_toRawSubstring_x27(v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(
    mut v_x_1843_: *mut LeanObject,
    mut v_a_1844_: *mut LeanObject,
    mut v_a_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    v___x_1846_ = l_Std_TreeSet_Raw_term___x7em___00__closed__4;
    lean_inc(v_x_1843_);
    v___x_1847_ = l_Lean_Syntax_isOfKind(v_x_1843_, v___x_1846_);
    if v___x_1847_ == 0 {
        let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1843_);
        v___x_1848_ = lean_box(1);
        v___x_1849_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1849_, 0, v___x_1848_);
        lean_ctor_set(v___x_1849_, 1, v_a_1845_);
        return v___x_1849_;
    } else {
        let mut v_quotContext_1850_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1851_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: u8 = 0;
        let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1850_ = lean_ctor_get(v_a_1844_, 1);
        v_currMacroScope_1851_ = lean_ctor_get(v_a_1844_, 2);
        v_ref_1852_ = lean_ctor_get(v_a_1844_, 5);
        v___x_1853_ = lean_unsigned_to_nat(0);
        v___x_1854_ = l_Lean_Syntax_getArg(v_x_1843_, v___x_1853_);
        v___x_1855_ = lean_unsigned_to_nat(2);
        v___x_1856_ = l_Lean_Syntax_getArg(v_x_1843_, v___x_1855_);
        lean_dec(v_x_1843_);
        v___x_1857_ = 0;
        v___x_1858_ = l_Lean_SourceInfo_fromRef(v_ref_1852_, v___x_1857_);
        v___x_1859_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2;
        v___x_1860_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4), core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once), _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4);
        v___x_1861_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5;
        lean_inc(v_currMacroScope_1851_);
        lean_inc(v_quotContext_1850_);
        v___x_1862_ =
            l_Lean_addMacroScope(v_quotContext_1850_, v___x_1861_, v_currMacroScope_1851_);
        v___x_1863_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10;
        lean_inc_n(v___x_1858_, 2);
        v___x_1864_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1864_, 0, v___x_1858_);
        lean_ctor_set(v___x_1864_, 1, v___x_1860_);
        lean_ctor_set(v___x_1864_, 2, v___x_1862_);
        lean_ctor_set(v___x_1864_, 3, v___x_1863_);
        v___x_1865_ = l_Std_TreeSet_Raw___auto__1___closed__9;
        v___x_1866_ = l_Lean_Syntax_node2(v___x_1858_, v___x_1865_, v___x_1854_, v___x_1856_);
        v___x_1867_ = l_Lean_Syntax_node2(v___x_1858_, v___x_1859_, v___x_1864_, v___x_1866_);
        v___x_1868_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1868_, 0, v___x_1867_);
        lean_ctor_set(v___x_1868_, 1, v_a_1845_);
        return v___x_1868_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___boxed(
    mut v_x_1869_: *mut LeanObject,
    mut v_a_1870_: *mut LeanObject,
    mut v_a_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1872_: *mut LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(v_x_1869_, v_a_1870_, v_a_1871_);
    lean_dec_ref(v_a_1870_);
    return v_res_1872_;
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(
    mut v_x_1876_: *mut LeanObject,
    mut v_a_1877_: *mut LeanObject,
    mut v_a_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    v___x_1879_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2;
    lean_inc(v_x_1876_);
    v___x_1880_ = l_Lean_Syntax_isOfKind(v_x_1876_, v___x_1879_);
    if v___x_1880_ == 0 {
        let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1876_);
        v___x_1881_ = lean_box(0);
        v___x_1882_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1882_, 0, v___x_1881_);
        lean_ctor_set(v___x_1882_, 1, v_a_1878_);
        return v___x_1882_;
    } else {
        let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: u8 = 0;
        v___x_1883_ = lean_unsigned_to_nat(0);
        v___x_1884_ = l_Lean_Syntax_getArg(v_x_1876_, v___x_1883_);
        v___x_1885_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1;
        lean_inc(v___x_1884_);
        v___x_1886_ = l_Lean_Syntax_isOfKind(v___x_1884_, v___x_1885_);
        if v___x_1886_ == 0 {
            let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1884_);
            lean_dec(v_x_1876_);
            v___x_1887_ = lean_box(0);
            v___x_1888_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1888_, 0, v___x_1887_);
            lean_ctor_set(v___x_1888_, 1, v_a_1878_);
            return v___x_1888_;
        } else {
            let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1892_: u8 = 0;
            v___x_1889_ = lean_unsigned_to_nat(1);
            v___x_1890_ = l_Lean_Syntax_getArg(v_x_1876_, v___x_1889_);
            lean_dec(v_x_1876_);
            v___x_1891_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1890_);
            v___x_1892_ = l_Lean_Syntax_matchesNull(v___x_1890_, v___x_1891_);
            if v___x_1892_ == 0 {
                let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1890_);
                lean_dec(v___x_1884_);
                v___x_1893_ = lean_box(0);
                v___x_1894_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1894_, 0, v___x_1893_);
                lean_ctor_set(v___x_1894_, 1, v_a_1878_);
                return v___x_1894_;
            } else {
                let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1897_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1898_: u8 = 0;
                let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
                v___x_1895_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1883_);
                v___x_1896_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1889_);
                lean_dec(v___x_1890_);
                v_ref_1897_ = l_Lean_replaceRef(v___x_1884_, v_a_1877_);
                lean_dec(v___x_1884_);
                v___x_1898_ = 0;
                v___x_1899_ = l_Lean_SourceInfo_fromRef(v_ref_1897_, v___x_1898_);
                lean_dec(v_ref_1897_);
                v___x_1900_ = l_Std_TreeSet_Raw_term___x7em___00__closed__4;
                v___x_1901_ = l_Std_TreeSet_Raw_term___x7em___00__closed__7;
                lean_inc(v___x_1899_);
                v___x_1902_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1902_, 0, v___x_1899_);
                lean_ctor_set(v___x_1902_, 1, v___x_1901_);
                v___x_1903_ = l_Lean_Syntax_node3(
                    v___x_1899_,
                    v___x_1900_,
                    v___x_1895_,
                    v___x_1902_,
                    v___x_1896_,
                );
                v___x_1904_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1904_, 0, v___x_1903_);
                lean_ctor_set(v___x_1904_, 1, v_a_1878_);
                return v___x_1904_;
            }
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(
    mut v_x_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1908_: *mut LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(v_x_1905_, v_a_1906_, v_a_1907_);
    lean_dec(v_a_1906_);
    return v_res_1908_;
}
pub unsafe fn l_Std_TreeSet_Raw_insert___redArg(
    mut v_cmp_1909_: *mut LeanObject,
    mut v_l_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1912_: u8 = 0;
    lean_inc(v_l_1910_);
    lean_inc(v_a_1911_);
    lean_inc_ref(v_cmp_1909_);
    v___x_1912_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1909_, v_a_1911_, v_l_1910_);
    if v___x_1912_ == 0 {
        let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
        v___x_1913_ = lean_box(0);
        v___x_1914_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1909_,
            v_a_1911_,
            v___x_1913_,
            v_l_1910_,
        );
        return v___x_1914_;
    } else {
        lean_dec(v_a_1911_);
        lean_dec_ref(v_cmp_1909_);
        return v_l_1910_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_insert(
    mut v_00_u03b1_1915_: *mut LeanObject,
    mut v_cmp_1916_: *mut LeanObject,
    mut v_l_1917_: *mut LeanObject,
    mut v_a_1918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1919_: u8 = 0;
    lean_inc(v_l_1917_);
    lean_inc(v_a_1918_);
    lean_inc_ref(v_cmp_1916_);
    v___x_1919_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1916_, v_a_1918_, v_l_1917_);
    if v___x_1919_ == 0 {
        let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
        v___x_1920_ = lean_box(0);
        v___x_1921_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1916_,
            v_a_1918_,
            v___x_1920_,
            v_l_1917_,
        );
        return v___x_1921_;
    } else {
        lean_dec(v_a_1918_);
        lean_dec_ref(v_cmp_1916_);
        return v_l_1917_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(
    mut v_cmp_1922_: *mut LeanObject,
    mut v_e_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    v___x_1924_ = lean_box(1);
    lean_inc(v_e_1923_);
    lean_inc_ref(v_cmp_1922_);
    v___x_1925_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1922_, v_e_1923_, v___x_1924_);
    if v___x_1925_ == 0 {
        let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
        v___x_1926_ = lean_box(0);
        v___x_1927_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1922_,
            v_e_1923_,
            v___x_1926_,
            v___x_1924_,
        );
        return v___x_1927_;
    } else {
        lean_dec(v_e_1923_);
        lean_dec_ref(v_cmp_1922_);
        return v___x_1924_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_instSingleton___redArg(
    mut v_cmp_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1929_: *mut LeanObject = core::ptr::null_mut();
    v___f_1929_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1929_, 0, v_cmp_1928_);
    return v___f_1929_;
}
pub unsafe fn l_Std_TreeSet_Raw_instSingleton(
    mut v_00_u03b1_1930_: *mut LeanObject,
    mut v_cmp_1931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1932_: *mut LeanObject = core::ptr::null_mut();
    v___f_1932_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1932_, 0, v_cmp_1931_);
    return v___f_1932_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInsert___redArg___lam__0(
    mut v_cmp_1933_: *mut LeanObject,
    mut v_e_1934_: *mut LeanObject,
    mut v_s_1935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1936_: u8 = 0;
    lean_inc(v_s_1935_);
    lean_inc(v_e_1934_);
    lean_inc_ref(v_cmp_1933_);
    v___x_1936_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1933_, v_e_1934_, v_s_1935_);
    if v___x_1936_ == 0 {
        let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
        v___x_1937_ = lean_box(0);
        v___x_1938_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1933_,
            v_e_1934_,
            v___x_1937_,
            v_s_1935_,
        );
        return v___x_1938_;
    } else {
        lean_dec(v_e_1934_);
        lean_dec_ref(v_cmp_1933_);
        return v_s_1935_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_instInsert___redArg(
    mut v_cmp_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1940_: *mut LeanObject = core::ptr::null_mut();
    v___f_1940_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1940_, 0, v_cmp_1939_);
    return v___f_1940_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInsert(
    mut v_00_u03b1_1941_: *mut LeanObject,
    mut v_cmp_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1943_: *mut LeanObject = core::ptr::null_mut();
    v___f_1943_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1943_, 0, v_cmp_1942_);
    return v___f_1943_;
}
pub unsafe fn l_Std_TreeSet_Raw_containsThenInsert___redArg(
    mut v_cmp_1944_: *mut LeanObject,
    mut v_t_1945_: *mut LeanObject,
    mut v_a_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1947_: u8 = 0;
    lean_inc(v_t_1945_);
    lean_inc(v_a_1946_);
    lean_inc_ref(v_cmp_1944_);
    v___x_1947_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1944_, v_a_1946_, v_t_1945_);
    if v___x_1947_ == 0 {
        let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
        v___x_1948_ = lean_box(0);
        v___x_1949_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1944_,
            v_a_1946_,
            v___x_1948_,
            v_t_1945_,
        );
        v___x_1950_ = lean_box((v___x_1947_) as usize);
        v___x_1951_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1951_, 0, v___x_1950_);
        lean_ctor_set(v___x_1951_, 1, v___x_1949_);
        return v___x_1951_;
    } else {
        let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_1946_);
        lean_dec_ref(v_cmp_1944_);
        v___x_1952_ = lean_box((v___x_1947_) as usize);
        v___x_1953_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1953_, 0, v___x_1952_);
        lean_ctor_set(v___x_1953_, 1, v_t_1945_);
        return v___x_1953_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_containsThenInsert(
    mut v_00_u03b1_1954_: *mut LeanObject,
    mut v_cmp_1955_: *mut LeanObject,
    mut v_t_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958_: u8 = 0;
    lean_inc(v_t_1956_);
    lean_inc(v_a_1957_);
    lean_inc_ref(v_cmp_1955_);
    v___x_1958_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1955_, v_a_1957_, v_t_1956_);
    if v___x_1958_ == 0 {
        let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
        v___x_1959_ = lean_box(0);
        v___x_1960_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1955_,
            v_a_1957_,
            v___x_1959_,
            v_t_1956_,
        );
        v___x_1961_ = lean_box((v___x_1958_) as usize);
        v___x_1962_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1962_, 0, v___x_1961_);
        lean_ctor_set(v___x_1962_, 1, v___x_1960_);
        return v___x_1962_;
    } else {
        let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_1957_);
        lean_dec_ref(v_cmp_1955_);
        v___x_1963_ = lean_box((v___x_1958_) as usize);
        v___x_1964_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1964_, 0, v___x_1963_);
        lean_ctor_set(v___x_1964_, 1, v_t_1956_);
        return v___x_1964_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_contains___redArg(
    mut v_cmp_1965_: *mut LeanObject,
    mut v_l_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
) -> u8 {
    let mut v___x_1968_: u8 = 0;
    v___x_1968_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1965_, v_a_1967_, v_l_1966_);
    return v___x_1968_;
}
pub unsafe fn l_Std_TreeSet_Raw_contains___redArg___boxed(
    mut v_cmp_1969_: *mut LeanObject,
    mut v_l_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1972_: u8 = 0;
    let mut v_r_1973_: *mut LeanObject = core::ptr::null_mut();
    v_res_1972_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_1969_, v_l_1970_, v_a_1971_);
    v_r_1973_ = lean_box((v_res_1972_) as usize);
    return v_r_1973_;
}
pub unsafe fn l_Std_TreeSet_Raw_contains(
    mut v_00_u03b1_1974_: *mut LeanObject,
    mut v_cmp_1975_: *mut LeanObject,
    mut v_l_1976_: *mut LeanObject,
    mut v_a_1977_: *mut LeanObject,
) -> u8 {
    let mut v___x_1978_: u8 = 0;
    v___x_1978_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1975_, v_a_1977_, v_l_1976_);
    return v___x_1978_;
}
pub unsafe fn l_Std_TreeSet_Raw_contains___boxed(
    mut v_00_u03b1_1979_: *mut LeanObject,
    mut v_cmp_1980_: *mut LeanObject,
    mut v_l_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1983_: u8 = 0;
    let mut v_r_1984_: *mut LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Std_TreeSet_Raw_contains(v_00_u03b1_1979_, v_cmp_1980_, v_l_1981_, v_a_1982_);
    v_r_1984_ = lean_box((v_res_1983_) as usize);
    return v_r_1984_;
}
pub unsafe fn l_Std_TreeSet_Raw_instMembership(
    mut v_00_u03b1_1985_: *mut LeanObject,
    mut v_cmp_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    v___x_1987_ = lean_box(0);
    return v___x_1987_;
}
pub unsafe fn l_Std_TreeSet_Raw_instMembership___boxed(
    mut v_00_u03b1_1988_: *mut LeanObject,
    mut v_cmp_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1990_: *mut LeanObject = core::ptr::null_mut();
    v_res_1990_ = l_Std_TreeSet_Raw_instMembership(v_00_u03b1_1988_, v_cmp_1989_);
    lean_dec_ref(v_cmp_1989_);
    return v_res_1990_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem___redArg(
    mut v_cmp_1991_: *mut LeanObject,
    mut v_t_1992_: *mut LeanObject,
    mut v_a_1993_: *mut LeanObject,
) -> u8 {
    let mut v___x_1994_: u8 = 0;
    v___x_1994_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1991_, v_a_1993_, v_t_1992_);
    return v___x_1994_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(
    mut v_cmp_1995_: *mut LeanObject,
    mut v_t_1996_: *mut LeanObject,
    mut v_a_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1998_: u8 = 0;
    let mut v_r_1999_: *mut LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_1995_, v_t_1996_, v_a_1997_);
    v_r_1999_ = lean_box((v_res_1998_) as usize);
    return v_r_1999_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem(
    mut v_00_u03b1_2000_: *mut LeanObject,
    mut v_cmp_2001_: *mut LeanObject,
    mut v_t_2002_: *mut LeanObject,
    mut v_a_2003_: *mut LeanObject,
) -> u8 {
    let mut v___x_2004_: u8 = 0;
    v___x_2004_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2001_, v_a_2003_, v_t_2002_);
    return v___x_2004_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem___boxed(
    mut v_00_u03b1_2005_: *mut LeanObject,
    mut v_cmp_2006_: *mut LeanObject,
    mut v_t_2007_: *mut LeanObject,
    mut v_a_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2009_: u8 = 0;
    let mut v_r_2010_: *mut LeanObject = core::ptr::null_mut();
    v_res_2009_ =
        l_Std_TreeSet_Raw_instDecidableMem(v_00_u03b1_2005_, v_cmp_2006_, v_t_2007_, v_a_2008_);
    v_r_2010_ = lean_box((v_res_2009_) as usize);
    return v_r_2010_;
}
pub unsafe fn l_Std_TreeSet_Raw_size___redArg(mut v_t_2011_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_t_2011_) == 0 {
        let mut v_size_2012_: *mut LeanObject = core::ptr::null_mut();
        v_size_2012_ = lean_ctor_get(v_t_2011_, 0);
        lean_inc(v_size_2012_);
        return v_size_2012_;
    } else {
        let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
        v___x_2013_ = lean_unsigned_to_nat(0);
        return v___x_2013_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_size___redArg___boxed(
    mut v_t_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2015_: *mut LeanObject = core::ptr::null_mut();
    v_res_2015_ = l_Std_TreeSet_Raw_size___redArg(v_t_2014_);
    lean_dec(v_t_2014_);
    return v_res_2015_;
}
pub unsafe fn l_Std_TreeSet_Raw_size(
    mut v_00_u03b1_2016_: *mut LeanObject,
    mut v_cmp_2017_: *mut LeanObject,
    mut v_t_2018_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_2018_) == 0 {
        let mut v_size_2019_: *mut LeanObject = core::ptr::null_mut();
        v_size_2019_ = lean_ctor_get(v_t_2018_, 0);
        lean_inc(v_size_2019_);
        return v_size_2019_;
    } else {
        let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
        v___x_2020_ = lean_unsigned_to_nat(0);
        return v___x_2020_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_size___boxed(
    mut v_00_u03b1_2021_: *mut LeanObject,
    mut v_cmp_2022_: *mut LeanObject,
    mut v_t_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2024_: *mut LeanObject = core::ptr::null_mut();
    v_res_2024_ = l_Std_TreeSet_Raw_size(v_00_u03b1_2021_, v_cmp_2022_, v_t_2023_);
    lean_dec(v_t_2023_);
    lean_dec_ref(v_cmp_2022_);
    return v_res_2024_;
}
pub unsafe fn l_Std_TreeSet_Raw_isEmpty___redArg(mut v_t_2025_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_t_2025_) == 0 {
        let mut v___x_2026_: u8 = 0;
        v___x_2026_ = 0;
        return v___x_2026_;
    } else {
        let mut v___x_2027_: u8 = 0;
        v___x_2027_ = 1;
        return v___x_2027_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_isEmpty___redArg___boxed(
    mut v_t_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2029_: u8 = 0;
    let mut v_r_2030_: *mut LeanObject = core::ptr::null_mut();
    v_res_2029_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_2028_);
    lean_dec(v_t_2028_);
    v_r_2030_ = lean_box((v_res_2029_) as usize);
    return v_r_2030_;
}
pub unsafe fn l_Std_TreeSet_Raw_isEmpty(
    mut v_00_u03b1_2031_: *mut LeanObject,
    mut v_cmp_2032_: *mut LeanObject,
    mut v_t_2033_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_t_2033_) == 0 {
        let mut v___x_2034_: u8 = 0;
        v___x_2034_ = 0;
        return v___x_2034_;
    } else {
        let mut v___x_2035_: u8 = 0;
        v___x_2035_ = 1;
        return v___x_2035_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_isEmpty___boxed(
    mut v_00_u03b1_2036_: *mut LeanObject,
    mut v_cmp_2037_: *mut LeanObject,
    mut v_t_2038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2039_: u8 = 0;
    let mut v_r_2040_: *mut LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Std_TreeSet_Raw_isEmpty(v_00_u03b1_2036_, v_cmp_2037_, v_t_2038_);
    lean_dec(v_t_2038_);
    lean_dec_ref(v_cmp_2037_);
    v_r_2040_ = lean_box((v_res_2039_) as usize);
    return v_r_2040_;
}
pub unsafe fn l_Std_TreeSet_Raw_erase___redArg(
    mut v_cmp_2041_: *mut LeanObject,
    mut v_t_2042_: *mut LeanObject,
    mut v_a_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2041_, v_a_2043_, v_t_2042_);
    return v___x_2044_;
}
pub unsafe fn l_Std_TreeSet_Raw_erase(
    mut v_00_u03b1_2045_: *mut LeanObject,
    mut v_cmp_2046_: *mut LeanObject,
    mut v_t_2047_: *mut LeanObject,
    mut v_a_2048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2049_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2046_, v_a_2048_, v_t_2047_);
    return v___x_2049_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x3f___redArg(
    mut v_cmp_2050_: *mut LeanObject,
    mut v_t_2051_: *mut LeanObject,
    mut v_a_2052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    v___x_2053_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2050_, v_t_2051_, v_a_2052_);
    return v___x_2053_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x3f(
    mut v_00_u03b1_2054_: *mut LeanObject,
    mut v_cmp_2055_: *mut LeanObject,
    mut v_t_2056_: *mut LeanObject,
    mut v_a_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    v___x_2058_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2055_, v_t_2056_, v_a_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Std_TreeSet_Raw_get___redArg(
    mut v_cmp_2059_: *mut LeanObject,
    mut v_t_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    v___x_2062_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2059_, v_t_2060_, v_a_2061_);
    return v___x_2062_;
}
pub unsafe fn l_Std_TreeSet_Raw_get(
    mut v_00_u03b1_2063_: *mut LeanObject,
    mut v_cmp_2064_: *mut LeanObject,
    mut v_t_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_h_2067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    v___x_2068_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2064_, v_t_2065_, v_a_2066_);
    return v___x_2068_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21___redArg(
    mut v_cmp_2069_: *mut LeanObject,
    mut v_inst_2070_: *mut LeanObject,
    mut v_t_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    v___x_2073_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2069_,
        v_t_2071_,
        v_a_2072_,
        v_inst_2070_,
    );
    return v___x_2073_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21___redArg___boxed(
    mut v_cmp_2074_: *mut LeanObject,
    mut v_inst_2075_: *mut LeanObject,
    mut v_t_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2078_: *mut LeanObject = core::ptr::null_mut();
    v_res_2078_ =
        l_Std_TreeSet_Raw_get_x21___redArg(v_cmp_2074_, v_inst_2075_, v_t_2076_, v_a_2077_);
    lean_dec(v_inst_2075_);
    return v_res_2078_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21(
    mut v_00_u03b1_2079_: *mut LeanObject,
    mut v_cmp_2080_: *mut LeanObject,
    mut v_inst_2081_: *mut LeanObject,
    mut v_t_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    v___x_2084_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2080_,
        v_t_2082_,
        v_a_2083_,
        v_inst_2081_,
    );
    return v___x_2084_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21___boxed(
    mut v_00_u03b1_2085_: *mut LeanObject,
    mut v_cmp_2086_: *mut LeanObject,
    mut v_inst_2087_: *mut LeanObject,
    mut v_t_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2090_: *mut LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Std_TreeSet_Raw_get_x21(
        v_00_u03b1_2085_,
        v_cmp_2086_,
        v_inst_2087_,
        v_t_2088_,
        v_a_2089_,
    );
    lean_dec(v_inst_2087_);
    return v_res_2090_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD___redArg(
    mut v_cmp_2091_: *mut LeanObject,
    mut v_t_2092_: *mut LeanObject,
    mut v_a_2093_: *mut LeanObject,
    mut v_fallback_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2091_,
        v_t_2092_,
        v_a_2093_,
        v_fallback_2094_,
    );
    return v___x_2095_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD___redArg___boxed(
    mut v_cmp_2096_: *mut LeanObject,
    mut v_t_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_fallback_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2100_: *mut LeanObject = core::ptr::null_mut();
    v_res_2100_ =
        l_Std_TreeSet_Raw_getD___redArg(v_cmp_2096_, v_t_2097_, v_a_2098_, v_fallback_2099_);
    lean_dec(v_fallback_2099_);
    return v_res_2100_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD(
    mut v_00_u03b1_2101_: *mut LeanObject,
    mut v_cmp_2102_: *mut LeanObject,
    mut v_t_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
    mut v_fallback_2105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v___x_2106_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2102_,
        v_t_2103_,
        v_a_2104_,
        v_fallback_2105_,
    );
    return v___x_2106_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD___boxed(
    mut v_00_u03b1_2107_: *mut LeanObject,
    mut v_cmp_2108_: *mut LeanObject,
    mut v_t_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
    mut v_fallback_2111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2112_: *mut LeanObject = core::ptr::null_mut();
    v_res_2112_ = l_Std_TreeSet_Raw_getD(
        v_00_u03b1_2107_,
        v_cmp_2108_,
        v_t_2109_,
        v_a_2110_,
        v_fallback_2111_,
    );
    lean_dec(v_fallback_2111_);
    return v_res_2112_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f___redArg(
    mut v_t_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    v___x_2114_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2113_);
    return v___x_2114_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f___redArg___boxed(
    mut v_t_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2116_: *mut LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Std_TreeSet_Raw_min_x3f___redArg(v_t_2115_);
    lean_dec(v_t_2115_);
    return v_res_2116_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f(
    mut v_00_u03b1_2117_: *mut LeanObject,
    mut v_cmp_2118_: *mut LeanObject,
    mut v_t_2119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    v___x_2120_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2119_);
    return v___x_2120_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f___boxed(
    mut v_00_u03b1_2121_: *mut LeanObject,
    mut v_cmp_2122_: *mut LeanObject,
    mut v_t_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2124_: *mut LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_Std_TreeSet_Raw_min_x3f(v_00_u03b1_2121_, v_cmp_2122_, v_t_2123_);
    lean_dec(v_t_2123_);
    lean_dec_ref(v_cmp_2122_);
    return v_res_2124_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21___redArg(
    mut v_inst_2125_: *mut LeanObject,
    mut v_t_2126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    v___x_2127_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2125_, v_t_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21___redArg___boxed(
    mut v_inst_2128_: *mut LeanObject,
    mut v_t_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2130_: *mut LeanObject = core::ptr::null_mut();
    v_res_2130_ = l_Std_TreeSet_Raw_min_x21___redArg(v_inst_2128_, v_t_2129_);
    lean_dec(v_t_2129_);
    lean_dec(v_inst_2128_);
    return v_res_2130_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21(
    mut v_00_u03b1_2131_: *mut LeanObject,
    mut v_cmp_2132_: *mut LeanObject,
    mut v_inst_2133_: *mut LeanObject,
    mut v_t_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    v___x_2135_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2133_, v_t_2134_);
    return v___x_2135_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21___boxed(
    mut v_00_u03b1_2136_: *mut LeanObject,
    mut v_cmp_2137_: *mut LeanObject,
    mut v_inst_2138_: *mut LeanObject,
    mut v_t_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2140_: *mut LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Std_TreeSet_Raw_min_x21(v_00_u03b1_2136_, v_cmp_2137_, v_inst_2138_, v_t_2139_);
    lean_dec(v_t_2139_);
    lean_dec(v_inst_2138_);
    lean_dec_ref(v_cmp_2137_);
    return v_res_2140_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD___redArg(
    mut v_t_2141_: *mut LeanObject,
    mut v_fallback_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2141_, v_fallback_2142_);
    return v___x_2143_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD___redArg___boxed(
    mut v_t_2144_: *mut LeanObject,
    mut v_fallback_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2146_: *mut LeanObject = core::ptr::null_mut();
    v_res_2146_ = l_Std_TreeSet_Raw_minD___redArg(v_t_2144_, v_fallback_2145_);
    lean_dec(v_fallback_2145_);
    lean_dec(v_t_2144_);
    return v_res_2146_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD(
    mut v_00_u03b1_2147_: *mut LeanObject,
    mut v_cmp_2148_: *mut LeanObject,
    mut v_t_2149_: *mut LeanObject,
    mut v_fallback_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    v___x_2151_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2149_, v_fallback_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD___boxed(
    mut v_00_u03b1_2152_: *mut LeanObject,
    mut v_cmp_2153_: *mut LeanObject,
    mut v_t_2154_: *mut LeanObject,
    mut v_fallback_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2156_: *mut LeanObject = core::ptr::null_mut();
    v_res_2156_ =
        l_Std_TreeSet_Raw_minD(v_00_u03b1_2152_, v_cmp_2153_, v_t_2154_, v_fallback_2155_);
    lean_dec(v_fallback_2155_);
    lean_dec(v_t_2154_);
    lean_dec_ref(v_cmp_2153_);
    return v_res_2156_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f___redArg(
    mut v_t_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    v___x_2158_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2157_);
    return v___x_2158_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f___redArg___boxed(
    mut v_t_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2160_: *mut LeanObject = core::ptr::null_mut();
    v_res_2160_ = l_Std_TreeSet_Raw_max_x3f___redArg(v_t_2159_);
    lean_dec(v_t_2159_);
    return v_res_2160_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f(
    mut v_00_u03b1_2161_: *mut LeanObject,
    mut v_cmp_2162_: *mut LeanObject,
    mut v_t_2163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    v___x_2164_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f___boxed(
    mut v_00_u03b1_2165_: *mut LeanObject,
    mut v_cmp_2166_: *mut LeanObject,
    mut v_t_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2168_: *mut LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Std_TreeSet_Raw_max_x3f(v_00_u03b1_2165_, v_cmp_2166_, v_t_2167_);
    lean_dec(v_t_2167_);
    lean_dec_ref(v_cmp_2166_);
    return v_res_2168_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21___redArg(
    mut v_inst_2169_: *mut LeanObject,
    mut v_t_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    v___x_2171_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2169_, v_t_2170_);
    return v___x_2171_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21___redArg___boxed(
    mut v_inst_2172_: *mut LeanObject,
    mut v_t_2173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2174_: *mut LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_Std_TreeSet_Raw_max_x21___redArg(v_inst_2172_, v_t_2173_);
    lean_dec(v_t_2173_);
    lean_dec(v_inst_2172_);
    return v_res_2174_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21(
    mut v_00_u03b1_2175_: *mut LeanObject,
    mut v_cmp_2176_: *mut LeanObject,
    mut v_inst_2177_: *mut LeanObject,
    mut v_t_2178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    v___x_2179_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2177_, v_t_2178_);
    return v___x_2179_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21___boxed(
    mut v_00_u03b1_2180_: *mut LeanObject,
    mut v_cmp_2181_: *mut LeanObject,
    mut v_inst_2182_: *mut LeanObject,
    mut v_t_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2184_: *mut LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Std_TreeSet_Raw_max_x21(v_00_u03b1_2180_, v_cmp_2181_, v_inst_2182_, v_t_2183_);
    lean_dec(v_t_2183_);
    lean_dec(v_inst_2182_);
    lean_dec_ref(v_cmp_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD___redArg(
    mut v_t_2185_: *mut LeanObject,
    mut v_fallback_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2185_, v_fallback_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD___redArg___boxed(
    mut v_t_2188_: *mut LeanObject,
    mut v_fallback_2189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2190_: *mut LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Std_TreeSet_Raw_maxD___redArg(v_t_2188_, v_fallback_2189_);
    lean_dec(v_fallback_2189_);
    lean_dec(v_t_2188_);
    return v_res_2190_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD(
    mut v_00_u03b1_2191_: *mut LeanObject,
    mut v_cmp_2192_: *mut LeanObject,
    mut v_t_2193_: *mut LeanObject,
    mut v_fallback_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2193_, v_fallback_2194_);
    return v___x_2195_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD___boxed(
    mut v_00_u03b1_2196_: *mut LeanObject,
    mut v_cmp_2197_: *mut LeanObject,
    mut v_t_2198_: *mut LeanObject,
    mut v_fallback_2199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2200_: *mut LeanObject = core::ptr::null_mut();
    v_res_2200_ =
        l_Std_TreeSet_Raw_maxD(v_00_u03b1_2196_, v_cmp_2197_, v_t_2198_, v_fallback_2199_);
    lean_dec(v_fallback_2199_);
    lean_dec(v_t_2198_);
    lean_dec_ref(v_cmp_2197_);
    return v_res_2200_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f___redArg(
    mut v_t_2201_: *mut LeanObject,
    mut v_n_2202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2201_, v_n_2202_);
    return v___x_2203_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(
    mut v_t_2204_: *mut LeanObject,
    mut v_n_2205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2206_: *mut LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Std_TreeSet_Raw_atIdx_x3f___redArg(v_t_2204_, v_n_2205_);
    lean_dec(v_t_2204_);
    return v_res_2206_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f(
    mut v_00_u03b1_2207_: *mut LeanObject,
    mut v_cmp_2208_: *mut LeanObject,
    mut v_t_2209_: *mut LeanObject,
    mut v_n_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    v___x_2211_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2209_, v_n_2210_);
    return v___x_2211_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f___boxed(
    mut v_00_u03b1_2212_: *mut LeanObject,
    mut v_cmp_2213_: *mut LeanObject,
    mut v_t_2214_: *mut LeanObject,
    mut v_n_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2216_: *mut LeanObject = core::ptr::null_mut();
    v_res_2216_ = l_Std_TreeSet_Raw_atIdx_x3f(v_00_u03b1_2212_, v_cmp_2213_, v_t_2214_, v_n_2215_);
    lean_dec(v_t_2214_);
    lean_dec_ref(v_cmp_2213_);
    return v_res_2216_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21___redArg(
    mut v_inst_2217_: *mut LeanObject,
    mut v_t_2218_: *mut LeanObject,
    mut v_n_2219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    v___x_2220_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2217_, v_t_2218_, v_n_2219_);
    return v___x_2220_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(
    mut v_inst_2221_: *mut LeanObject,
    mut v_t_2222_: *mut LeanObject,
    mut v_n_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2224_: *mut LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Std_TreeSet_Raw_atIdx_x21___redArg(v_inst_2221_, v_t_2222_, v_n_2223_);
    lean_dec(v_t_2222_);
    lean_dec(v_inst_2221_);
    return v_res_2224_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21(
    mut v_00_u03b1_2225_: *mut LeanObject,
    mut v_cmp_2226_: *mut LeanObject,
    mut v_inst_2227_: *mut LeanObject,
    mut v_t_2228_: *mut LeanObject,
    mut v_n_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    v___x_2230_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2227_, v_t_2228_, v_n_2229_);
    return v___x_2230_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21___boxed(
    mut v_00_u03b1_2231_: *mut LeanObject,
    mut v_cmp_2232_: *mut LeanObject,
    mut v_inst_2233_: *mut LeanObject,
    mut v_t_2234_: *mut LeanObject,
    mut v_n_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2236_: *mut LeanObject = core::ptr::null_mut();
    v_res_2236_ = l_Std_TreeSet_Raw_atIdx_x21(
        v_00_u03b1_2231_,
        v_cmp_2232_,
        v_inst_2233_,
        v_t_2234_,
        v_n_2235_,
    );
    lean_dec(v_t_2234_);
    lean_dec(v_inst_2233_);
    lean_dec_ref(v_cmp_2232_);
    return v_res_2236_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD___redArg(
    mut v_t_2237_: *mut LeanObject,
    mut v_n_2238_: *mut LeanObject,
    mut v_fallback_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    v___x_2240_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2237_, v_n_2238_, v_fallback_2239_);
    return v___x_2240_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD___redArg___boxed(
    mut v_t_2241_: *mut LeanObject,
    mut v_n_2242_: *mut LeanObject,
    mut v_fallback_2243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2244_: *mut LeanObject = core::ptr::null_mut();
    v_res_2244_ = l_Std_TreeSet_Raw_atIdxD___redArg(v_t_2241_, v_n_2242_, v_fallback_2243_);
    lean_dec(v_fallback_2243_);
    lean_dec(v_t_2241_);
    return v_res_2244_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD(
    mut v_00_u03b1_2245_: *mut LeanObject,
    mut v_cmp_2246_: *mut LeanObject,
    mut v_t_2247_: *mut LeanObject,
    mut v_n_2248_: *mut LeanObject,
    mut v_fallback_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2247_, v_n_2248_, v_fallback_2249_);
    return v___x_2250_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD___boxed(
    mut v_00_u03b1_2251_: *mut LeanObject,
    mut v_cmp_2252_: *mut LeanObject,
    mut v_t_2253_: *mut LeanObject,
    mut v_n_2254_: *mut LeanObject,
    mut v_fallback_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Std_TreeSet_Raw_atIdxD(
        v_00_u03b1_2251_,
        v_cmp_2252_,
        v_t_2253_,
        v_n_2254_,
        v_fallback_2255_,
    );
    lean_dec(v_fallback_2255_);
    lean_dec(v_t_2253_);
    lean_dec_ref(v_cmp_2252_);
    return v_res_2256_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x3f___redArg(
    mut v_cmp_2257_: *mut LeanObject,
    mut v_t_2258_: *mut LeanObject,
    mut v_k_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = lean_box(0);
    v___x_2261_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2257_,
        v_k_2259_,
        v___x_2260_,
        v_t_2258_,
    );
    return v___x_2261_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x3f(
    mut v_00_u03b1_2262_: *mut LeanObject,
    mut v_cmp_2263_: *mut LeanObject,
    mut v_t_2264_: *mut LeanObject,
    mut v_k_2265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    v___x_2266_ = lean_box(0);
    v___x_2267_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2263_,
        v_k_2265_,
        v___x_2266_,
        v_t_2264_,
    );
    return v___x_2267_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x3f___redArg(
    mut v_cmp_2268_: *mut LeanObject,
    mut v_t_2269_: *mut LeanObject,
    mut v_k_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    v___x_2271_ = lean_box(0);
    v___x_2272_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2268_,
        v_k_2270_,
        v___x_2271_,
        v_t_2269_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x3f(
    mut v_00_u03b1_2273_: *mut LeanObject,
    mut v_cmp_2274_: *mut LeanObject,
    mut v_t_2275_: *mut LeanObject,
    mut v_k_2276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    v___x_2277_ = lean_box(0);
    v___x_2278_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2274_,
        v_k_2276_,
        v___x_2277_,
        v_t_2275_,
    );
    return v___x_2278_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x3f___redArg(
    mut v_cmp_2279_: *mut LeanObject,
    mut v_t_2280_: *mut LeanObject,
    mut v_k_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    v___x_2282_ = lean_box(0);
    v___x_2283_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2279_,
        v_k_2281_,
        v___x_2282_,
        v_t_2280_,
    );
    return v___x_2283_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x3f(
    mut v_00_u03b1_2284_: *mut LeanObject,
    mut v_cmp_2285_: *mut LeanObject,
    mut v_t_2286_: *mut LeanObject,
    mut v_k_2287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    v___x_2288_ = lean_box(0);
    v___x_2289_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2285_,
        v_k_2287_,
        v___x_2288_,
        v_t_2286_,
    );
    return v___x_2289_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x3f___redArg(
    mut v_cmp_2290_: *mut LeanObject,
    mut v_t_2291_: *mut LeanObject,
    mut v_k_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    v___x_2293_ = lean_box(0);
    v___x_2294_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2290_,
        v_k_2292_,
        v___x_2293_,
        v_t_2291_,
    );
    return v___x_2294_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x3f(
    mut v_00_u03b1_2295_: *mut LeanObject,
    mut v_cmp_2296_: *mut LeanObject,
    mut v_t_2297_: *mut LeanObject,
    mut v_k_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = lean_box(0);
    v___x_2300_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2296_,
        v_k_2298_,
        v___x_2299_,
        v_t_2297_,
    );
    return v___x_2300_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ = l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2;
    v___x_2305_ = lean_unsigned_to_nat(14);
    v___x_2306_ = lean_unsigned_to_nat(22);
    v___x_2307_ = l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1;
    v___x_2308_ = l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0;
    v___x_2309_ = l_mkPanicMessageWithDecl(
        v___x_2308_,
        v___x_2307_,
        v___x_2306_,
        v___x_2305_,
        v___x_2304_,
    );
    return v___x_2309_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x21___redArg(
    mut v_cmp_2310_: *mut LeanObject,
    mut v_inst_2311_: *mut LeanObject,
    mut v_t_2312_: *mut LeanObject,
    mut v_k_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2314_ = lean_box(0);
    v___x_2315_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2310_,
        v_k_2313_,
        v___x_2314_,
        v_t_2312_,
    );
    if lean_obj_tag(v___x_2315_) == 0 {
        let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
        v___x_2316_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2317_ = l_panic___redArg(v_inst_2311_, v___x_2316_);
        return v___x_2317_;
    } else {
        let mut v_val_2318_: *mut LeanObject = core::ptr::null_mut();
        v_val_2318_ = lean_ctor_get(v___x_2315_, 0);
        lean_inc(v_val_2318_);
        lean_dec_ref_known(v___x_2315_, 1);
        return v_val_2318_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x21___redArg___boxed(
    mut v_cmp_2319_: *mut LeanObject,
    mut v_inst_2320_: *mut LeanObject,
    mut v_t_2321_: *mut LeanObject,
    mut v_k_2322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2323_: *mut LeanObject = core::ptr::null_mut();
    v_res_2323_ =
        l_Std_TreeSet_Raw_getGE_x21___redArg(v_cmp_2319_, v_inst_2320_, v_t_2321_, v_k_2322_);
    lean_dec(v_inst_2320_);
    return v_res_2323_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x21(
    mut v_00_u03b1_2324_: *mut LeanObject,
    mut v_cmp_2325_: *mut LeanObject,
    mut v_inst_2326_: *mut LeanObject,
    mut v_t_2327_: *mut LeanObject,
    mut v_k_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    v___x_2329_ = lean_box(0);
    v___x_2330_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2325_,
        v_k_2328_,
        v___x_2329_,
        v_t_2327_,
    );
    if lean_obj_tag(v___x_2330_) == 0 {
        let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
        v___x_2331_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2332_ = l_panic___redArg(v_inst_2326_, v___x_2331_);
        return v___x_2332_;
    } else {
        let mut v_val_2333_: *mut LeanObject = core::ptr::null_mut();
        v_val_2333_ = lean_ctor_get(v___x_2330_, 0);
        lean_inc(v_val_2333_);
        lean_dec_ref_known(v___x_2330_, 1);
        return v_val_2333_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x21___boxed(
    mut v_00_u03b1_2334_: *mut LeanObject,
    mut v_cmp_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
    mut v_t_2337_: *mut LeanObject,
    mut v_k_2338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2339_: *mut LeanObject = core::ptr::null_mut();
    v_res_2339_ = l_Std_TreeSet_Raw_getGE_x21(
        v_00_u03b1_2334_,
        v_cmp_2335_,
        v_inst_2336_,
        v_t_2337_,
        v_k_2338_,
    );
    lean_dec(v_inst_2336_);
    return v_res_2339_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21___redArg(
    mut v_cmp_2340_: *mut LeanObject,
    mut v_inst_2341_: *mut LeanObject,
    mut v_t_2342_: *mut LeanObject,
    mut v_k_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    v___x_2344_ = lean_box(0);
    v___x_2345_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2340_,
        v_k_2343_,
        v___x_2344_,
        v_t_2342_,
    );
    if lean_obj_tag(v___x_2345_) == 0 {
        let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
        v___x_2346_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2347_ = l_panic___redArg(v_inst_2341_, v___x_2346_);
        return v___x_2347_;
    } else {
        let mut v_val_2348_: *mut LeanObject = core::ptr::null_mut();
        v_val_2348_ = lean_ctor_get(v___x_2345_, 0);
        lean_inc(v_val_2348_);
        lean_dec_ref_known(v___x_2345_, 1);
        return v_val_2348_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21___redArg___boxed(
    mut v_cmp_2349_: *mut LeanObject,
    mut v_inst_2350_: *mut LeanObject,
    mut v_t_2351_: *mut LeanObject,
    mut v_k_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_res_2353_ =
        l_Std_TreeSet_Raw_getGT_x21___redArg(v_cmp_2349_, v_inst_2350_, v_t_2351_, v_k_2352_);
    lean_dec(v_inst_2350_);
    return v_res_2353_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21(
    mut v_00_u03b1_2354_: *mut LeanObject,
    mut v_cmp_2355_: *mut LeanObject,
    mut v_inst_2356_: *mut LeanObject,
    mut v_t_2357_: *mut LeanObject,
    mut v_k_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    v___x_2359_ = lean_box(0);
    v___x_2360_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2355_,
        v_k_2358_,
        v___x_2359_,
        v_t_2357_,
    );
    if lean_obj_tag(v___x_2360_) == 0 {
        let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
        v___x_2361_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2362_ = l_panic___redArg(v_inst_2356_, v___x_2361_);
        return v___x_2362_;
    } else {
        let mut v_val_2363_: *mut LeanObject = core::ptr::null_mut();
        v_val_2363_ = lean_ctor_get(v___x_2360_, 0);
        lean_inc(v_val_2363_);
        lean_dec_ref_known(v___x_2360_, 1);
        return v_val_2363_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21___boxed(
    mut v_00_u03b1_2364_: *mut LeanObject,
    mut v_cmp_2365_: *mut LeanObject,
    mut v_inst_2366_: *mut LeanObject,
    mut v_t_2367_: *mut LeanObject,
    mut v_k_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2369_: *mut LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Std_TreeSet_Raw_getGT_x21(
        v_00_u03b1_2364_,
        v_cmp_2365_,
        v_inst_2366_,
        v_t_2367_,
        v_k_2368_,
    );
    lean_dec(v_inst_2366_);
    return v_res_2369_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21___redArg(
    mut v_cmp_2370_: *mut LeanObject,
    mut v_inst_2371_: *mut LeanObject,
    mut v_t_2372_: *mut LeanObject,
    mut v_k_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    v___x_2374_ = lean_box(0);
    v___x_2375_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2370_,
        v_k_2373_,
        v___x_2374_,
        v_t_2372_,
    );
    if lean_obj_tag(v___x_2375_) == 0 {
        let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
        v___x_2376_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2377_ = l_panic___redArg(v_inst_2371_, v___x_2376_);
        return v___x_2377_;
    } else {
        let mut v_val_2378_: *mut LeanObject = core::ptr::null_mut();
        v_val_2378_ = lean_ctor_get(v___x_2375_, 0);
        lean_inc(v_val_2378_);
        lean_dec_ref_known(v___x_2375_, 1);
        return v_val_2378_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21___redArg___boxed(
    mut v_cmp_2379_: *mut LeanObject,
    mut v_inst_2380_: *mut LeanObject,
    mut v_t_2381_: *mut LeanObject,
    mut v_k_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2383_: *mut LeanObject = core::ptr::null_mut();
    v_res_2383_ =
        l_Std_TreeSet_Raw_getLE_x21___redArg(v_cmp_2379_, v_inst_2380_, v_t_2381_, v_k_2382_);
    lean_dec(v_inst_2380_);
    return v_res_2383_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21(
    mut v_00_u03b1_2384_: *mut LeanObject,
    mut v_cmp_2385_: *mut LeanObject,
    mut v_inst_2386_: *mut LeanObject,
    mut v_t_2387_: *mut LeanObject,
    mut v_k_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    v___x_2389_ = lean_box(0);
    v___x_2390_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2385_,
        v_k_2388_,
        v___x_2389_,
        v_t_2387_,
    );
    if lean_obj_tag(v___x_2390_) == 0 {
        let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
        v___x_2391_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2392_ = l_panic___redArg(v_inst_2386_, v___x_2391_);
        return v___x_2392_;
    } else {
        let mut v_val_2393_: *mut LeanObject = core::ptr::null_mut();
        v_val_2393_ = lean_ctor_get(v___x_2390_, 0);
        lean_inc(v_val_2393_);
        lean_dec_ref_known(v___x_2390_, 1);
        return v_val_2393_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21___boxed(
    mut v_00_u03b1_2394_: *mut LeanObject,
    mut v_cmp_2395_: *mut LeanObject,
    mut v_inst_2396_: *mut LeanObject,
    mut v_t_2397_: *mut LeanObject,
    mut v_k_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2399_: *mut LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Std_TreeSet_Raw_getLE_x21(
        v_00_u03b1_2394_,
        v_cmp_2395_,
        v_inst_2396_,
        v_t_2397_,
        v_k_2398_,
    );
    lean_dec(v_inst_2396_);
    return v_res_2399_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21___redArg(
    mut v_cmp_2400_: *mut LeanObject,
    mut v_inst_2401_: *mut LeanObject,
    mut v_t_2402_: *mut LeanObject,
    mut v_k_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    v___x_2404_ = lean_box(0);
    v___x_2405_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2400_,
        v_k_2403_,
        v___x_2404_,
        v_t_2402_,
    );
    if lean_obj_tag(v___x_2405_) == 0 {
        let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
        v___x_2406_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2407_ = l_panic___redArg(v_inst_2401_, v___x_2406_);
        return v___x_2407_;
    } else {
        let mut v_val_2408_: *mut LeanObject = core::ptr::null_mut();
        v_val_2408_ = lean_ctor_get(v___x_2405_, 0);
        lean_inc(v_val_2408_);
        lean_dec_ref_known(v___x_2405_, 1);
        return v_val_2408_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21___redArg___boxed(
    mut v_cmp_2409_: *mut LeanObject,
    mut v_inst_2410_: *mut LeanObject,
    mut v_t_2411_: *mut LeanObject,
    mut v_k_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
    v_res_2413_ =
        l_Std_TreeSet_Raw_getLT_x21___redArg(v_cmp_2409_, v_inst_2410_, v_t_2411_, v_k_2412_);
    lean_dec(v_inst_2410_);
    return v_res_2413_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21(
    mut v_00_u03b1_2414_: *mut LeanObject,
    mut v_cmp_2415_: *mut LeanObject,
    mut v_inst_2416_: *mut LeanObject,
    mut v_t_2417_: *mut LeanObject,
    mut v_k_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    v___x_2419_ = lean_box(0);
    v___x_2420_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2415_,
        v_k_2418_,
        v___x_2419_,
        v_t_2417_,
    );
    if lean_obj_tag(v___x_2420_) == 0 {
        let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
        v___x_2421_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2422_ = l_panic___redArg(v_inst_2416_, v___x_2421_);
        return v___x_2422_;
    } else {
        let mut v_val_2423_: *mut LeanObject = core::ptr::null_mut();
        v_val_2423_ = lean_ctor_get(v___x_2420_, 0);
        lean_inc(v_val_2423_);
        lean_dec_ref_known(v___x_2420_, 1);
        return v_val_2423_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21___boxed(
    mut v_00_u03b1_2424_: *mut LeanObject,
    mut v_cmp_2425_: *mut LeanObject,
    mut v_inst_2426_: *mut LeanObject,
    mut v_t_2427_: *mut LeanObject,
    mut v_k_2428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2429_: *mut LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Std_TreeSet_Raw_getLT_x21(
        v_00_u03b1_2424_,
        v_cmp_2425_,
        v_inst_2426_,
        v_t_2427_,
        v_k_2428_,
    );
    lean_dec(v_inst_2426_);
    return v_res_2429_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGED___redArg(
    mut v_cmp_2430_: *mut LeanObject,
    mut v_t_2431_: *mut LeanObject,
    mut v_k_2432_: *mut LeanObject,
    mut v_fallback_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    v___x_2434_ = lean_box(0);
    v___x_2435_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2430_,
        v_k_2432_,
        v___x_2434_,
        v_t_2431_,
    );
    if lean_obj_tag(v___x_2435_) == 0 {
        lean_inc(v_fallback_2433_);
        return v_fallback_2433_;
    } else {
        let mut v_val_2436_: *mut LeanObject = core::ptr::null_mut();
        v_val_2436_ = lean_ctor_get(v___x_2435_, 0);
        lean_inc(v_val_2436_);
        lean_dec_ref_known(v___x_2435_, 1);
        return v_val_2436_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGED___redArg___boxed(
    mut v_cmp_2437_: *mut LeanObject,
    mut v_t_2438_: *mut LeanObject,
    mut v_k_2439_: *mut LeanObject,
    mut v_fallback_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2441_: *mut LeanObject = core::ptr::null_mut();
    v_res_2441_ =
        l_Std_TreeSet_Raw_getGED___redArg(v_cmp_2437_, v_t_2438_, v_k_2439_, v_fallback_2440_);
    lean_dec(v_fallback_2440_);
    return v_res_2441_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGED(
    mut v_00_u03b1_2442_: *mut LeanObject,
    mut v_cmp_2443_: *mut LeanObject,
    mut v_t_2444_: *mut LeanObject,
    mut v_k_2445_: *mut LeanObject,
    mut v_fallback_2446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    v___x_2447_ = lean_box(0);
    v___x_2448_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2443_,
        v_k_2445_,
        v___x_2447_,
        v_t_2444_,
    );
    if lean_obj_tag(v___x_2448_) == 0 {
        lean_inc(v_fallback_2446_);
        return v_fallback_2446_;
    } else {
        let mut v_val_2449_: *mut LeanObject = core::ptr::null_mut();
        v_val_2449_ = lean_ctor_get(v___x_2448_, 0);
        lean_inc(v_val_2449_);
        lean_dec_ref_known(v___x_2448_, 1);
        return v_val_2449_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGED___boxed(
    mut v_00_u03b1_2450_: *mut LeanObject,
    mut v_cmp_2451_: *mut LeanObject,
    mut v_t_2452_: *mut LeanObject,
    mut v_k_2453_: *mut LeanObject,
    mut v_fallback_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2455_: *mut LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Std_TreeSet_Raw_getGED(
        v_00_u03b1_2450_,
        v_cmp_2451_,
        v_t_2452_,
        v_k_2453_,
        v_fallback_2454_,
    );
    lean_dec(v_fallback_2454_);
    return v_res_2455_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD___redArg(
    mut v_cmp_2456_: *mut LeanObject,
    mut v_t_2457_: *mut LeanObject,
    mut v_k_2458_: *mut LeanObject,
    mut v_fallback_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    v___x_2460_ = lean_box(0);
    v___x_2461_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2456_,
        v_k_2458_,
        v___x_2460_,
        v_t_2457_,
    );
    if lean_obj_tag(v___x_2461_) == 0 {
        lean_inc(v_fallback_2459_);
        return v_fallback_2459_;
    } else {
        let mut v_val_2462_: *mut LeanObject = core::ptr::null_mut();
        v_val_2462_ = lean_ctor_get(v___x_2461_, 0);
        lean_inc(v_val_2462_);
        lean_dec_ref_known(v___x_2461_, 1);
        return v_val_2462_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD___redArg___boxed(
    mut v_cmp_2463_: *mut LeanObject,
    mut v_t_2464_: *mut LeanObject,
    mut v_k_2465_: *mut LeanObject,
    mut v_fallback_2466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2467_: *mut LeanObject = core::ptr::null_mut();
    v_res_2467_ =
        l_Std_TreeSet_Raw_getGTD___redArg(v_cmp_2463_, v_t_2464_, v_k_2465_, v_fallback_2466_);
    lean_dec(v_fallback_2466_);
    return v_res_2467_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD(
    mut v_00_u03b1_2468_: *mut LeanObject,
    mut v_cmp_2469_: *mut LeanObject,
    mut v_t_2470_: *mut LeanObject,
    mut v_k_2471_: *mut LeanObject,
    mut v_fallback_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2473_ = lean_box(0);
    v___x_2474_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2469_,
        v_k_2471_,
        v___x_2473_,
        v_t_2470_,
    );
    if lean_obj_tag(v___x_2474_) == 0 {
        lean_inc(v_fallback_2472_);
        return v_fallback_2472_;
    } else {
        let mut v_val_2475_: *mut LeanObject = core::ptr::null_mut();
        v_val_2475_ = lean_ctor_get(v___x_2474_, 0);
        lean_inc(v_val_2475_);
        lean_dec_ref_known(v___x_2474_, 1);
        return v_val_2475_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD___boxed(
    mut v_00_u03b1_2476_: *mut LeanObject,
    mut v_cmp_2477_: *mut LeanObject,
    mut v_t_2478_: *mut LeanObject,
    mut v_k_2479_: *mut LeanObject,
    mut v_fallback_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Std_TreeSet_Raw_getGTD(
        v_00_u03b1_2476_,
        v_cmp_2477_,
        v_t_2478_,
        v_k_2479_,
        v_fallback_2480_,
    );
    lean_dec(v_fallback_2480_);
    return v_res_2481_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLED___redArg(
    mut v_cmp_2482_: *mut LeanObject,
    mut v_t_2483_: *mut LeanObject,
    mut v_k_2484_: *mut LeanObject,
    mut v_fallback_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    v___x_2486_ = lean_box(0);
    v___x_2487_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2482_,
        v_k_2484_,
        v___x_2486_,
        v_t_2483_,
    );
    if lean_obj_tag(v___x_2487_) == 0 {
        lean_inc(v_fallback_2485_);
        return v_fallback_2485_;
    } else {
        let mut v_val_2488_: *mut LeanObject = core::ptr::null_mut();
        v_val_2488_ = lean_ctor_get(v___x_2487_, 0);
        lean_inc(v_val_2488_);
        lean_dec_ref_known(v___x_2487_, 1);
        return v_val_2488_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLED___redArg___boxed(
    mut v_cmp_2489_: *mut LeanObject,
    mut v_t_2490_: *mut LeanObject,
    mut v_k_2491_: *mut LeanObject,
    mut v_fallback_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ =
        l_Std_TreeSet_Raw_getLED___redArg(v_cmp_2489_, v_t_2490_, v_k_2491_, v_fallback_2492_);
    lean_dec(v_fallback_2492_);
    return v_res_2493_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLED(
    mut v_00_u03b1_2494_: *mut LeanObject,
    mut v_cmp_2495_: *mut LeanObject,
    mut v_t_2496_: *mut LeanObject,
    mut v_k_2497_: *mut LeanObject,
    mut v_fallback_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v___x_2499_ = lean_box(0);
    v___x_2500_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2495_,
        v_k_2497_,
        v___x_2499_,
        v_t_2496_,
    );
    if lean_obj_tag(v___x_2500_) == 0 {
        lean_inc(v_fallback_2498_);
        return v_fallback_2498_;
    } else {
        let mut v_val_2501_: *mut LeanObject = core::ptr::null_mut();
        v_val_2501_ = lean_ctor_get(v___x_2500_, 0);
        lean_inc(v_val_2501_);
        lean_dec_ref_known(v___x_2500_, 1);
        return v_val_2501_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLED___boxed(
    mut v_00_u03b1_2502_: *mut LeanObject,
    mut v_cmp_2503_: *mut LeanObject,
    mut v_t_2504_: *mut LeanObject,
    mut v_k_2505_: *mut LeanObject,
    mut v_fallback_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2507_: *mut LeanObject = core::ptr::null_mut();
    v_res_2507_ = l_Std_TreeSet_Raw_getLED(
        v_00_u03b1_2502_,
        v_cmp_2503_,
        v_t_2504_,
        v_k_2505_,
        v_fallback_2506_,
    );
    lean_dec(v_fallback_2506_);
    return v_res_2507_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD___redArg(
    mut v_cmp_2508_: *mut LeanObject,
    mut v_t_2509_: *mut LeanObject,
    mut v_k_2510_: *mut LeanObject,
    mut v_fallback_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2512_ = lean_box(0);
    v___x_2513_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2508_,
        v_k_2510_,
        v___x_2512_,
        v_t_2509_,
    );
    if lean_obj_tag(v___x_2513_) == 0 {
        lean_inc(v_fallback_2511_);
        return v_fallback_2511_;
    } else {
        let mut v_val_2514_: *mut LeanObject = core::ptr::null_mut();
        v_val_2514_ = lean_ctor_get(v___x_2513_, 0);
        lean_inc(v_val_2514_);
        lean_dec_ref_known(v___x_2513_, 1);
        return v_val_2514_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD___redArg___boxed(
    mut v_cmp_2515_: *mut LeanObject,
    mut v_t_2516_: *mut LeanObject,
    mut v_k_2517_: *mut LeanObject,
    mut v_fallback_2518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2519_: *mut LeanObject = core::ptr::null_mut();
    v_res_2519_ =
        l_Std_TreeSet_Raw_getLTD___redArg(v_cmp_2515_, v_t_2516_, v_k_2517_, v_fallback_2518_);
    lean_dec(v_fallback_2518_);
    return v_res_2519_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD(
    mut v_00_u03b1_2520_: *mut LeanObject,
    mut v_cmp_2521_: *mut LeanObject,
    mut v_t_2522_: *mut LeanObject,
    mut v_k_2523_: *mut LeanObject,
    mut v_fallback_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    v___x_2525_ = lean_box(0);
    v___x_2526_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2521_,
        v_k_2523_,
        v___x_2525_,
        v_t_2522_,
    );
    if lean_obj_tag(v___x_2526_) == 0 {
        lean_inc(v_fallback_2524_);
        return v_fallback_2524_;
    } else {
        let mut v_val_2527_: *mut LeanObject = core::ptr::null_mut();
        v_val_2527_ = lean_ctor_get(v___x_2526_, 0);
        lean_inc(v_val_2527_);
        lean_dec_ref_known(v___x_2526_, 1);
        return v_val_2527_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD___boxed(
    mut v_00_u03b1_2528_: *mut LeanObject,
    mut v_cmp_2529_: *mut LeanObject,
    mut v_t_2530_: *mut LeanObject,
    mut v_k_2531_: *mut LeanObject,
    mut v_fallback_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2533_: *mut LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Std_TreeSet_Raw_getLTD(
        v_00_u03b1_2528_,
        v_cmp_2529_,
        v_t_2530_,
        v_k_2531_,
        v_fallback_2532_,
    );
    lean_dec(v_fallback_2532_);
    return v_res_2533_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___redArg___lam__0(
    mut v_f_2534_: *mut LeanObject,
    mut v_a_2535_: *mut LeanObject,
    mut v_x_2536_: *mut LeanObject,
) -> u8 {
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    v___x_2537_ = lean_apply_1(v_f_2534_, v_a_2535_);
    v___x_2538_ = (lean_unbox(v___x_2537_) as u8);
    return v___x_2538_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(
    mut v_f_2539_: *mut LeanObject,
    mut v_a_2540_: *mut LeanObject,
    mut v_x_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2542_: u8 = 0;
    let mut v_r_2543_: *mut LeanObject = core::ptr::null_mut();
    v_res_2542_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_2539_, v_a_2540_, v_x_2541_);
    v_r_2543_ = lean_box((v_res_2542_) as usize);
    return v_r_2543_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___redArg(
    mut v_f_2544_: *mut LeanObject,
    mut v_t_2545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    v___f_2546_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2546_, 0, v_f_2544_);
    v___x_2547_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_2546_, v_t_2545_);
    return v___x_2547_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter(
    mut v_00_u03b1_2548_: *mut LeanObject,
    mut v_cmp_2549_: *mut LeanObject,
    mut v_f_2550_: *mut LeanObject,
    mut v_t_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    v___f_2552_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2552_, 0, v_f_2550_);
    v___x_2553_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_2552_, v_t_2551_);
    return v___x_2553_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___boxed(
    mut v_00_u03b1_2554_: *mut LeanObject,
    mut v_cmp_2555_: *mut LeanObject,
    mut v_f_2556_: *mut LeanObject,
    mut v_t_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2558_: *mut LeanObject = core::ptr::null_mut();
    v_res_2558_ = l_Std_TreeSet_Raw_filter(v_00_u03b1_2554_, v_cmp_2555_, v_f_2556_, v_t_2557_);
    lean_dec_ref(v_cmp_2555_);
    return v_res_2558_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM___redArg___lam__0(
    mut v_f_2559_: *mut LeanObject,
    mut v_c_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
    mut v_x_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    v___x_2563_ = lean_apply_2(v_f_2559_, v_c_2560_, v_a_2561_);
    return v___x_2563_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM___redArg(
    mut v_inst_2564_: *mut LeanObject,
    mut v_f_2565_: *mut LeanObject,
    mut v_init_2566_: *mut LeanObject,
    mut v_t_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    v___f_2568_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2568_, 0, v_f_2565_);
    v___x_2569_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2564_,
        v___f_2568_,
        v_init_2566_,
        v_t_2567_,
    );
    return v___x_2569_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM(
    mut v_00_u03b1_2570_: *mut LeanObject,
    mut v_cmp_2571_: *mut LeanObject,
    mut v_00_u03b4_2572_: *mut LeanObject,
    mut v_m_2573_: *mut LeanObject,
    mut v_inst_2574_: *mut LeanObject,
    mut v_f_2575_: *mut LeanObject,
    mut v_init_2576_: *mut LeanObject,
    mut v_t_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    v___f_2578_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2578_, 0, v_f_2575_);
    v___x_2579_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2574_,
        v___f_2578_,
        v_init_2576_,
        v_t_2577_,
    );
    return v___x_2579_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM___boxed(
    mut v_00_u03b1_2580_: *mut LeanObject,
    mut v_cmp_2581_: *mut LeanObject,
    mut v_00_u03b4_2582_: *mut LeanObject,
    mut v_m_2583_: *mut LeanObject,
    mut v_inst_2584_: *mut LeanObject,
    mut v_f_2585_: *mut LeanObject,
    mut v_init_2586_: *mut LeanObject,
    mut v_t_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2588_: *mut LeanObject = core::ptr::null_mut();
    v_res_2588_ = l_Std_TreeSet_Raw_foldlM(
        v_00_u03b1_2580_,
        v_cmp_2581_,
        v_00_u03b4_2582_,
        v_m_2583_,
        v_inst_2584_,
        v_f_2585_,
        v_init_2586_,
        v_t_2587_,
    );
    lean_dec_ref(v_cmp_2581_);
    return v_res_2588_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldl___redArg(
    mut v_f_2589_: *mut LeanObject,
    mut v_init_2590_: *mut LeanObject,
    mut v_t_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    v___f_2592_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2592_, 0, v_f_2589_);
    v___x_2593_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2592_, v_init_2590_, v_t_2591_);
    return v___x_2593_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldl(
    mut v_00_u03b1_2594_: *mut LeanObject,
    mut v_cmp_2595_: *mut LeanObject,
    mut v_00_u03b4_2596_: *mut LeanObject,
    mut v_f_2597_: *mut LeanObject,
    mut v_init_2598_: *mut LeanObject,
    mut v_t_2599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    v___f_2600_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2600_, 0, v_f_2597_);
    v___x_2601_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2600_, v_init_2598_, v_t_2599_);
    return v___x_2601_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldl___boxed(
    mut v_00_u03b1_2602_: *mut LeanObject,
    mut v_cmp_2603_: *mut LeanObject,
    mut v_00_u03b4_2604_: *mut LeanObject,
    mut v_f_2605_: *mut LeanObject,
    mut v_init_2606_: *mut LeanObject,
    mut v_t_2607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2608_: *mut LeanObject = core::ptr::null_mut();
    v_res_2608_ = l_Std_TreeSet_Raw_foldl(
        v_00_u03b1_2602_,
        v_cmp_2603_,
        v_00_u03b4_2604_,
        v_f_2605_,
        v_init_2606_,
        v_t_2607_,
    );
    lean_dec_ref(v_cmp_2603_);
    return v_res_2608_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM___redArg___lam__0(
    mut v_f_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_x_2611_: *mut LeanObject,
    mut v_acc_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2613_ = lean_apply_2(v_f_2609_, v_a_2610_, v_acc_2612_);
    return v___x_2613_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM___redArg(
    mut v_inst_2614_: *mut LeanObject,
    mut v_f_2615_: *mut LeanObject,
    mut v_init_2616_: *mut LeanObject,
    mut v_t_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    v___f_2618_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2618_, 0, v_f_2615_);
    v___x_2619_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2614_,
        v___f_2618_,
        v_init_2616_,
        v_t_2617_,
    );
    return v___x_2619_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM(
    mut v_00_u03b1_2620_: *mut LeanObject,
    mut v_cmp_2621_: *mut LeanObject,
    mut v_00_u03b4_2622_: *mut LeanObject,
    mut v_m_2623_: *mut LeanObject,
    mut v_inst_2624_: *mut LeanObject,
    mut v_f_2625_: *mut LeanObject,
    mut v_init_2626_: *mut LeanObject,
    mut v_t_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    v___f_2628_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2628_, 0, v_f_2625_);
    v___x_2629_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2624_,
        v___f_2628_,
        v_init_2626_,
        v_t_2627_,
    );
    return v___x_2629_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM___boxed(
    mut v_00_u03b1_2630_: *mut LeanObject,
    mut v_cmp_2631_: *mut LeanObject,
    mut v_00_u03b4_2632_: *mut LeanObject,
    mut v_m_2633_: *mut LeanObject,
    mut v_inst_2634_: *mut LeanObject,
    mut v_f_2635_: *mut LeanObject,
    mut v_init_2636_: *mut LeanObject,
    mut v_t_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2638_: *mut LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Std_TreeSet_Raw_foldrM(
        v_00_u03b1_2630_,
        v_cmp_2631_,
        v_00_u03b4_2632_,
        v_m_2633_,
        v_inst_2634_,
        v_f_2635_,
        v_init_2636_,
        v_t_2637_,
    );
    lean_dec_ref(v_cmp_2631_);
    return v_res_2638_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldr___redArg___lam__0(
    mut v_f_2639_: *mut LeanObject,
    mut v_x1_2640_: *mut LeanObject,
    mut v_x2_2641_: *mut LeanObject,
    mut v_x3_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    v___x_2643_ = lean_apply_2(v_f_2639_, v_x1_2640_, v_x3_2642_);
    return v___x_2643_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldr___redArg(
    mut v_f_2663_: *mut LeanObject,
    mut v_init_2664_: *mut LeanObject,
    mut v_t_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    v___f_2666_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2666_, 0, v_f_2663_);
    v___x_2667_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v___x_2668_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_2667_,
        v___f_2666_,
        v_init_2664_,
        v_t_2665_,
    );
    return v___x_2668_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldr(
    mut v_00_u03b1_2669_: *mut LeanObject,
    mut v_cmp_2670_: *mut LeanObject,
    mut v_00_u03b4_2671_: *mut LeanObject,
    mut v_f_2672_: *mut LeanObject,
    mut v_init_2673_: *mut LeanObject,
    mut v_t_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    v___f_2675_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2675_, 0, v_f_2672_);
    v___x_2676_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v___x_2677_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_2676_,
        v___f_2675_,
        v_init_2673_,
        v_t_2674_,
    );
    return v___x_2677_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldr___boxed(
    mut v_00_u03b1_2678_: *mut LeanObject,
    mut v_cmp_2679_: *mut LeanObject,
    mut v_00_u03b4_2680_: *mut LeanObject,
    mut v_f_2681_: *mut LeanObject,
    mut v_init_2682_: *mut LeanObject,
    mut v_t_2683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2684_: *mut LeanObject = core::ptr::null_mut();
    v_res_2684_ = l_Std_TreeSet_Raw_foldr(
        v_00_u03b1_2678_,
        v_cmp_2679_,
        v_00_u03b4_2680_,
        v_f_2681_,
        v_init_2682_,
        v_t_2683_,
    );
    lean_dec_ref(v_cmp_2679_);
    return v_res_2684_;
}
pub unsafe fn l_Std_TreeSet_Raw_partition___redArg___lam__0(
    mut v_f_2685_: *mut LeanObject,
    mut v_cmp_2686_: *mut LeanObject,
    mut v_x_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
    mut v_b_2689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2690_ = lean_ctor_get(v_x_2687_, 0);
                v_snd_2691_ = lean_ctor_get(v_x_2687_, 1);
                v_isSharedCheck_2705_ = (!lean_is_exclusive(v_x_2687_)) as u8;
                if v_isSharedCheck_2705_ == 0 {
                    v___x_2693_ = v_x_2687_;
                    v_isShared_2694_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2691_);
                    lean_inc(v_fst_2690_);
                    lean_dec(v_x_2687_);
                    v___x_2693_ = lean_box(0);
                    v_isShared_2694_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_2688_);
                v___x_2695_ = lean_apply_1(v_f_2685_, v_a_2688_);
                v___x_2696_ = (lean_unbox(v___x_2695_) as u8);
                if v___x_2696_ == 0 {
                    v___x_2697_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                        v_cmp_2686_,
                        v_a_2688_,
                        v_b_2689_,
                        v_snd_2691_,
                    );
                    if v_isShared_2694_ == 0 {
                        lean_ctor_set(v___x_2693_, 1, v___x_2697_);
                        v___x_2699_ = v___x_2693_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_fst_2690_);
                        lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2697_);
                        v___x_2699_ = v_reuseFailAlloc_2700_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2701_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                        v_cmp_2686_,
                        v_a_2688_,
                        v_b_2689_,
                        v_fst_2690_,
                    );
                    if v_isShared_2694_ == 0 {
                        lean_ctor_set(v___x_2693_, 0, v___x_2701_);
                        v___x_2703_ = v___x_2693_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
                        lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_snd_2691_);
                        v___x_2703_ = v_reuseFailAlloc_2704_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2699_;
            }
            3 => {
                return v___x_2703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_partition___redArg(
    mut v_cmp_2708_: *mut LeanObject,
    mut v_f_2709_: *mut LeanObject,
    mut v_t_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2711_ = lean_alloc_closure(
                    l_Std_TreeSet_Raw_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2711_, 0, v_f_2709_);
                lean_closure_set(v___f_2711_, 1, v_cmp_2708_);
                v___x_2712_ = l_Std_TreeSet_Raw_partition___redArg___closed__0;
                v_p_2713_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_2711_,
                    v___x_2712_,
                    v_t_2710_,
                );
                v_fst_2714_ = lean_ctor_get(v_p_2713_, 0);
                v_snd_2715_ = lean_ctor_get(v_p_2713_, 1);
                v_isSharedCheck_2722_ = (!lean_is_exclusive(v_p_2713_)) as u8;
                if v_isSharedCheck_2722_ == 0 {
                    v___x_2717_ = v_p_2713_;
                    v_isShared_2718_ = v_isSharedCheck_2722_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2715_);
                    lean_inc(v_fst_2714_);
                    lean_dec(v_p_2713_);
                    v___x_2717_ = lean_box(0);
                    v_isShared_2718_ = v_isSharedCheck_2722_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2718_ == 0 {
                    v___x_2720_ = v___x_2717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_fst_2714_);
                    lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_snd_2715_);
                    v___x_2720_ = v_reuseFailAlloc_2721_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_partition(
    mut v_00_u03b1_2723_: *mut LeanObject,
    mut v_cmp_2724_: *mut LeanObject,
    mut v_f_2725_: *mut LeanObject,
    mut v_t_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2727_ = lean_alloc_closure(
                    l_Std_TreeSet_Raw_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2727_, 0, v_f_2725_);
                lean_closure_set(v___f_2727_, 1, v_cmp_2724_);
                v___x_2728_ = l_Std_TreeSet_Raw_partition___redArg___closed__0;
                v_p_2729_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_2727_,
                    v___x_2728_,
                    v_t_2726_,
                );
                v_fst_2730_ = lean_ctor_get(v_p_2729_, 0);
                v_snd_2731_ = lean_ctor_get(v_p_2729_, 1);
                v_isSharedCheck_2738_ = (!lean_is_exclusive(v_p_2729_)) as u8;
                if v_isSharedCheck_2738_ == 0 {
                    v___x_2733_ = v_p_2729_;
                    v_isShared_2734_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2731_);
                    lean_inc(v_fst_2730_);
                    lean_dec(v_p_2729_);
                    v___x_2733_ = lean_box(0);
                    v_isShared_2734_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2734_ == 0 {
                    v___x_2736_ = v___x_2733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_fst_2730_);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_snd_2731_);
                    v___x_2736_ = v_reuseFailAlloc_2737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_forM___redArg___lam__0(
    mut v_f_2739_: *mut LeanObject,
    mut v_x_2740_: *mut LeanObject,
    mut v_k_2741_: *mut LeanObject,
    mut v_v_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    v___x_2743_ = lean_apply_1(v_f_2739_, v_k_2741_);
    return v___x_2743_;
}
pub unsafe fn l_Std_TreeSet_Raw_forM___redArg(
    mut v_inst_2744_: *mut LeanObject,
    mut v_f_2745_: *mut LeanObject,
    mut v_t_2746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    v___f_2747_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2747_, 0, v_f_2745_);
    v___x_2748_ = lean_box(0);
    v___x_2749_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2744_,
        v___f_2747_,
        v___x_2748_,
        v_t_2746_,
    );
    return v___x_2749_;
}
pub unsafe fn l_Std_TreeSet_Raw_forM(
    mut v_00_u03b1_2750_: *mut LeanObject,
    mut v_cmp_2751_: *mut LeanObject,
    mut v_m_2752_: *mut LeanObject,
    mut v_inst_2753_: *mut LeanObject,
    mut v_f_2754_: *mut LeanObject,
    mut v_t_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    v___f_2756_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2756_, 0, v_f_2754_);
    v___x_2757_ = lean_box(0);
    v___x_2758_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2753_,
        v___f_2756_,
        v___x_2757_,
        v_t_2755_,
    );
    return v___x_2758_;
}
pub unsafe fn l_Std_TreeSet_Raw_forM___boxed(
    mut v_00_u03b1_2759_: *mut LeanObject,
    mut v_cmp_2760_: *mut LeanObject,
    mut v_m_2761_: *mut LeanObject,
    mut v_inst_2762_: *mut LeanObject,
    mut v_f_2763_: *mut LeanObject,
    mut v_t_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2765_: *mut LeanObject = core::ptr::null_mut();
    v_res_2765_ = l_Std_TreeSet_Raw_forM(
        v_00_u03b1_2759_,
        v_cmp_2760_,
        v_m_2761_,
        v_inst_2762_,
        v_f_2763_,
        v_t_2764_,
    );
    lean_dec_ref(v_cmp_2760_);
    return v_res_2765_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___redArg___lam__0(
    mut v_f_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
    mut v_b_2768_: *mut LeanObject,
    mut v_c_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    v___x_2770_ = lean_apply_2(v_f_2766_, v_a_2767_, v_c_2769_);
    return v___x_2770_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___redArg___lam__1(
    mut v_toPure_2771_: *mut LeanObject,
    mut v_____do__lift_2772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    v_a_2773_ = lean_ctor_get(v_____do__lift_2772_, 0);
    lean_inc(v_a_2773_);
    lean_dec_ref(v_____do__lift_2772_);
    v___x_2774_ = lean_apply_2(v_toPure_2771_, lean_box(0), v_a_2773_);
    return v___x_2774_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___redArg(
    mut v_inst_2775_: *mut LeanObject,
    mut v_f_2776_: *mut LeanObject,
    mut v_init_2777_: *mut LeanObject,
    mut v_t_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2779_ = lean_ctor_get(v_inst_2775_, 0);
    v_toBind_2780_ = lean_ctor_get(v_inst_2775_, 1);
    lean_inc(v_toBind_2780_);
    v_toPure_2781_ = lean_ctor_get(v_toApplicative_2779_, 1);
    lean_inc(v_toPure_2781_);
    v___f_2782_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2782_, 0, v_f_2776_);
    v___x_2783_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2775_,
        v___f_2782_,
        v_init_2777_,
        v_t_2778_,
    );
    v___f_2784_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2784_, 0, v_toPure_2781_);
    v___x_2785_ = lean_apply_4(
        v_toBind_2780_,
        lean_box(0),
        lean_box(0),
        v___x_2783_,
        v___f_2784_,
    );
    return v___x_2785_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn(
    mut v_00_u03b1_2786_: *mut LeanObject,
    mut v_cmp_2787_: *mut LeanObject,
    mut v_00_u03b4_2788_: *mut LeanObject,
    mut v_m_2789_: *mut LeanObject,
    mut v_inst_2790_: *mut LeanObject,
    mut v_f_2791_: *mut LeanObject,
    mut v_init_2792_: *mut LeanObject,
    mut v_t_2793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2794_ = lean_ctor_get(v_inst_2790_, 0);
    v_toBind_2795_ = lean_ctor_get(v_inst_2790_, 1);
    lean_inc(v_toBind_2795_);
    v_toPure_2796_ = lean_ctor_get(v_toApplicative_2794_, 1);
    lean_inc(v_toPure_2796_);
    v___f_2797_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2797_, 0, v_f_2791_);
    v___x_2798_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2790_,
        v___f_2797_,
        v_init_2792_,
        v_t_2793_,
    );
    v___f_2799_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2799_, 0, v_toPure_2796_);
    v___x_2800_ = lean_apply_4(
        v_toBind_2795_,
        lean_box(0),
        lean_box(0),
        v___x_2798_,
        v___f_2799_,
    );
    return v___x_2800_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___boxed(
    mut v_00_u03b1_2801_: *mut LeanObject,
    mut v_cmp_2802_: *mut LeanObject,
    mut v_00_u03b4_2803_: *mut LeanObject,
    mut v_m_2804_: *mut LeanObject,
    mut v_inst_2805_: *mut LeanObject,
    mut v_f_2806_: *mut LeanObject,
    mut v_init_2807_: *mut LeanObject,
    mut v_t_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2809_: *mut LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_Std_TreeSet_Raw_forIn(
        v_00_u03b1_2801_,
        v_cmp_2802_,
        v_00_u03b4_2803_,
        v_m_2804_,
        v_inst_2805_,
        v_f_2806_,
        v_init_2807_,
        v_t_2808_,
    );
    lean_dec_ref(v_cmp_2802_);
    return v_res_2809_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(
    mut v_inst_2810_: *mut LeanObject,
    mut v_t_2811_: *mut LeanObject,
    mut v_f_2812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    v___f_2813_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2813_, 0, v_f_2812_);
    v___x_2814_ = lean_box(0);
    v___x_2815_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2810_,
        v___f_2813_,
        v___x_2814_,
        v_t_2811_,
    );
    return v___x_2815_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad___redArg(
    mut v_inst_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2817_: *mut LeanObject = core::ptr::null_mut();
    v___f_2817_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2817_, 0, v_inst_2816_);
    return v___f_2817_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad(
    mut v_00_u03b1_2818_: *mut LeanObject,
    mut v_cmp_2819_: *mut LeanObject,
    mut v_m_2820_: *mut LeanObject,
    mut v_inst_2821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2822_: *mut LeanObject = core::ptr::null_mut();
    v___f_2822_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2822_, 0, v_inst_2821_);
    return v___f_2822_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad___boxed(
    mut v_00_u03b1_2823_: *mut LeanObject,
    mut v_cmp_2824_: *mut LeanObject,
    mut v_m_2825_: *mut LeanObject,
    mut v_inst_2826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2827_: *mut LeanObject = core::ptr::null_mut();
    v_res_2827_ =
        l_Std_TreeSet_Raw_instForMOfMonad(v_00_u03b1_2823_, v_cmp_2824_, v_m_2825_, v_inst_2826_);
    lean_dec_ref(v_cmp_2824_);
    return v_res_2827_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(
    mut v_inst_2828_: *mut LeanObject,
    mut v_00_u03b2_2829_: *mut LeanObject,
    mut v_t_2830_: *mut LeanObject,
    mut v_init_2831_: *mut LeanObject,
    mut v_f_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2833_ = lean_ctor_get(v_inst_2828_, 0);
    v_toBind_2834_ = lean_ctor_get(v_inst_2828_, 1);
    lean_inc(v_toBind_2834_);
    v_toPure_2835_ = lean_ctor_get(v_toApplicative_2833_, 1);
    lean_inc(v_toPure_2835_);
    v___f_2836_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2836_, 0, v_f_2832_);
    v___x_2837_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2828_,
        v___f_2836_,
        v_init_2831_,
        v_t_2830_,
    );
    v___f_2838_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2838_, 0, v_toPure_2835_);
    v___x_2839_ = lean_apply_4(
        v_toBind_2834_,
        lean_box(0),
        lean_box(0),
        v___x_2837_,
        v___f_2838_,
    );
    return v___x_2839_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad___redArg(
    mut v_inst_2840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2841_: *mut LeanObject = core::ptr::null_mut();
    v___f_2841_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2841_, 0, v_inst_2840_);
    return v___f_2841_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad(
    mut v_00_u03b1_2842_: *mut LeanObject,
    mut v_cmp_2843_: *mut LeanObject,
    mut v_m_2844_: *mut LeanObject,
    mut v_inst_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2846_: *mut LeanObject = core::ptr::null_mut();
    v___f_2846_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2846_, 0, v_inst_2845_);
    return v___f_2846_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad___boxed(
    mut v_00_u03b1_2847_: *mut LeanObject,
    mut v_cmp_2848_: *mut LeanObject,
    mut v_m_2849_: *mut LeanObject,
    mut v_inst_2850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2851_: *mut LeanObject = core::ptr::null_mut();
    v_res_2851_ =
        l_Std_TreeSet_Raw_instForInOfMonad(v_00_u03b1_2847_, v_cmp_2848_, v_m_2849_, v_inst_2850_);
    lean_dec_ref(v_cmp_2848_);
    return v_res_2851_;
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg___lam__0(
    mut v_p_2852_: *mut LeanObject,
    mut v___x_2853_: *mut LeanObject,
    mut v___x_2854_: *mut LeanObject,
    mut v_a_2855_: *mut LeanObject,
    mut v_b_2856_: *mut LeanObject,
    mut v_acc_2857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    v___x_2858_ = lean_apply_1(v_p_2852_, v_a_2855_);
    v___x_2859_ = (lean_unbox(v___x_2858_) as u8);
    if v___x_2859_ == 0 {
        let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
        v___x_2860_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2860_, 0, v___x_2853_);
        return v___x_2860_;
    } else {
        let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2853_);
        v___x_2861_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2861_, 0, v___x_2858_);
        v___x_2862_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2862_, 0, v___x_2861_);
        lean_ctor_set(v___x_2862_, 1, v___x_2854_);
        v___x_2863_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2863_, 0, v___x_2862_);
        return v___x_2863_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(
    mut v_p_2864_: *mut LeanObject,
    mut v___x_2865_: *mut LeanObject,
    mut v___x_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
    mut v_b_2868_: *mut LeanObject,
    mut v_acc_2869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2870_: *mut LeanObject = core::ptr::null_mut();
    v_res_2870_ = l_Std_TreeSet_Raw_any___redArg___lam__0(
        v_p_2864_,
        v___x_2865_,
        v___x_2866_,
        v_a_2867_,
        v_b_2868_,
        v_acc_2869_,
    );
    lean_dec_ref(v_acc_2869_);
    return v_res_2870_;
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg(
    mut v_t_2874_: *mut LeanObject,
    mut v_p_2875_: *mut LeanObject,
) -> u8 {
    let mut v___y_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: u8 = 0;
    let mut v_val_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2882_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2883_ = lean_box(0);
                v___x_2884_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2885_ = lean_alloc_closure(
                    l_Std_TreeSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_2885_, 0, v_p_2875_);
                lean_closure_set(v___f_2885_, 1, v___x_2884_);
                lean_closure_set(v___f_2885_, 2, v___x_2883_);
                v___x_2886_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2882_,
                    v___f_2885_,
                    v___x_2884_,
                    v_t_2874_,
                );
                v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
                lean_inc(v_a_2887_);
                lean_dec(v___x_2886_);
                v___y_2877_ = v_a_2887_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2878_ = lean_ctor_get(v___y_2877_, 0);
                lean_inc(v_fst_2878_);
                lean_dec_ref(v___y_2877_);
                if lean_obj_tag(v_fst_2878_) == 0 {
                    v___x_2879_ = 0;
                    return v___x_2879_;
                } else {
                    v_val_2880_ = lean_ctor_get(v_fst_2878_, 0);
                    lean_inc(v_val_2880_);
                    lean_dec_ref_known(v_fst_2878_, 1);
                    v___x_2881_ = (lean_unbox(v_val_2880_) as u8);
                    lean_dec(v_val_2880_);
                    return v___x_2881_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg___boxed(
    mut v_t_2888_: *mut LeanObject,
    mut v_p_2889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2890_: u8 = 0;
    let mut v_r_2891_: *mut LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_Std_TreeSet_Raw_any___redArg(v_t_2888_, v_p_2889_);
    v_r_2891_ = lean_box((v_res_2890_) as usize);
    return v_r_2891_;
}
pub unsafe fn l_Std_TreeSet_Raw_any(
    mut v_00_u03b1_2892_: *mut LeanObject,
    mut v_cmp_2893_: *mut LeanObject,
    mut v_t_2894_: *mut LeanObject,
    mut v_p_2895_: *mut LeanObject,
) -> u8 {
    let mut v___y_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u8 = 0;
    let mut v_val_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2902_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2903_ = lean_box(0);
                v___x_2904_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2905_ = lean_alloc_closure(
                    l_Std_TreeSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_2905_, 0, v_p_2895_);
                lean_closure_set(v___f_2905_, 1, v___x_2904_);
                lean_closure_set(v___f_2905_, 2, v___x_2903_);
                v___x_2906_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2902_,
                    v___f_2905_,
                    v___x_2904_,
                    v_t_2894_,
                );
                v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
                lean_inc(v_a_2907_);
                lean_dec(v___x_2906_);
                v___y_2897_ = v_a_2907_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2898_ = lean_ctor_get(v___y_2897_, 0);
                lean_inc(v_fst_2898_);
                lean_dec_ref(v___y_2897_);
                if lean_obj_tag(v_fst_2898_) == 0 {
                    v___x_2899_ = 0;
                    return v___x_2899_;
                } else {
                    v_val_2900_ = lean_ctor_get(v_fst_2898_, 0);
                    lean_inc(v_val_2900_);
                    lean_dec_ref_known(v_fst_2898_, 1);
                    v___x_2901_ = (lean_unbox(v_val_2900_) as u8);
                    lean_dec(v_val_2900_);
                    return v___x_2901_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_any___boxed(
    mut v_00_u03b1_2908_: *mut LeanObject,
    mut v_cmp_2909_: *mut LeanObject,
    mut v_t_2910_: *mut LeanObject,
    mut v_p_2911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2912_: u8 = 0;
    let mut v_r_2913_: *mut LeanObject = core::ptr::null_mut();
    v_res_2912_ = l_Std_TreeSet_Raw_any(v_00_u03b1_2908_, v_cmp_2909_, v_t_2910_, v_p_2911_);
    lean_dec_ref(v_cmp_2909_);
    v_r_2913_ = lean_box((v_res_2912_) as usize);
    return v_r_2913_;
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg___lam__0(
    mut v_p_2914_: *mut LeanObject,
    mut v___x_2915_: *mut LeanObject,
    mut v___x_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_b_2918_: *mut LeanObject,
    mut v_acc_2919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    v___x_2920_ = lean_apply_1(v_p_2914_, v_a_2917_);
    v___x_2921_ = (lean_unbox(v___x_2920_) as u8);
    if v___x_2921_ == 0 {
        let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2916_);
        v___x_2922_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2922_, 0, v___x_2920_);
        v___x_2923_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2923_, 0, v___x_2922_);
        lean_ctor_set(v___x_2923_, 1, v___x_2915_);
        v___x_2924_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2924_, 0, v___x_2923_);
        return v___x_2924_;
    } else {
        let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
        v___x_2925_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2925_, 0, v___x_2916_);
        return v___x_2925_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(
    mut v_p_2926_: *mut LeanObject,
    mut v___x_2927_: *mut LeanObject,
    mut v___x_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_b_2930_: *mut LeanObject,
    mut v_acc_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2932_: *mut LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Std_TreeSet_Raw_all___redArg___lam__0(
        v_p_2926_,
        v___x_2927_,
        v___x_2928_,
        v_a_2929_,
        v_b_2930_,
        v_acc_2931_,
    );
    lean_dec_ref(v_acc_2931_);
    return v_res_2932_;
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg(
    mut v_t_2933_: *mut LeanObject,
    mut v_p_2934_: *mut LeanObject,
) -> u8 {
    let mut v___y_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v_val_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2941_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2942_ = lean_box(0);
                v___x_2943_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2944_ = lean_alloc_closure(
                    l_Std_TreeSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_2944_, 0, v_p_2934_);
                lean_closure_set(v___f_2944_, 1, v___x_2942_);
                lean_closure_set(v___f_2944_, 2, v___x_2943_);
                v___x_2945_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2941_,
                    v___f_2944_,
                    v___x_2943_,
                    v_t_2933_,
                );
                v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
                lean_inc(v_a_2946_);
                lean_dec(v___x_2945_);
                v___y_2936_ = v_a_2946_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2937_ = lean_ctor_get(v___y_2936_, 0);
                lean_inc(v_fst_2937_);
                lean_dec_ref(v___y_2936_);
                if lean_obj_tag(v_fst_2937_) == 0 {
                    v___x_2938_ = 1;
                    return v___x_2938_;
                } else {
                    v_val_2939_ = lean_ctor_get(v_fst_2937_, 0);
                    lean_inc(v_val_2939_);
                    lean_dec_ref_known(v_fst_2937_, 1);
                    v___x_2940_ = (lean_unbox(v_val_2939_) as u8);
                    lean_dec(v_val_2939_);
                    return v___x_2940_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg___boxed(
    mut v_t_2947_: *mut LeanObject,
    mut v_p_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2949_: u8 = 0;
    let mut v_r_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Std_TreeSet_Raw_all___redArg(v_t_2947_, v_p_2948_);
    v_r_2950_ = lean_box((v_res_2949_) as usize);
    return v_r_2950_;
}
pub unsafe fn l_Std_TreeSet_Raw_all(
    mut v_00_u03b1_2951_: *mut LeanObject,
    mut v_cmp_2952_: *mut LeanObject,
    mut v_t_2953_: *mut LeanObject,
    mut v_p_2954_: *mut LeanObject,
) -> u8 {
    let mut v___y_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v_val_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2961_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2962_ = lean_box(0);
                v___x_2963_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2964_ = lean_alloc_closure(
                    l_Std_TreeSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_2964_, 0, v_p_2954_);
                lean_closure_set(v___f_2964_, 1, v___x_2962_);
                lean_closure_set(v___f_2964_, 2, v___x_2963_);
                v___x_2965_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2961_,
                    v___f_2964_,
                    v___x_2963_,
                    v_t_2953_,
                );
                v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
                lean_inc(v_a_2966_);
                lean_dec(v___x_2965_);
                v___y_2956_ = v_a_2966_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2957_ = lean_ctor_get(v___y_2956_, 0);
                lean_inc(v_fst_2957_);
                lean_dec_ref(v___y_2956_);
                if lean_obj_tag(v_fst_2957_) == 0 {
                    v___x_2958_ = 1;
                    return v___x_2958_;
                } else {
                    v_val_2959_ = lean_ctor_get(v_fst_2957_, 0);
                    lean_inc(v_val_2959_);
                    lean_dec_ref_known(v_fst_2957_, 1);
                    v___x_2960_ = (lean_unbox(v_val_2959_) as u8);
                    lean_dec(v_val_2959_);
                    return v___x_2960_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_all___boxed(
    mut v_00_u03b1_2967_: *mut LeanObject,
    mut v_cmp_2968_: *mut LeanObject,
    mut v_t_2969_: *mut LeanObject,
    mut v_p_2970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2971_: u8 = 0;
    let mut v_r_2972_: *mut LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Std_TreeSet_Raw_all(v_00_u03b1_2967_, v_cmp_2968_, v_t_2969_, v_p_2970_);
    lean_dec_ref(v_cmp_2968_);
    v_r_2972_ = lean_box((v_res_2971_) as usize);
    return v_r_2972_;
}
pub unsafe fn l_Std_TreeSet_Raw_toList___redArg___lam__0(
    mut v_x1_2973_: *mut LeanObject,
    mut v_x2_2974_: *mut LeanObject,
    mut v_x3_2975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___x_2976_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2976_, 0, v_x1_2973_);
    lean_ctor_set(v___x_2976_, 1, v_x3_2975_);
    return v___x_2976_;
}
pub unsafe fn l_Std_TreeSet_Raw_toList___redArg(mut v_t_2978_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    v___f_2979_ = l_Std_TreeSet_Raw_toList___redArg___closed__0;
    v___x_2980_ = lean_box(0);
    v___x_2981_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v___x_2982_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_2981_,
        v___f_2979_,
        v___x_2980_,
        v_t_2978_,
    );
    return v___x_2982_;
}
pub unsafe fn l_Std_TreeSet_Raw_toList(
    mut v_00_u03b1_2983_: *mut LeanObject,
    mut v_cmp_2984_: *mut LeanObject,
    mut v_t_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    v___f_2986_ = l_Std_TreeSet_Raw_toList___redArg___closed__0;
    v___x_2987_ = lean_box(0);
    v___x_2988_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v___x_2989_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_2988_,
        v___f_2986_,
        v___x_2987_,
        v_t_2985_,
    );
    return v___x_2989_;
}
pub unsafe fn l_Std_TreeSet_Raw_toList___boxed(
    mut v_00_u03b1_2990_: *mut LeanObject,
    mut v_cmp_2991_: *mut LeanObject,
    mut v_t_2992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2993_: *mut LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Std_TreeSet_Raw_toList(v_00_u03b1_2990_, v_cmp_2991_, v_t_2992_);
    lean_dec_ref(v_cmp_2991_);
    return v_res_2993_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw_ofList___auto__1() -> *mut LeanObject {
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    v___x_2994_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__26,
    );
    return v___x_2994_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___redArg___lam__0(
    mut v_cmp_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
    mut v_x_2997_: *mut LeanObject,
    mut v___y_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2999_: u8 = 0;
    lean_inc(v___y_2998_);
    lean_inc(v_a_2996_);
    lean_inc_ref(v_cmp_2995_);
    v___x_2999_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2995_, v_a_2996_, v___y_2998_);
    if v___x_2999_ == 0 {
        let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
        v___x_3000_ = lean_box(0);
        v___x_3001_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2995_,
            v_a_2996_,
            v___x_3000_,
            v___y_2998_,
        );
        v___x_3002_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3002_, 0, v___x_3001_);
        return v___x_3002_;
    } else {
        let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_2996_);
        lean_dec_ref(v_cmp_2995_);
        v___x_3003_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3003_, 0, v___y_2998_);
        return v___x_3003_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___redArg(
    mut v_l_3004_: *mut LeanObject,
    mut v_cmp_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    v___f_3006_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3006_, 0, v_cmp_3005_);
    v___x_3007_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3008_ = lean_box(1);
    v___x_3009_ = l_List_forIn_x27_loop___redArg(v___x_3007_, v___f_3006_, v_l_3004_, v_r_3008_);
    return v___x_3009_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___redArg___boxed(
    mut v_l_3010_: *mut LeanObject,
    mut v_cmp_3011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3012_: *mut LeanObject = core::ptr::null_mut();
    v_res_3012_ = l_Std_TreeSet_Raw_ofList___redArg(v_l_3010_, v_cmp_3011_);
    lean_dec(v_l_3010_);
    return v_res_3012_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList(
    mut v_00_u03b1_3013_: *mut LeanObject,
    mut v_l_3014_: *mut LeanObject,
    mut v_cmp_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    v___f_3016_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3016_, 0, v_cmp_3015_);
    v___x_3017_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3018_ = lean_box(1);
    v___x_3019_ = l_List_forIn_x27_loop___redArg(v___x_3017_, v___f_3016_, v_l_3014_, v_r_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___boxed(
    mut v_00_u03b1_3020_: *mut LeanObject,
    mut v_l_3021_: *mut LeanObject,
    mut v_cmp_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3023_: *mut LeanObject = core::ptr::null_mut();
    v_res_3023_ = l_Std_TreeSet_Raw_ofList(v_00_u03b1_3020_, v_l_3021_, v_cmp_3022_);
    lean_dec(v_l_3021_);
    return v_res_3023_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray___redArg___lam__0(
    mut v_c_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_x_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    v___x_3027_ = lean_array_push(v_c_3024_, v_a_3025_);
    return v___x_3027_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray___redArg(
    mut v_t_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    v___f_3032_ = l_Std_TreeSet_Raw_toArray___redArg___closed__0;
    v___x_3033_ = l_Std_TreeSet_Raw_toArray___redArg___closed__1;
    v___x_3034_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3032_, v___x_3033_, v_t_3031_);
    return v___x_3034_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray(
    mut v_00_u03b1_3035_: *mut LeanObject,
    mut v_cmp_3036_: *mut LeanObject,
    mut v_t_3037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    v___f_3038_ = l_Std_TreeSet_Raw_toArray___redArg___closed__0;
    v___x_3039_ = l_Std_TreeSet_Raw_toArray___redArg___closed__1;
    v___x_3040_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3038_, v___x_3039_, v_t_3037_);
    return v___x_3040_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray___boxed(
    mut v_00_u03b1_3041_: *mut LeanObject,
    mut v_cmp_3042_: *mut LeanObject,
    mut v_t_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3044_: *mut LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Std_TreeSet_Raw_toArray(v_00_u03b1_3041_, v_cmp_3042_, v_t_3043_);
    lean_dec_ref(v_cmp_3042_);
    return v_res_3044_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw_ofArray___auto__1() -> *mut LeanObject {
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    v___x_3045_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__26,
    );
    return v___x_3045_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofArray___redArg(
    mut v_a_3046_: *mut LeanObject,
    mut v_cmp_3047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3051_: usize = 0;
    let mut v___x_3052_: usize = 0;
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    v___f_3048_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3048_, 0, v_cmp_3047_);
    v___x_3049_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3050_ = lean_box(1);
    v_sz_3051_ = lean_array_size(v_a_3046_);
    v___x_3052_ = 0usize;
    v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_3049_,
        v_a_3046_,
        v___f_3048_,
        v_sz_3051_,
        v___x_3052_,
        v_r_3050_,
    );
    return v___x_3053_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofArray(
    mut v_00_u03b1_3054_: *mut LeanObject,
    mut v_a_3055_: *mut LeanObject,
    mut v_cmp_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3060_: usize = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    v___f_3057_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3057_, 0, v_cmp_3056_);
    v___x_3058_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3059_ = lean_box(1);
    v_sz_3060_ = lean_array_size(v_a_3055_);
    v___x_3061_ = 0usize;
    v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_3058_,
        v_a_3055_,
        v___f_3057_,
        v_sz_3060_,
        v___x_3061_,
        v_r_3059_,
    );
    return v___x_3062_;
}
pub unsafe fn l_Std_TreeSet_Raw_merge___redArg___lam__0(
    mut v_b_u2082_3065_: *mut LeanObject,
    mut v_x_3066_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3066_) == 0 {
        let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
        v___x_3067_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3067_, 0, v_b_u2082_3065_);
        return v___x_3067_;
    } else {
        let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
        v___x_3068_ = l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0;
        return v___x_3068_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(
    mut v_b_u2082_3069_: *mut LeanObject,
    mut v_x_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3071_: *mut LeanObject = core::ptr::null_mut();
    v_res_3071_ = l_Std_TreeSet_Raw_merge___redArg___lam__0(v_b_u2082_3069_, v_x_3070_);
    lean_dec(v_x_3070_);
    return v_res_3071_;
}
pub unsafe fn l_Std_TreeSet_Raw_merge___redArg___lam__1(
    mut v_cmp_3072_: *mut LeanObject,
    mut v_t_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
    mut v_b_u2082_3075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    v___f_3076_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3076_, 0, v_b_u2082_3075_);
    v___x_3077_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(
        v_cmp_3072_,
        v_a_3074_,
        v___f_3076_,
        v_t_3073_,
    );
    return v___x_3077_;
}
pub unsafe fn l_Std_TreeSet_Raw_merge___redArg(
    mut v_cmp_3078_: *mut LeanObject,
    mut v_t_u2081_3079_: *mut LeanObject,
    mut v_t_u2082_3080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    v___f_3081_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3081_, 0, v_cmp_3078_);
    v___x_3082_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3081_, v_t_u2081_3079_, v_t_u2082_3080_);
    return v___x_3082_;
}
pub unsafe fn l_Std_TreeSet_Raw_merge(
    mut v_00_u03b1_3083_: *mut LeanObject,
    mut v_cmp_3084_: *mut LeanObject,
    mut v_t_u2081_3085_: *mut LeanObject,
    mut v_t_u2082_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    v___f_3087_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3087_, 0, v_cmp_3084_);
    v___x_3088_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3087_, v_t_u2081_3085_, v_t_u2082_3086_);
    return v___x_3088_;
}
pub unsafe fn l_Std_TreeSet_Raw_insertMany___redArg___lam__0(
    mut v_cmp_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_____s_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3092_: u8 = 0;
    lean_inc(v_____s_3091_);
    lean_inc(v_a_3090_);
    lean_inc_ref(v_cmp_3089_);
    v___x_3092_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3089_, v_a_3090_, v_____s_3091_);
    if v___x_3092_ == 0 {
        let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
        v___x_3093_ = lean_box(0);
        v___x_3094_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_3089_,
            v_a_3090_,
            v___x_3093_,
            v_____s_3091_,
        );
        v___x_3095_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3095_, 0, v___x_3094_);
        return v___x_3095_;
    } else {
        let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_3090_);
        lean_dec_ref(v_cmp_3089_);
        v___x_3096_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3096_, 0, v_____s_3091_);
        return v___x_3096_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_insertMany___redArg(
    mut v_cmp_3097_: *mut LeanObject,
    mut v_inst_3098_: *mut LeanObject,
    mut v_t_3099_: *mut LeanObject,
    mut v_l_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    v___f_3101_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3101_, 0, v_cmp_3097_);
    v___x_3102_ = lean_apply_4(v_inst_3098_, lean_box(0), v_l_3100_, v_t_3099_, v___f_3101_);
    return v___x_3102_;
}
pub unsafe fn l_Std_TreeSet_Raw_insertMany(
    mut v_00_u03b1_3103_: *mut LeanObject,
    mut v_cmp_3104_: *mut LeanObject,
    mut v_00_u03c1_3105_: *mut LeanObject,
    mut v_inst_3106_: *mut LeanObject,
    mut v_t_3107_: *mut LeanObject,
    mut v_l_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    v___f_3109_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3109_, 0, v_cmp_3104_);
    v___x_3110_ = lean_apply_4(v_inst_3106_, lean_box(0), v_l_3108_, v_t_3107_, v___f_3109_);
    return v___x_3110_;
}
pub unsafe fn l_Std_TreeSet_Raw_union___redArg(
    mut v_cmp_3111_: *mut LeanObject,
    mut v_t_u2081_3112_: *mut LeanObject,
    mut v_t_u2082_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    v___x_3114_ =
        l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(
            v_cmp_3111_,
            v_t_u2081_3112_,
            v_t_u2082_3113_,
        );
    return v___x_3114_;
}
pub unsafe fn l_Std_TreeSet_Raw_union(
    mut v_00_u03b1_3115_: *mut LeanObject,
    mut v_cmp_3116_: *mut LeanObject,
    mut v_t_u2081_3117_: *mut LeanObject,
    mut v_t_u2082_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    v___x_3119_ =
        l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(
            v_cmp_3116_,
            v_t_u2081_3117_,
            v_t_u2082_3118_,
        );
    return v___x_3119_;
}
pub unsafe fn l_Std_TreeSet_Raw_instUnion___redArg(
    mut v_cmp_3120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    v___x_3121_ = lean_alloc_closure(l_Std_TreeSet_Raw_union as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3121_, 0, lean_box(0));
    lean_closure_set(v___x_3121_, 1, v_cmp_3120_);
    return v___x_3121_;
}
pub unsafe fn l_Std_TreeSet_Raw_instUnion(
    mut v_00_u03b1_3122_: *mut LeanObject,
    mut v_cmp_3123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    v___x_3124_ = lean_alloc_closure(l_Std_TreeSet_Raw_union as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3124_, 0, lean_box(0));
    lean_closure_set(v___x_3124_, 1, v_cmp_3123_);
    return v___x_3124_;
}
pub unsafe fn l_Std_TreeSet_Raw_inter___redArg(
    mut v_cmp_3125_: *mut LeanObject,
    mut v_t_u2081_3126_: *mut LeanObject,
    mut v_t_u2082_3127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    v___x_3128_ =
        l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(
            v_cmp_3125_,
            v_t_u2081_3126_,
            v_t_u2082_3127_,
        );
    return v___x_3128_;
}
pub unsafe fn l_Std_TreeSet_Raw_inter(
    mut v_00_u03b1_3129_: *mut LeanObject,
    mut v_cmp_3130_: *mut LeanObject,
    mut v_t_u2081_3131_: *mut LeanObject,
    mut v_t_u2082_3132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    v___x_3133_ =
        l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(
            v_cmp_3130_,
            v_t_u2081_3131_,
            v_t_u2082_3132_,
        );
    return v___x_3133_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInter___redArg(
    mut v_cmp_3134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    v___x_3135_ = lean_alloc_closure(l_Std_TreeSet_Raw_inter as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3135_, 0, lean_box(0));
    lean_closure_set(v___x_3135_, 1, v_cmp_3134_);
    return v___x_3135_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInter(
    mut v_00_u03b1_3136_: *mut LeanObject,
    mut v_cmp_3137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    v___x_3138_ = lean_alloc_closure(l_Std_TreeSet_Raw_inter as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3138_, 0, lean_box(0));
    lean_closure_set(v___x_3138_, 1, v_cmp_3137_);
    return v___x_3138_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(
    mut v_x_3139_: *mut LeanObject,
    mut v_x_3140_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3139_) == 0 {
        if lean_obj_tag(v_x_3140_) == 0 {
            let mut v___x_3141_: u8 = 0;
            v___x_3141_ = 1;
            return v___x_3141_;
        } else {
            let mut v___x_3142_: u8 = 0;
            v___x_3142_ = 0;
            return v___x_3142_;
        }
    } else {
        if lean_obj_tag(v_x_3140_) == 0 {
            let mut v___x_3143_: u8 = 0;
            v___x_3143_ = 0;
            return v___x_3143_;
        } else {
            let mut v___x_3144_: u8 = 0;
            v___x_3144_ = 1;
            return v___x_3144_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_x_3145_: *mut LeanObject,
    mut v_x_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3147_: u8 = 0;
    let mut v_r_3148_: *mut LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_3145_, v_x_3146_);
    lean_dec(v_x_3146_);
    lean_dec(v_x_3145_);
    v_r_3148_ = lean_box((v_res_3147_) as usize);
    return v_r_3148_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_cmp_3149_: *mut LeanObject,
    mut v_t_3150_: *mut LeanObject,
    mut v_k_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: u8 = 0;
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3150_) == 0 {
                    v_k_3152_ = lean_ctor_get(v_t_3150_, 1);
                    lean_inc(v_k_3152_);
                    v_v_3153_ = lean_ctor_get(v_t_3150_, 2);
                    lean_inc(v_v_3153_);
                    v_l_3154_ = lean_ctor_get(v_t_3150_, 3);
                    lean_inc(v_l_3154_);
                    v_r_3155_ = lean_ctor_get(v_t_3150_, 4);
                    lean_inc(v_r_3155_);
                    lean_dec_ref_known(v_t_3150_, 5);
                    lean_inc_ref(v_cmp_3149_);
                    lean_inc(v_k_3151_);
                    v___x_3156_ = lean_apply_2(v_cmp_3149_, v_k_3151_, v_k_3152_);
                    v___x_3157_ = (lean_unbox(v___x_3156_) as u8);
                    match v___x_3157_ {
                        0 => {
                            lean_dec(v_r_3155_);
                            lean_dec(v_v_3153_);
                            v_t_3150_ = v_l_3154_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_3155_);
                            lean_dec(v_l_3154_);
                            lean_dec(v_k_3151_);
                            lean_dec_ref(v_cmp_3149_);
                            v___x_3159_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3159_, 0, v_v_3153_);
                            return v___x_3159_;
                        }
                        _ => {
                            lean_dec(v_l_3154_);
                            lean_dec(v_v_3153_);
                            v_t_3150_ = v_r_3155_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_3151_);
                    lean_dec_ref(v_cmp_3149_);
                    v___x_3161_ = lean_box(0);
                    return v___x_3161_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_cmp_3162_: *mut LeanObject,
    mut v_t_u2082_3163_: *mut LeanObject,
    mut v_init_3164_: *mut LeanObject,
    mut v_x_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_unused_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3165_) == 0 {
                    v_k_3166_ = lean_ctor_get(v_x_3165_, 1);
                    lean_inc(v_k_3166_);
                    v_v_3167_ = lean_ctor_get(v_x_3165_, 2);
                    lean_inc(v_v_3167_);
                    v_l_3168_ = lean_ctor_get(v_x_3165_, 3);
                    lean_inc(v_l_3168_);
                    v_r_3169_ = lean_ctor_get(v_x_3165_, 4);
                    lean_inc(v_r_3169_);
                    lean_dec_ref_known(v_x_3165_, 5);
                    lean_inc(v_t_u2082_3163_);
                    lean_inc_ref(v_cmp_3162_);
                    v___x_3170_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_3162_, v_t_u2082_3163_, v_init_3164_, v_l_3168_);
                    if lean_obj_tag(v___x_3170_) == 0 {
                        lean_dec(v_r_3169_);
                        lean_dec(v_v_3167_);
                        lean_dec(v_k_3166_);
                        lean_dec(v_t_u2082_3163_);
                        lean_dec_ref(v_cmp_3162_);
                        return v___x_3170_;
                    } else {
                        v_isSharedCheck_3186_ = (!lean_is_exclusive(v___x_3170_)) as u8;
                        if v_isSharedCheck_3186_ == 0 {
                            v_unused_3187_ = lean_ctor_get(v___x_3170_, 0);
                            lean_dec(v_unused_3187_);
                            v___x_3172_ = v___x_3170_;
                            v_isShared_3173_ = v_isSharedCheck_3186_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3170_);
                            v___x_3172_ = lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3186_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_t_u2082_3163_);
                    lean_dec_ref(v_cmp_3162_);
                    v___x_3188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3188_, 0, v_init_3164_);
                    return v___x_3188_;
                }
            }
            1 => {
                v___x_3174_ = lean_box(0);
                lean_inc(v_t_u2082_3163_);
                lean_inc_ref(v_cmp_3162_);
                v___x_3175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_3162_, v_t_u2082_3163_, v_k_3166_);
                v___x_3176_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3176_, 0, v_v_3167_);
                v___x_3177_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v___x_3175_, v___x_3176_);
                lean_dec_ref_known(v___x_3176_, 1);
                lean_dec(v___x_3175_);
                if v___x_3177_ == 0 {
                    lean_dec(v_r_3169_);
                    lean_dec(v_t_u2082_3163_);
                    lean_dec_ref(v_cmp_3162_);
                    v___x_3178_ = lean_box((v___x_3177_) as usize);
                    v___x_3179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3179_, 0, v___x_3178_);
                    v___x_3180_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3180_, 0, v___x_3179_);
                    lean_ctor_set(v___x_3180_, 1, v___x_3174_);
                    if v_isShared_3173_ == 0 {
                        lean_ctor_set_tag(v___x_3172_, 0);
                        lean_ctor_set(v___x_3172_, 0, v___x_3180_);
                        v___x_3182_ = v___x_3172_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
                        v___x_3182_ = v_reuseFailAlloc_3183_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3172_);
                    v___x_3184_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                    v_init_3164_ = v___x_3184_;
                    v_x_3165_ = v_r_3169_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_3182_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(
    mut v_cmp_3189_: *mut LeanObject,
    mut v_t_u2081_3190_: *mut LeanObject,
    mut v_t_u2082_3191_: *mut LeanObject,
) -> u8 {
    let mut v___y_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: u8 = 0;
    let mut v_val_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___y_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_u2081_3190_) == 0 {
                    v_size_3209_ = lean_ctor_get(v_t_u2081_3190_, 0);
                    lean_inc(v_size_3209_);
                    v___y_3206_ = v_size_3209_;
                    state = 3;
                    continue;
                } else {
                    v___x_3210_ = lean_unsigned_to_nat(0);
                    v___y_3206_ = v___x_3210_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_fst_3194_ = lean_ctor_get(v___y_3193_, 0);
                lean_inc(v_fst_3194_);
                lean_dec_ref(v___y_3193_);
                if lean_obj_tag(v_fst_3194_) == 0 {
                    v___x_3195_ = 1;
                    return v___x_3195_;
                } else {
                    v_val_3196_ = lean_ctor_get(v_fst_3194_, 0);
                    lean_inc(v_val_3196_);
                    lean_dec_ref_known(v_fst_3194_, 1);
                    v___x_3197_ = (lean_unbox(v_val_3196_) as u8);
                    lean_dec(v_val_3196_);
                    return v___x_3197_;
                }
            }
            2 => {
                v___x_3201_ = lean_nat_dec_eq(v___y_3199_, v___y_3200_);
                lean_dec(v___y_3200_);
                lean_dec(v___y_3199_);
                if v___x_3201_ == 0 {
                    lean_dec(v_t_u2082_3191_);
                    lean_dec(v_t_u2081_3190_);
                    lean_dec_ref(v_cmp_3189_);
                    return v___x_3201_;
                } else {
                    v___x_3202_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                    v___x_3203_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_3189_, v_t_u2082_3191_, v___x_3202_, v_t_u2081_3190_);
                    v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
                    lean_inc(v_a_3204_);
                    lean_dec_ref(v___x_3203_);
                    v___y_3193_ = v_a_3204_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_t_u2082_3191_) == 0 {
                    v_size_3207_ = lean_ctor_get(v_t_u2082_3191_, 0);
                    lean_inc(v_size_3207_);
                    v___y_3199_ = v___y_3206_;
                    v___y_3200_ = v_size_3207_;
                    state = 2;
                    continue;
                } else {
                    v___x_3208_ = lean_unsigned_to_nat(0);
                    v___y_3199_ = v___y_3206_;
                    v___y_3200_ = v___x_3208_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_cmp_3211_: *mut LeanObject,
    mut v_t_u2081_3212_: *mut LeanObject,
    mut v_t_u2082_3213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3214_: u8 = 0;
    let mut v_r_3215_: *mut LeanObject = core::ptr::null_mut();
    v_res_3214_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3211_, v_t_u2081_3212_, v_t_u2082_3213_);
    v_r_3215_ = lean_box((v_res_3214_) as usize);
    return v_r_3215_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq___redArg(
    mut v_cmp_3216_: *mut LeanObject,
    mut v_t_u2081_3217_: *mut LeanObject,
    mut v_t_u2082_3218_: *mut LeanObject,
) -> u8 {
    let mut v___x_3219_: u8 = 0;
    v___x_3219_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3216_, v_t_u2081_3217_, v_t_u2082_3218_);
    return v___x_3219_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq___redArg___boxed(
    mut v_cmp_3220_: *mut LeanObject,
    mut v_t_u2081_3221_: *mut LeanObject,
    mut v_t_u2082_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3223_: u8 = 0;
    let mut v_r_3224_: *mut LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_3220_, v_t_u2081_3221_, v_t_u2082_3222_);
    v_r_3224_ = lean_box((v_res_3223_) as usize);
    return v_r_3224_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq(
    mut v_00_u03b1_3225_: *mut LeanObject,
    mut v_cmp_3226_: *mut LeanObject,
    mut v_t_u2081_3227_: *mut LeanObject,
    mut v_t_u2082_3228_: *mut LeanObject,
) -> u8 {
    let mut v___x_3229_: u8 = 0;
    v___x_3229_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3226_, v_t_u2081_3227_, v_t_u2082_3228_);
    return v___x_3229_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq___boxed(
    mut v_00_u03b1_3230_: *mut LeanObject,
    mut v_cmp_3231_: *mut LeanObject,
    mut v_t_u2081_3232_: *mut LeanObject,
    mut v_t_u2082_3233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3234_: u8 = 0;
    let mut v_r_3235_: *mut LeanObject = core::ptr::null_mut();
    v_res_3234_ = l_Std_TreeSet_Raw_beq(
        v_00_u03b1_3230_,
        v_cmp_3231_,
        v_t_u2081_3232_,
        v_t_u2082_3233_,
    );
    v_r_3235_ = lean_box((v_res_3234_) as usize);
    return v_r_3235_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(
    mut v_cmp_3236_: *mut LeanObject,
    mut v_t_u2081_3237_: *mut LeanObject,
    mut v_t_u2082_3238_: *mut LeanObject,
) -> u8 {
    let mut v___x_3239_: u8 = 0;
    v___x_3239_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3236_, v_t_u2081_3237_, v_t_u2082_3238_);
    return v___x_3239_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(
    mut v_cmp_3240_: *mut LeanObject,
    mut v_t_u2081_3241_: *mut LeanObject,
    mut v_t_u2082_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3243_: u8 = 0;
    let mut v_r_3244_: *mut LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(
        v_cmp_3240_,
        v_t_u2081_3241_,
        v_t_u2082_3242_,
    );
    v_r_3244_ = lean_box((v_res_3243_) as usize);
    return v_r_3244_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(
    mut v_00_u03b1_3245_: *mut LeanObject,
    mut v_cmp_3246_: *mut LeanObject,
    mut v_t_u2081_3247_: *mut LeanObject,
    mut v_t_u2082_3248_: *mut LeanObject,
) -> u8 {
    let mut v___x_3249_: u8 = 0;
    v___x_3249_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3246_, v_t_u2081_3247_, v_t_u2082_3248_);
    return v___x_3249_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(
    mut v_00_u03b1_3250_: *mut LeanObject,
    mut v_cmp_3251_: *mut LeanObject,
    mut v_t_u2081_3252_: *mut LeanObject,
    mut v_t_u2082_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3254_: u8 = 0;
    let mut v_r_3255_: *mut LeanObject = core::ptr::null_mut();
    v_res_3254_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(
        v_00_u03b1_3250_,
        v_cmp_3251_,
        v_t_u2081_3252_,
        v_t_u2082_3253_,
    );
    v_r_3255_ = lean_box((v_res_3254_) as usize);
    return v_r_3255_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(
    mut v_cmp_3256_: *mut LeanObject,
    mut v_t_u2081_3257_: *mut LeanObject,
    mut v_t_u2082_3258_: *mut LeanObject,
) -> u8 {
    let mut v___x_3259_: u8 = 0;
    v___x_3259_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3256_, v_t_u2081_3257_, v_t_u2082_3258_);
    return v___x_3259_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(
    mut v_cmp_3260_: *mut LeanObject,
    mut v_t_u2081_3261_: *mut LeanObject,
    mut v_t_u2082_3262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3263_: u8 = 0;
    let mut v_r_3264_: *mut LeanObject = core::ptr::null_mut();
    v_res_3263_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_3260_, v_t_u2081_3261_, v_t_u2082_3262_);
    v_r_3264_ = lean_box((v_res_3263_) as usize);
    return v_r_3264_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(
    mut v_00_u03b1_3265_: *mut LeanObject,
    mut v_cmp_3266_: *mut LeanObject,
    mut v_t_u2081_3267_: *mut LeanObject,
    mut v_t_u2082_3268_: *mut LeanObject,
) -> u8 {
    let mut v___x_3269_: u8 = 0;
    v___x_3269_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3266_, v_t_u2081_3267_, v_t_u2082_3268_);
    return v___x_3269_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(
    mut v_00_u03b1_3270_: *mut LeanObject,
    mut v_cmp_3271_: *mut LeanObject,
    mut v_t_u2081_3272_: *mut LeanObject,
    mut v_t_u2082_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3274_: u8 = 0;
    let mut v_r_3275_: *mut LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(v_00_u03b1_3270_, v_cmp_3271_, v_t_u2081_3272_, v_t_u2082_3273_);
    v_r_3275_ = lean_box((v_res_3274_) as usize);
    return v_r_3275_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3276_: *mut LeanObject,
    mut v_cmp_3277_: *mut LeanObject,
    mut v_t_u2081_3278_: *mut LeanObject,
    mut v_t_u2082_3279_: *mut LeanObject,
) -> u8 {
    let mut v___x_3280_: u8 = 0;
    v___x_3280_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3277_, v_t_u2081_3278_, v_t_u2082_3279_);
    return v___x_3280_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3281_: *mut LeanObject,
    mut v_cmp_3282_: *mut LeanObject,
    mut v_t_u2081_3283_: *mut LeanObject,
    mut v_t_u2082_3284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3285_: u8 = 0;
    let mut v_r_3286_: *mut LeanObject = core::ptr::null_mut();
    v_res_3285_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(v_00_u03b1_3281_, v_cmp_3282_, v_t_u2081_3283_, v_t_u2082_3284_);
    v_r_3286_ = lean_box((v_res_3285_) as usize);
    return v_r_3286_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3287_: *mut LeanObject,
    mut v_cmp_3288_: *mut LeanObject,
    mut v_00_u03b4_3289_: *mut LeanObject,
    mut v_t_3290_: *mut LeanObject,
    mut v_k_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    v___x_3292_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_3288_, v_t_3290_, v_k_3291_);
    return v___x_3292_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_3293_: *mut LeanObject,
    mut v_cmp_3294_: *mut LeanObject,
    mut v_t_u2082_3295_: *mut LeanObject,
    mut v_init_3296_: *mut LeanObject,
    mut v_x_3297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    v___x_3298_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_3294_, v_t_u2082_3295_, v_init_3296_, v_x_3297_);
    return v___x_3298_;
}
pub unsafe fn l_Std_TreeSet_Raw_instBEq___redArg(
    mut v_cmp_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    v___x_3300_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_3300_, 0, lean_box(0));
    lean_closure_set(v___x_3300_, 1, v_cmp_3299_);
    return v___x_3300_;
}
pub unsafe fn l_Std_TreeSet_Raw_instBEq(
    mut v_00_u03b1_3301_: *mut LeanObject,
    mut v_cmp_3302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    v___x_3303_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_3303_, 0, lean_box(0));
    lean_closure_set(v___x_3303_, 1, v_cmp_3302_);
    return v___x_3303_;
}
pub unsafe fn l_Std_TreeSet_Raw_diff___redArg(
    mut v_cmp_3304_: *mut LeanObject,
    mut v_t_u2081_3305_: *mut LeanObject,
    mut v_t_u2082_3306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    v___x_3307_ =
        l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(
            v_cmp_3304_,
            v_t_u2081_3305_,
            v_t_u2082_3306_,
        );
    return v___x_3307_;
}
pub unsafe fn l_Std_TreeSet_Raw_diff(
    mut v_00_u03b1_3308_: *mut LeanObject,
    mut v_cmp_3309_: *mut LeanObject,
    mut v_t_u2081_3310_: *mut LeanObject,
    mut v_t_u2082_3311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    v___x_3312_ =
        l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(
            v_cmp_3309_,
            v_t_u2081_3310_,
            v_t_u2082_3311_,
        );
    return v___x_3312_;
}
pub unsafe fn l_Std_TreeSet_Raw_instSDiff___redArg(
    mut v_cmp_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ = lean_alloc_closure(l_Std_TreeSet_Raw_diff as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3314_, 0, lean_box(0));
    lean_closure_set(v___x_3314_, 1, v_cmp_3313_);
    return v___x_3314_;
}
pub unsafe fn l_Std_TreeSet_Raw_instSDiff(
    mut v_00_u03b1_3315_: *mut LeanObject,
    mut v_cmp_3316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    v___x_3317_ = lean_alloc_closure(l_Std_TreeSet_Raw_diff as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3317_, 0, lean_box(0));
    lean_closure_set(v___x_3317_, 1, v_cmp_3316_);
    return v___x_3317_;
}
pub unsafe fn l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(
    mut v_cmp_3318_: *mut LeanObject,
    mut v_a_3319_: *mut LeanObject,
    mut v_____s_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    v_r_3321_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_3318_, v_a_3319_, v_____s_3320_);
    v___x_3322_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3322_, 0, v_r_3321_);
    return v___x_3322_;
}
pub unsafe fn l_Std_TreeSet_Raw_eraseMany___redArg(
    mut v_cmp_3323_: *mut LeanObject,
    mut v_inst_3324_: *mut LeanObject,
    mut v_t_3325_: *mut LeanObject,
    mut v_l_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    v___f_3327_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3327_, 0, v_cmp_3323_);
    v___x_3328_ = lean_apply_4(v_inst_3324_, lean_box(0), v_l_3326_, v_t_3325_, v___f_3327_);
    return v___x_3328_;
}
pub unsafe fn l_Std_TreeSet_Raw_eraseMany(
    mut v_00_u03b1_3329_: *mut LeanObject,
    mut v_cmp_3330_: *mut LeanObject,
    mut v_00_u03c1_3331_: *mut LeanObject,
    mut v_inst_3332_: *mut LeanObject,
    mut v_t_3333_: *mut LeanObject,
    mut v_l_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    v___f_3335_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3335_, 0, v_cmp_3330_);
    v___x_3336_ = lean_apply_4(v_inst_3332_, lean_box(0), v_l_3334_, v_t_3333_, v___f_3335_);
    return v___x_3336_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___redArg___lam__1(
    mut v___f_3340_: *mut LeanObject,
    mut v_inst_3341_: *mut LeanObject,
    mut v_m_3342_: *mut LeanObject,
    mut v_prec_3343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    v___x_3344_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1;
    v___x_3345_ = lean_box(0);
    v___x_3346_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v___x_3347_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3346_,
        v___f_3340_,
        v___x_3345_,
        v_m_3342_,
    );
    v___x_3348_ = l_List_repr___redArg(v_inst_3341_, v___x_3347_);
    v___x_3349_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3349_, 0, v___x_3344_);
    lean_ctor_set(v___x_3349_, 1, v___x_3348_);
    v___x_3350_ = l_Repr_addAppParen(v___x_3349_, v_prec_3343_);
    return v___x_3350_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(
    mut v___f_3351_: *mut LeanObject,
    mut v_inst_3352_: *mut LeanObject,
    mut v_m_3353_: *mut LeanObject,
    mut v_prec_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3355_: *mut LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1(
        v___f_3351_,
        v_inst_3352_,
        v_m_3353_,
        v_prec_3354_,
    );
    lean_dec(v_prec_3354_);
    return v_res_3355_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___redArg(
    mut v_inst_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3358_: *mut LeanObject = core::ptr::null_mut();
    v___f_3357_ = l_Std_TreeSet_Raw_toList___redArg___closed__0;
    v___f_3358_ = lean_alloc_closure(
        l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3358_, 0, v___f_3357_);
    lean_closure_set(v___f_3358_, 1, v_inst_3356_);
    return v___f_3358_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr(
    mut v_00_u03b1_3359_: *mut LeanObject,
    mut v_cmp_3360_: *mut LeanObject,
    mut v_inst_3361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    v___x_3362_ = l_Std_TreeSet_Raw_instRepr___redArg(v_inst_3361_);
    return v___x_3362_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___boxed(
    mut v_00_u03b1_3363_: *mut LeanObject,
    mut v_cmp_3364_: *mut LeanObject,
    mut v_inst_3365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3366_: *mut LeanObject = core::ptr::null_mut();
    v_res_3366_ = l_Std_TreeSet_Raw_instRepr(v_00_u03b1_3363_, v_cmp_3364_, v_inst_3365_);
    lean_dec_ref(v_cmp_3364_);
    return v_res_3366_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Raw_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeSet_Raw___auto__1 = _init_l_Std_TreeSet_Raw___auto__1();
    lean_mark_persistent(l_Std_TreeSet_Raw___auto__1);
    l_Std_TreeSet_Raw_ofList___auto__1 = _init_l_Std_TreeSet_Raw_ofList___auto__1();
    lean_mark_persistent(l_Std_TreeSet_Raw_ofList___auto__1);
    l_Std_TreeSet_Raw_ofArray___auto__1 = _init_l_Std_TreeSet_Raw_ofArray___auto__1();
    lean_mark_persistent(l_Std_TreeSet_Raw_ofArray___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Raw_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Raw_Basic(builtin);
}
