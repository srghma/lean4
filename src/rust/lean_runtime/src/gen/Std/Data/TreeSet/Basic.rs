// Lean compiler output
// Module: Std.Data.TreeSet.Basic
// Imports: Std.Data.TreeMap.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_mkAtom, l_Lean_replaceRef,
    l_String_toRawSubstring_x27, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_alter___redArg, l_Std_DTreeMap_Internal_Impl_erase___redArg,
    l_Std_DTreeMap_Internal_Impl_filter___redArg, l_Std_DTreeMap_Internal_Impl_insert___redArg,
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
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_mul, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Std_TreeSet___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__3_value) as *mut LeanObject;
static l_Std_TreeSet___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeSet___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeSet___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeSet___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_TreeSet___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__6_value) as *mut LeanObject;
static l_Std_TreeSet___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeSet___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeSet___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeSet___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__10_value) as *mut LeanObject;
static l_Std_TreeSet___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_TreeSet___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_TreeSet___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_TreeSet___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__10_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Std_TreeSet___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet___auto__1___closed__14_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Std_TreeSet___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__14_value) as *mut LeanObject;
static mut l_Std_TreeSet___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet___auto__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__14_value) as *mut LeanObject,
        16710690322389477741 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__17_value) as *mut LeanObject;
static mut l_Std_TreeSet___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_term___x7em___00__closed__0_value: LeanStringObject<4> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__1_value: LeanStringObject<8> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__2_value: LeanStringObject<9> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__2_value) as *mut LeanObject;
static l_Std_TreeSet_term___x7em___00__closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__0_value) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Std_TreeSet_term___x7em___00__closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__1_value) as *mut LeanObject,
        206985604220839926 as *mut LeanObject,
    ],
};
pub static l_Std_TreeSet_term___x7em___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__2_value) as *mut LeanObject,
        18267916200040923880 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_term___x7em___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__4_value: LeanStringObject<8> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__4_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__4_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_term___x7em___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__5_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__6_value: LeanStringObject<5> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__6_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_term___x7em___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__8_value: LeanStringObject<5> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__8_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_term___x7em___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__9_value) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_term___x7em___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__10_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_term___x7em___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__11_value) as *mut LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__12_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_term___x7em___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__12_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_term___x7em__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__12_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value) as *mut LeanObject;
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value) as *mut LeanObject;
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value) as *mut LeanObject,6049842283740396800 as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5_value) as *mut LeanObject;
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__1_value) as *mut LeanObject,206985604220839926 as *mut LeanObject] };
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value) as *mut LeanObject,15083926597284366801 as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value) as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value) as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_getGE_x21___redArg___closed__0_value: LeanStringObject<26> =
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
static mut l_Std_TreeSet_getGE_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_getGE_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_getGE_x21___redArg___closed__1_value: LeanStringObject<12> =
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
static mut l_Std_TreeSet_getGE_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_getGE_x21___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_getGE_x21___redArg___closed__2_value: LeanStringObject<14> =
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
static mut l_Std_TreeSet_getGE_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_getGE_x21___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_TreeSet_getGE_x21___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_getGE_x21___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_foldr___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_foldr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_foldr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_TreeSet_foldr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_TreeSet_partition___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Std_TreeSet_partition___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_partition___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_any___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Std_TreeSet_any___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_any___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_toList___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_toList___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_ofList___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_toArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_ofArray___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_merge___redArg___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Std_TreeSet_merge___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_merge___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value: LeanStringObject<20> =
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
            83, 116, 100, 46, 84, 114, 101, 101, 83, 101, 116, 46, 111, 102, 76, 105, 115, 116, 32,
            0,
        ],
    };
static mut l_Std_TreeSet_instRepr___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instRepr___redArg___lam__1___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_instRepr___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instRepr___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    v___x_2134_ = l_Std_TreeSet___auto__1___closed__10;
    v___x_2135_ = l_Lean_mkAtom(v___x_2134_);
    return v___x_2135_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    v___x_2136_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__12_once),
        _init_l_Std_TreeSet___auto__1___closed__12,
    );
    v___x_2137_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2138_ = lean_array_push(v___x_2137_, v___x_2136_);
    return v___x_2138_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    v___x_2140_ = l_Std_TreeSet___auto__1___closed__14;
    v___x_2141_ = lean_string_utf8_byte_size(v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    v___x_2142_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__15_once),
        _init_l_Std_TreeSet___auto__1___closed__15,
    );
    v___x_2143_ = lean_unsigned_to_nat(0);
    v___x_2144_ = l_Std_TreeSet___auto__1___closed__14;
    v___x_2145_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2145_, 0, v___x_2144_);
    lean_ctor_set(v___x_2145_, 1, v___x_2143_);
    lean_ctor_set(v___x_2145_, 2, v___x_2142_);
    return v___x_2145_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    v___x_2148_ = lean_box(0);
    v___x_2149_ = l_Std_TreeSet___auto__1___closed__17;
    v___x_2150_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__16_once),
        _init_l_Std_TreeSet___auto__1___closed__16,
    );
    v___x_2151_ = lean_box(2);
    v___x_2152_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_2152_, 0, v___x_2151_);
    lean_ctor_set(v___x_2152_, 1, v___x_2150_);
    lean_ctor_set(v___x_2152_, 2, v___x_2149_);
    lean_ctor_set(v___x_2152_, 3, v___x_2148_);
    return v___x_2152_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    v___x_2153_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__18_once),
        _init_l_Std_TreeSet___auto__1___closed__18,
    );
    v___x_2154_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__13_once),
        _init_l_Std_TreeSet___auto__1___closed__13,
    );
    v___x_2155_ = lean_array_push(v___x_2154_, v___x_2153_);
    return v___x_2155_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    v___x_2156_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__19_once),
        _init_l_Std_TreeSet___auto__1___closed__19,
    );
    v___x_2157_ = l_Std_TreeSet___auto__1___closed__11;
    v___x_2158_ = lean_box(2);
    v___x_2159_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2159_, 0, v___x_2158_);
    lean_ctor_set(v___x_2159_, 1, v___x_2157_);
    lean_ctor_set(v___x_2159_, 2, v___x_2156_);
    return v___x_2159_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    v___x_2160_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__20_once),
        _init_l_Std_TreeSet___auto__1___closed__20,
    );
    v___x_2161_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2162_ = lean_array_push(v___x_2161_, v___x_2160_);
    return v___x_2162_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    v___x_2163_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__21_once),
        _init_l_Std_TreeSet___auto__1___closed__21,
    );
    v___x_2164_ = l_Std_TreeSet___auto__1___closed__9;
    v___x_2165_ = lean_box(2);
    v___x_2166_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2166_, 0, v___x_2165_);
    lean_ctor_set(v___x_2166_, 1, v___x_2164_);
    lean_ctor_set(v___x_2166_, 2, v___x_2163_);
    return v___x_2166_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    v___x_2167_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__22_once),
        _init_l_Std_TreeSet___auto__1___closed__22,
    );
    v___x_2168_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2169_ = lean_array_push(v___x_2168_, v___x_2167_);
    return v___x_2169_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    v___x_2170_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__23_once),
        _init_l_Std_TreeSet___auto__1___closed__23,
    );
    v___x_2171_ = l_Std_TreeSet___auto__1___closed__7;
    v___x_2172_ = lean_box(2);
    v___x_2173_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2173_, 0, v___x_2172_);
    lean_ctor_set(v___x_2173_, 1, v___x_2171_);
    lean_ctor_set(v___x_2173_, 2, v___x_2170_);
    return v___x_2173_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    v___x_2174_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__24_once),
        _init_l_Std_TreeSet___auto__1___closed__24,
    );
    v___x_2175_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2176_ = lean_array_push(v___x_2175_, v___x_2174_);
    return v___x_2176_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    v___x_2177_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__25_once),
        _init_l_Std_TreeSet___auto__1___closed__25,
    );
    v___x_2178_ = l_Std_TreeSet___auto__1___closed__4;
    v___x_2179_ = lean_box(2);
    v___x_2180_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2180_, 0, v___x_2179_);
    lean_ctor_set(v___x_2180_, 1, v___x_2178_);
    lean_ctor_set(v___x_2180_, 2, v___x_2177_);
    return v___x_2180_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1() -> *mut LeanObject {
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    v___x_2181_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26_once),
        _init_l_Std_TreeSet___auto__1___closed__26,
    );
    return v___x_2181_;
}
pub unsafe fn l_Std_TreeSet_empty(
    mut v_00_u03b1_2182_: *mut LeanObject,
    mut v_cmp_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    v___x_2184_ = lean_box(1);
    return v___x_2184_;
}
pub unsafe fn l_Std_TreeSet_empty___boxed(
    mut v_00_u03b1_2185_: *mut LeanObject,
    mut v_cmp_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2187_: *mut LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Std_TreeSet_empty(v_00_u03b1_2185_, v_cmp_2186_);
    lean_dec_ref(v_cmp_2186_);
    return v_res_2187_;
}
pub unsafe fn l_Std_TreeSet_instEmptyCollection(
    mut v_00_u03b1_2188_: *mut LeanObject,
    mut v_cmp_2189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    v___x_2190_ = lean_box(1);
    return v___x_2190_;
}
pub unsafe fn l_Std_TreeSet_instEmptyCollection___boxed(
    mut v_00_u03b1_2191_: *mut LeanObject,
    mut v_cmp_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2193_: *mut LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Std_TreeSet_instEmptyCollection(v_00_u03b1_2191_, v_cmp_2192_);
    lean_dec_ref(v_cmp_2192_);
    return v_res_2193_;
}
pub unsafe fn l_Std_TreeSet_instInhabited(
    mut v_00_u03b1_2194_: *mut LeanObject,
    mut v_cmp_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    v___x_2196_ = lean_box(1);
    return v___x_2196_;
}
pub unsafe fn l_Std_TreeSet_instInhabited___boxed(
    mut v_00_u03b1_2197_: *mut LeanObject,
    mut v_cmp_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2199_: *mut LeanObject = core::ptr::null_mut();
    v_res_2199_ = l_Std_TreeSet_instInhabited(v_00_u03b1_2197_, v_cmp_2198_);
    lean_dec_ref(v_cmp_2198_);
    return v_res_2199_;
}
pub unsafe fn _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4()
-> *mut LeanObject {
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3;
    v___x_2238_ = l_String_toRawSubstring_x27(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(
    mut v_x_2256_: *mut LeanObject,
    mut v_a_2257_: *mut LeanObject,
    mut v_a_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    v___x_2259_ = l_Std_TreeSet_term___x7em___00__closed__3;
    lean_inc(v_x_2256_);
    v___x_2260_ = l_Lean_Syntax_isOfKind(v_x_2256_, v___x_2259_);
    if v___x_2260_ == 0 {
        let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2256_);
        v___x_2261_ = lean_box(1);
        v___x_2262_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2262_, 0, v___x_2261_);
        lean_ctor_set(v___x_2262_, 1, v_a_2258_);
        return v___x_2262_;
    } else {
        let mut v_quotContext_2263_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2264_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2270_: u8 = 0;
        let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2263_ = lean_ctor_get(v_a_2257_, 1);
        v_currMacroScope_2264_ = lean_ctor_get(v_a_2257_, 2);
        v_ref_2265_ = lean_ctor_get(v_a_2257_, 5);
        v___x_2266_ = lean_unsigned_to_nat(0);
        v___x_2267_ = l_Lean_Syntax_getArg(v_x_2256_, v___x_2266_);
        v___x_2268_ = lean_unsigned_to_nat(2);
        v___x_2269_ = l_Lean_Syntax_getArg(v_x_2256_, v___x_2268_);
        lean_dec(v_x_2256_);
        v___x_2270_ = 0;
        v___x_2271_ = l_Lean_SourceInfo_fromRef(v_ref_2265_, v___x_2270_);
        v___x_2272_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2;
        v___x_2273_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4), core::ptr::addr_of_mut!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once), _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4);
        v___x_2274_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5;
        lean_inc(v_currMacroScope_2264_);
        lean_inc(v_quotContext_2263_);
        v___x_2275_ =
            l_Lean_addMacroScope(v_quotContext_2263_, v___x_2274_, v_currMacroScope_2264_);
        v___x_2276_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10;
        lean_inc_n(v___x_2271_, 2);
        v___x_2277_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2277_, 0, v___x_2271_);
        lean_ctor_set(v___x_2277_, 1, v___x_2273_);
        lean_ctor_set(v___x_2277_, 2, v___x_2275_);
        lean_ctor_set(v___x_2277_, 3, v___x_2276_);
        v___x_2278_ = l_Std_TreeSet___auto__1___closed__9;
        v___x_2279_ = l_Lean_Syntax_node2(v___x_2271_, v___x_2278_, v___x_2267_, v___x_2269_);
        v___x_2280_ = l_Lean_Syntax_node2(v___x_2271_, v___x_2272_, v___x_2277_, v___x_2279_);
        v___x_2281_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2281_, 0, v___x_2280_);
        lean_ctor_set(v___x_2281_, 1, v_a_2258_);
        return v___x_2281_;
    }
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___boxed(
    mut v_x_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2285_: *mut LeanObject = core::ptr::null_mut();
    v_res_2285_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(v_x_2282_, v_a_2283_, v_a_2284_);
    lean_dec_ref(v_a_2283_);
    return v_res_2285_;
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(
    mut v_x_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
    mut v_a_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    v___x_2292_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2;
    lean_inc(v_x_2289_);
    v___x_2293_ = l_Lean_Syntax_isOfKind(v_x_2289_, v___x_2292_);
    if v___x_2293_ == 0 {
        let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2289_);
        v___x_2294_ = lean_box(0);
        v___x_2295_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2295_, 0, v___x_2294_);
        lean_ctor_set(v___x_2295_, 1, v_a_2291_);
        return v___x_2295_;
    } else {
        let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: u8 = 0;
        v___x_2296_ = lean_unsigned_to_nat(0);
        v___x_2297_ = l_Lean_Syntax_getArg(v_x_2289_, v___x_2296_);
        v___x_2298_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1;
        lean_inc(v___x_2297_);
        v___x_2299_ = l_Lean_Syntax_isOfKind(v___x_2297_, v___x_2298_);
        if v___x_2299_ == 0 {
            let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2297_);
            lean_dec(v_x_2289_);
            v___x_2300_ = lean_box(0);
            v___x_2301_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2301_, 0, v___x_2300_);
            lean_ctor_set(v___x_2301_, 1, v_a_2291_);
            return v___x_2301_;
        } else {
            let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2305_: u8 = 0;
            v___x_2302_ = lean_unsigned_to_nat(1);
            v___x_2303_ = l_Lean_Syntax_getArg(v_x_2289_, v___x_2302_);
            lean_dec(v_x_2289_);
            v___x_2304_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_2303_);
            v___x_2305_ = l_Lean_Syntax_matchesNull(v___x_2303_, v___x_2304_);
            if v___x_2305_ == 0 {
                let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2303_);
                lean_dec(v___x_2297_);
                v___x_2306_ = lean_box(0);
                v___x_2307_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2307_, 0, v___x_2306_);
                lean_ctor_set(v___x_2307_, 1, v_a_2291_);
                return v___x_2307_;
            } else {
                let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_2310_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2311_: u8 = 0;
                let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
                v___x_2308_ = l_Lean_Syntax_getArg(v___x_2303_, v___x_2296_);
                v___x_2309_ = l_Lean_Syntax_getArg(v___x_2303_, v___x_2302_);
                lean_dec(v___x_2303_);
                v_ref_2310_ = l_Lean_replaceRef(v___x_2297_, v_a_2290_);
                lean_dec(v___x_2297_);
                v___x_2311_ = 0;
                v___x_2312_ = l_Lean_SourceInfo_fromRef(v_ref_2310_, v___x_2311_);
                lean_dec(v_ref_2310_);
                v___x_2313_ = l_Std_TreeSet_term___x7em___00__closed__3;
                v___x_2314_ = l_Std_TreeSet_term___x7em___00__closed__6;
                lean_inc(v___x_2312_);
                v___x_2315_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2315_, 0, v___x_2312_);
                lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                v___x_2316_ = l_Lean_Syntax_node3(
                    v___x_2312_,
                    v___x_2313_,
                    v___x_2308_,
                    v___x_2315_,
                    v___x_2309_,
                );
                v___x_2317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2317_, 0, v___x_2316_);
                lean_ctor_set(v___x_2317_, 1, v_a_2291_);
                return v___x_2317_;
            }
        }
    }
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(
    mut v_x_2318_: *mut LeanObject,
    mut v_a_2319_: *mut LeanObject,
    mut v_a_2320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2321_: *mut LeanObject = core::ptr::null_mut();
    v_res_2321_ =
        l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(
            v_x_2318_, v_a_2319_, v_a_2320_,
        );
    lean_dec(v_a_2319_);
    return v_res_2321_;
}
pub unsafe fn l_Std_TreeSet_insert___redArg(
    mut v_cmp_2322_: *mut LeanObject,
    mut v_l_2323_: *mut LeanObject,
    mut v_a_2324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2325_: u8 = 0;
    lean_inc(v_l_2323_);
    lean_inc(v_a_2324_);
    lean_inc_ref(v_cmp_2322_);
    v___x_2325_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2322_, v_a_2324_, v_l_2323_);
    if v___x_2325_ == 0 {
        let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
        v___x_2326_ = lean_box(0);
        v___x_2327_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2322_,
            v_a_2324_,
            v___x_2326_,
            v_l_2323_,
        );
        return v___x_2327_;
    } else {
        lean_dec(v_a_2324_);
        lean_dec_ref(v_cmp_2322_);
        return v_l_2323_;
    }
}
pub unsafe fn l_Std_TreeSet_insert(
    mut v_00_u03b1_2328_: *mut LeanObject,
    mut v_cmp_2329_: *mut LeanObject,
    mut v_l_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2332_: u8 = 0;
    lean_inc(v_l_2330_);
    lean_inc(v_a_2331_);
    lean_inc_ref(v_cmp_2329_);
    v___x_2332_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2329_, v_a_2331_, v_l_2330_);
    if v___x_2332_ == 0 {
        let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
        v___x_2333_ = lean_box(0);
        v___x_2334_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2329_,
            v_a_2331_,
            v___x_2333_,
            v_l_2330_,
        );
        return v___x_2334_;
    } else {
        lean_dec(v_a_2331_);
        lean_dec_ref(v_cmp_2329_);
        return v_l_2330_;
    }
}
pub unsafe fn l_Std_TreeSet_instSingleton___redArg___lam__0(
    mut v_cmp_2335_: *mut LeanObject,
    mut v_e_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    v___x_2337_ = lean_box(1);
    lean_inc(v_e_2336_);
    lean_inc_ref(v_cmp_2335_);
    v___x_2338_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2335_, v_e_2336_, v___x_2337_);
    if v___x_2338_ == 0 {
        let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
        v___x_2339_ = lean_box(0);
        v___x_2340_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2335_,
            v_e_2336_,
            v___x_2339_,
            v___x_2337_,
        );
        return v___x_2340_;
    } else {
        lean_dec(v_e_2336_);
        lean_dec_ref(v_cmp_2335_);
        return v___x_2337_;
    }
}
pub unsafe fn l_Std_TreeSet_instSingleton___redArg(
    mut v_cmp_2341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2342_: *mut LeanObject = core::ptr::null_mut();
    v___f_2342_ = lean_alloc_closure(
        l_Std_TreeSet_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2342_, 0, v_cmp_2341_);
    return v___f_2342_;
}
pub unsafe fn l_Std_TreeSet_instSingleton(
    mut v_00_u03b1_2343_: *mut LeanObject,
    mut v_cmp_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2345_: *mut LeanObject = core::ptr::null_mut();
    v___f_2345_ = lean_alloc_closure(
        l_Std_TreeSet_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2345_, 0, v_cmp_2344_);
    return v___f_2345_;
}
pub unsafe fn l_Std_TreeSet_instInsert___redArg___lam__0(
    mut v_cmp_2346_: *mut LeanObject,
    mut v_e_2347_: *mut LeanObject,
    mut v_s_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2349_: u8 = 0;
    lean_inc(v_s_2348_);
    lean_inc(v_e_2347_);
    lean_inc_ref(v_cmp_2346_);
    v___x_2349_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2346_, v_e_2347_, v_s_2348_);
    if v___x_2349_ == 0 {
        let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
        v___x_2350_ = lean_box(0);
        v___x_2351_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2346_,
            v_e_2347_,
            v___x_2350_,
            v_s_2348_,
        );
        return v___x_2351_;
    } else {
        lean_dec(v_e_2347_);
        lean_dec_ref(v_cmp_2346_);
        return v_s_2348_;
    }
}
pub unsafe fn l_Std_TreeSet_instInsert___redArg(
    mut v_cmp_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2353_: *mut LeanObject = core::ptr::null_mut();
    v___f_2353_ = lean_alloc_closure(
        l_Std_TreeSet_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2353_, 0, v_cmp_2352_);
    return v___f_2353_;
}
pub unsafe fn l_Std_TreeSet_instInsert(
    mut v_00_u03b1_2354_: *mut LeanObject,
    mut v_cmp_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2356_: *mut LeanObject = core::ptr::null_mut();
    v___f_2356_ = lean_alloc_closure(
        l_Std_TreeSet_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2356_, 0, v_cmp_2355_);
    return v___f_2356_;
}
pub unsafe fn l_Std_TreeSet_containsThenInsert___redArg(
    mut v_cmp_2357_: *mut LeanObject,
    mut v_t_2358_: *mut LeanObject,
    mut v_a_2359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2360_: u8 = 0;
    lean_inc(v_t_2358_);
    lean_inc(v_a_2359_);
    lean_inc_ref(v_cmp_2357_);
    v___x_2360_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2357_, v_a_2359_, v_t_2358_);
    if v___x_2360_ == 0 {
        let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
        v___x_2361_ = lean_box(0);
        v___x_2362_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2357_,
            v_a_2359_,
            v___x_2361_,
            v_t_2358_,
        );
        v___x_2363_ = lean_box((v___x_2360_) as usize);
        v___x_2364_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2364_, 0, v___x_2363_);
        lean_ctor_set(v___x_2364_, 1, v___x_2362_);
        return v___x_2364_;
    } else {
        let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_2359_);
        lean_dec_ref(v_cmp_2357_);
        v___x_2365_ = lean_box((v___x_2360_) as usize);
        v___x_2366_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2366_, 0, v___x_2365_);
        lean_ctor_set(v___x_2366_, 1, v_t_2358_);
        return v___x_2366_;
    }
}
pub unsafe fn l_Std_TreeSet_containsThenInsert(
    mut v_00_u03b1_2367_: *mut LeanObject,
    mut v_cmp_2368_: *mut LeanObject,
    mut v_t_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2371_: u8 = 0;
    lean_inc(v_t_2369_);
    lean_inc(v_a_2370_);
    lean_inc_ref(v_cmp_2368_);
    v___x_2371_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2368_, v_a_2370_, v_t_2369_);
    if v___x_2371_ == 0 {
        let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
        v___x_2372_ = lean_box(0);
        v___x_2373_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2368_,
            v_a_2370_,
            v___x_2372_,
            v_t_2369_,
        );
        v___x_2374_ = lean_box((v___x_2371_) as usize);
        v___x_2375_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2375_, 0, v___x_2374_);
        lean_ctor_set(v___x_2375_, 1, v___x_2373_);
        return v___x_2375_;
    } else {
        let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_2370_);
        lean_dec_ref(v_cmp_2368_);
        v___x_2376_ = lean_box((v___x_2371_) as usize);
        v___x_2377_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2377_, 0, v___x_2376_);
        lean_ctor_set(v___x_2377_, 1, v_t_2369_);
        return v___x_2377_;
    }
}
pub unsafe fn l_Std_TreeSet_contains___redArg(
    mut v_cmp_2378_: *mut LeanObject,
    mut v_l_2379_: *mut LeanObject,
    mut v_a_2380_: *mut LeanObject,
) -> u8 {
    let mut v___x_2381_: u8 = 0;
    v___x_2381_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2378_, v_a_2380_, v_l_2379_);
    return v___x_2381_;
}
pub unsafe fn l_Std_TreeSet_contains___redArg___boxed(
    mut v_cmp_2382_: *mut LeanObject,
    mut v_l_2383_: *mut LeanObject,
    mut v_a_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2385_: u8 = 0;
    let mut v_r_2386_: *mut LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_Std_TreeSet_contains___redArg(v_cmp_2382_, v_l_2383_, v_a_2384_);
    v_r_2386_ = lean_box((v_res_2385_) as usize);
    return v_r_2386_;
}
pub unsafe fn l_Std_TreeSet_contains(
    mut v_00_u03b1_2387_: *mut LeanObject,
    mut v_cmp_2388_: *mut LeanObject,
    mut v_l_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
) -> u8 {
    let mut v___x_2391_: u8 = 0;
    v___x_2391_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2388_, v_a_2390_, v_l_2389_);
    return v___x_2391_;
}
pub unsafe fn l_Std_TreeSet_contains___boxed(
    mut v_00_u03b1_2392_: *mut LeanObject,
    mut v_cmp_2393_: *mut LeanObject,
    mut v_l_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2396_: u8 = 0;
    let mut v_r_2397_: *mut LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Std_TreeSet_contains(v_00_u03b1_2392_, v_cmp_2393_, v_l_2394_, v_a_2395_);
    v_r_2397_ = lean_box((v_res_2396_) as usize);
    return v_r_2397_;
}
pub unsafe fn l_Std_TreeSet_instMembership(
    mut v_00_u03b1_2398_: *mut LeanObject,
    mut v_cmp_2399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    v___x_2400_ = lean_box(0);
    return v___x_2400_;
}
pub unsafe fn l_Std_TreeSet_instMembership___boxed(
    mut v_00_u03b1_2401_: *mut LeanObject,
    mut v_cmp_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2403_: *mut LeanObject = core::ptr::null_mut();
    v_res_2403_ = l_Std_TreeSet_instMembership(v_00_u03b1_2401_, v_cmp_2402_);
    lean_dec_ref(v_cmp_2402_);
    return v_res_2403_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem___redArg(
    mut v_cmp_2404_: *mut LeanObject,
    mut v_m_2405_: *mut LeanObject,
    mut v_a_2406_: *mut LeanObject,
) -> u8 {
    let mut v___x_2407_: u8 = 0;
    v___x_2407_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2404_, v_a_2406_, v_m_2405_);
    return v___x_2407_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem___redArg___boxed(
    mut v_cmp_2408_: *mut LeanObject,
    mut v_m_2409_: *mut LeanObject,
    mut v_a_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2411_: u8 = 0;
    let mut v_r_2412_: *mut LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_2408_, v_m_2409_, v_a_2410_);
    v_r_2412_ = lean_box((v_res_2411_) as usize);
    return v_r_2412_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem(
    mut v_00_u03b1_2413_: *mut LeanObject,
    mut v_cmp_2414_: *mut LeanObject,
    mut v_m_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
) -> u8 {
    let mut v___x_2417_: u8 = 0;
    v___x_2417_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2414_, v_a_2416_, v_m_2415_);
    return v___x_2417_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem___boxed(
    mut v_00_u03b1_2418_: *mut LeanObject,
    mut v_cmp_2419_: *mut LeanObject,
    mut v_m_2420_: *mut LeanObject,
    mut v_a_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2422_: u8 = 0;
    let mut v_r_2423_: *mut LeanObject = core::ptr::null_mut();
    v_res_2422_ =
        l_Std_TreeSet_instDecidableMem(v_00_u03b1_2418_, v_cmp_2419_, v_m_2420_, v_a_2421_);
    v_r_2423_ = lean_box((v_res_2422_) as usize);
    return v_r_2423_;
}
pub unsafe fn l_Std_TreeSet_size___redArg(mut v_t_2424_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_t_2424_) == 0 {
        let mut v_size_2425_: *mut LeanObject = core::ptr::null_mut();
        v_size_2425_ = lean_ctor_get(v_t_2424_, 0);
        lean_inc(v_size_2425_);
        return v_size_2425_;
    } else {
        let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
        v___x_2426_ = lean_unsigned_to_nat(0);
        return v___x_2426_;
    }
}
pub unsafe fn l_Std_TreeSet_size___redArg___boxed(
    mut v_t_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2428_: *mut LeanObject = core::ptr::null_mut();
    v_res_2428_ = l_Std_TreeSet_size___redArg(v_t_2427_);
    lean_dec(v_t_2427_);
    return v_res_2428_;
}
pub unsafe fn l_Std_TreeSet_size(
    mut v_00_u03b1_2429_: *mut LeanObject,
    mut v_cmp_2430_: *mut LeanObject,
    mut v_t_2431_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_2431_) == 0 {
        let mut v_size_2432_: *mut LeanObject = core::ptr::null_mut();
        v_size_2432_ = lean_ctor_get(v_t_2431_, 0);
        lean_inc(v_size_2432_);
        return v_size_2432_;
    } else {
        let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
        v___x_2433_ = lean_unsigned_to_nat(0);
        return v___x_2433_;
    }
}
pub unsafe fn l_Std_TreeSet_size___boxed(
    mut v_00_u03b1_2434_: *mut LeanObject,
    mut v_cmp_2435_: *mut LeanObject,
    mut v_t_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2437_: *mut LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Std_TreeSet_size(v_00_u03b1_2434_, v_cmp_2435_, v_t_2436_);
    lean_dec(v_t_2436_);
    lean_dec_ref(v_cmp_2435_);
    return v_res_2437_;
}
pub unsafe fn l_Std_TreeSet_isEmpty___redArg(mut v_t_2438_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_t_2438_) == 0 {
        let mut v___x_2439_: u8 = 0;
        v___x_2439_ = 0;
        return v___x_2439_;
    } else {
        let mut v___x_2440_: u8 = 0;
        v___x_2440_ = 1;
        return v___x_2440_;
    }
}
pub unsafe fn l_Std_TreeSet_isEmpty___redArg___boxed(
    mut v_t_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2442_: u8 = 0;
    let mut v_r_2443_: *mut LeanObject = core::ptr::null_mut();
    v_res_2442_ = l_Std_TreeSet_isEmpty___redArg(v_t_2441_);
    lean_dec(v_t_2441_);
    v_r_2443_ = lean_box((v_res_2442_) as usize);
    return v_r_2443_;
}
pub unsafe fn l_Std_TreeSet_isEmpty(
    mut v_00_u03b1_2444_: *mut LeanObject,
    mut v_cmp_2445_: *mut LeanObject,
    mut v_t_2446_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_t_2446_) == 0 {
        let mut v___x_2447_: u8 = 0;
        v___x_2447_ = 0;
        return v___x_2447_;
    } else {
        let mut v___x_2448_: u8 = 0;
        v___x_2448_ = 1;
        return v___x_2448_;
    }
}
pub unsafe fn l_Std_TreeSet_isEmpty___boxed(
    mut v_00_u03b1_2449_: *mut LeanObject,
    mut v_cmp_2450_: *mut LeanObject,
    mut v_t_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2452_: u8 = 0;
    let mut v_r_2453_: *mut LeanObject = core::ptr::null_mut();
    v_res_2452_ = l_Std_TreeSet_isEmpty(v_00_u03b1_2449_, v_cmp_2450_, v_t_2451_);
    lean_dec(v_t_2451_);
    lean_dec_ref(v_cmp_2450_);
    v_r_2453_ = lean_box((v_res_2452_) as usize);
    return v_r_2453_;
}
pub unsafe fn l_Std_TreeSet_erase___redArg(
    mut v_cmp_2454_: *mut LeanObject,
    mut v_t_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2454_, v_a_2456_, v_t_2455_);
    return v___x_2457_;
}
pub unsafe fn l_Std_TreeSet_erase(
    mut v_00_u03b1_2458_: *mut LeanObject,
    mut v_cmp_2459_: *mut LeanObject,
    mut v_t_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2459_, v_a_2461_, v_t_2460_);
    return v___x_2462_;
}
pub unsafe fn l_Std_TreeSet_get_x3f___redArg(
    mut v_cmp_2463_: *mut LeanObject,
    mut v_t_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    v___x_2466_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2463_, v_t_2464_, v_a_2465_);
    return v___x_2466_;
}
pub unsafe fn l_Std_TreeSet_get_x3f(
    mut v_00_u03b1_2467_: *mut LeanObject,
    mut v_cmp_2468_: *mut LeanObject,
    mut v_t_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v___x_2471_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2468_, v_t_2469_, v_a_2470_);
    return v___x_2471_;
}
pub unsafe fn l_Std_TreeSet_get___redArg(
    mut v_cmp_2472_: *mut LeanObject,
    mut v_t_2473_: *mut LeanObject,
    mut v_a_2474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2472_, v_t_2473_, v_a_2474_);
    return v___x_2475_;
}
pub unsafe fn l_Std_TreeSet_get(
    mut v_00_u03b1_2476_: *mut LeanObject,
    mut v_cmp_2477_: *mut LeanObject,
    mut v_t_2478_: *mut LeanObject,
    mut v_a_2479_: *mut LeanObject,
    mut v_h_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v___x_2481_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2477_, v_t_2478_, v_a_2479_);
    return v___x_2481_;
}
pub unsafe fn l_Std_TreeSet_get_x21___redArg(
    mut v_cmp_2482_: *mut LeanObject,
    mut v_inst_2483_: *mut LeanObject,
    mut v_t_2484_: *mut LeanObject,
    mut v_a_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2486_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2482_,
        v_t_2484_,
        v_a_2485_,
        v_inst_2483_,
    );
    return v___x_2486_;
}
pub unsafe fn l_Std_TreeSet_get_x21___redArg___boxed(
    mut v_cmp_2487_: *mut LeanObject,
    mut v_inst_2488_: *mut LeanObject,
    mut v_t_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2491_: *mut LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Std_TreeSet_get_x21___redArg(v_cmp_2487_, v_inst_2488_, v_t_2489_, v_a_2490_);
    lean_dec(v_inst_2488_);
    return v_res_2491_;
}
pub unsafe fn l_Std_TreeSet_get_x21(
    mut v_00_u03b1_2492_: *mut LeanObject,
    mut v_cmp_2493_: *mut LeanObject,
    mut v_inst_2494_: *mut LeanObject,
    mut v_t_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    v___x_2497_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2493_,
        v_t_2495_,
        v_a_2496_,
        v_inst_2494_,
    );
    return v___x_2497_;
}
pub unsafe fn l_Std_TreeSet_get_x21___boxed(
    mut v_00_u03b1_2498_: *mut LeanObject,
    mut v_cmp_2499_: *mut LeanObject,
    mut v_inst_2500_: *mut LeanObject,
    mut v_t_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2503_: *mut LeanObject = core::ptr::null_mut();
    v_res_2503_ = l_Std_TreeSet_get_x21(
        v_00_u03b1_2498_,
        v_cmp_2499_,
        v_inst_2500_,
        v_t_2501_,
        v_a_2502_,
    );
    lean_dec(v_inst_2500_);
    return v_res_2503_;
}
pub unsafe fn l_Std_TreeSet_getD___redArg(
    mut v_cmp_2504_: *mut LeanObject,
    mut v_t_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
    mut v_fallback_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2504_,
        v_t_2505_,
        v_a_2506_,
        v_fallback_2507_,
    );
    return v___x_2508_;
}
pub unsafe fn l_Std_TreeSet_getD___redArg___boxed(
    mut v_cmp_2509_: *mut LeanObject,
    mut v_t_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_fallback_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2513_: *mut LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Std_TreeSet_getD___redArg(v_cmp_2509_, v_t_2510_, v_a_2511_, v_fallback_2512_);
    lean_dec(v_fallback_2512_);
    return v_res_2513_;
}
pub unsafe fn l_Std_TreeSet_getD(
    mut v_00_u03b1_2514_: *mut LeanObject,
    mut v_cmp_2515_: *mut LeanObject,
    mut v_t_2516_: *mut LeanObject,
    mut v_a_2517_: *mut LeanObject,
    mut v_fallback_2518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2515_,
        v_t_2516_,
        v_a_2517_,
        v_fallback_2518_,
    );
    return v___x_2519_;
}
pub unsafe fn l_Std_TreeSet_getD___boxed(
    mut v_00_u03b1_2520_: *mut LeanObject,
    mut v_cmp_2521_: *mut LeanObject,
    mut v_t_2522_: *mut LeanObject,
    mut v_a_2523_: *mut LeanObject,
    mut v_fallback_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2525_: *mut LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Std_TreeSet_getD(
        v_00_u03b1_2520_,
        v_cmp_2521_,
        v_t_2522_,
        v_a_2523_,
        v_fallback_2524_,
    );
    lean_dec(v_fallback_2524_);
    return v_res_2525_;
}
pub unsafe fn l_Std_TreeSet_min_x3f___redArg(mut v_t_2526_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    v___x_2527_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2526_);
    return v___x_2527_;
}
pub unsafe fn l_Std_TreeSet_min_x3f___redArg___boxed(
    mut v_t_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_TreeSet_min_x3f___redArg(v_t_2528_);
    lean_dec(v_t_2528_);
    return v_res_2529_;
}
pub unsafe fn l_Std_TreeSet_min_x3f(
    mut v_00_u03b1_2530_: *mut LeanObject,
    mut v_cmp_2531_: *mut LeanObject,
    mut v_t_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    v___x_2533_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2532_);
    return v___x_2533_;
}
pub unsafe fn l_Std_TreeSet_min_x3f___boxed(
    mut v_00_u03b1_2534_: *mut LeanObject,
    mut v_cmp_2535_: *mut LeanObject,
    mut v_t_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2537_: *mut LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Std_TreeSet_min_x3f(v_00_u03b1_2534_, v_cmp_2535_, v_t_2536_);
    lean_dec(v_t_2536_);
    lean_dec_ref(v_cmp_2535_);
    return v_res_2537_;
}
pub unsafe fn l_Std_TreeSet_min___redArg(mut v_t_2538_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    v___x_2539_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2538_);
    return v___x_2539_;
}
pub unsafe fn l_Std_TreeSet_min___redArg___boxed(
    mut v_t_2540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2541_: *mut LeanObject = core::ptr::null_mut();
    v_res_2541_ = l_Std_TreeSet_min___redArg(v_t_2540_);
    lean_dec(v_t_2540_);
    return v_res_2541_;
}
pub unsafe fn l_Std_TreeSet_min(
    mut v_00_u03b1_2542_: *mut LeanObject,
    mut v_cmp_2543_: *mut LeanObject,
    mut v_t_2544_: *mut LeanObject,
    mut v_h_2545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    v___x_2546_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2544_);
    return v___x_2546_;
}
pub unsafe fn l_Std_TreeSet_min___boxed(
    mut v_00_u03b1_2547_: *mut LeanObject,
    mut v_cmp_2548_: *mut LeanObject,
    mut v_t_2549_: *mut LeanObject,
    mut v_h_2550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2551_: *mut LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_Std_TreeSet_min(v_00_u03b1_2547_, v_cmp_2548_, v_t_2549_, v_h_2550_);
    lean_dec(v_t_2549_);
    lean_dec_ref(v_cmp_2548_);
    return v_res_2551_;
}
pub unsafe fn l_Std_TreeSet_min_x21___redArg(
    mut v_inst_2552_: *mut LeanObject,
    mut v_t_2553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    v___x_2554_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2552_, v_t_2553_);
    return v___x_2554_;
}
pub unsafe fn l_Std_TreeSet_min_x21___redArg___boxed(
    mut v_inst_2555_: *mut LeanObject,
    mut v_t_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2557_: *mut LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Std_TreeSet_min_x21___redArg(v_inst_2555_, v_t_2556_);
    lean_dec(v_t_2556_);
    lean_dec(v_inst_2555_);
    return v_res_2557_;
}
pub unsafe fn l_Std_TreeSet_min_x21(
    mut v_00_u03b1_2558_: *mut LeanObject,
    mut v_cmp_2559_: *mut LeanObject,
    mut v_inst_2560_: *mut LeanObject,
    mut v_t_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2560_, v_t_2561_);
    return v___x_2562_;
}
pub unsafe fn l_Std_TreeSet_min_x21___boxed(
    mut v_00_u03b1_2563_: *mut LeanObject,
    mut v_cmp_2564_: *mut LeanObject,
    mut v_inst_2565_: *mut LeanObject,
    mut v_t_2566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2567_: *mut LeanObject = core::ptr::null_mut();
    v_res_2567_ = l_Std_TreeSet_min_x21(v_00_u03b1_2563_, v_cmp_2564_, v_inst_2565_, v_t_2566_);
    lean_dec(v_t_2566_);
    lean_dec(v_inst_2565_);
    lean_dec_ref(v_cmp_2564_);
    return v_res_2567_;
}
pub unsafe fn l_Std_TreeSet_minD___redArg(
    mut v_t_2568_: *mut LeanObject,
    mut v_fallback_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    v___x_2570_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2568_, v_fallback_2569_);
    return v___x_2570_;
}
pub unsafe fn l_Std_TreeSet_minD___redArg___boxed(
    mut v_t_2571_: *mut LeanObject,
    mut v_fallback_2572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2573_: *mut LeanObject = core::ptr::null_mut();
    v_res_2573_ = l_Std_TreeSet_minD___redArg(v_t_2571_, v_fallback_2572_);
    lean_dec(v_fallback_2572_);
    lean_dec(v_t_2571_);
    return v_res_2573_;
}
pub unsafe fn l_Std_TreeSet_minD(
    mut v_00_u03b1_2574_: *mut LeanObject,
    mut v_cmp_2575_: *mut LeanObject,
    mut v_t_2576_: *mut LeanObject,
    mut v_fallback_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2576_, v_fallback_2577_);
    return v___x_2578_;
}
pub unsafe fn l_Std_TreeSet_minD___boxed(
    mut v_00_u03b1_2579_: *mut LeanObject,
    mut v_cmp_2580_: *mut LeanObject,
    mut v_t_2581_: *mut LeanObject,
    mut v_fallback_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2583_: *mut LeanObject = core::ptr::null_mut();
    v_res_2583_ = l_Std_TreeSet_minD(v_00_u03b1_2579_, v_cmp_2580_, v_t_2581_, v_fallback_2582_);
    lean_dec(v_fallback_2582_);
    lean_dec(v_t_2581_);
    lean_dec_ref(v_cmp_2580_);
    return v_res_2583_;
}
pub unsafe fn l_Std_TreeSet_max_x3f___redArg(mut v_t_2584_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    v___x_2585_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2584_);
    return v___x_2585_;
}
pub unsafe fn l_Std_TreeSet_max_x3f___redArg___boxed(
    mut v_t_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2587_: *mut LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Std_TreeSet_max_x3f___redArg(v_t_2586_);
    lean_dec(v_t_2586_);
    return v_res_2587_;
}
pub unsafe fn l_Std_TreeSet_max_x3f(
    mut v_00_u03b1_2588_: *mut LeanObject,
    mut v_cmp_2589_: *mut LeanObject,
    mut v_t_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    v___x_2591_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2590_);
    return v___x_2591_;
}
pub unsafe fn l_Std_TreeSet_max_x3f___boxed(
    mut v_00_u03b1_2592_: *mut LeanObject,
    mut v_cmp_2593_: *mut LeanObject,
    mut v_t_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2595_: *mut LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_Std_TreeSet_max_x3f(v_00_u03b1_2592_, v_cmp_2593_, v_t_2594_);
    lean_dec(v_t_2594_);
    lean_dec_ref(v_cmp_2593_);
    return v_res_2595_;
}
pub unsafe fn l_Std_TreeSet_max___redArg(mut v_t_2596_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    v___x_2597_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2596_);
    return v___x_2597_;
}
pub unsafe fn l_Std_TreeSet_max___redArg___boxed(
    mut v_t_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2599_: *mut LeanObject = core::ptr::null_mut();
    v_res_2599_ = l_Std_TreeSet_max___redArg(v_t_2598_);
    lean_dec(v_t_2598_);
    return v_res_2599_;
}
pub unsafe fn l_Std_TreeSet_max(
    mut v_00_u03b1_2600_: *mut LeanObject,
    mut v_cmp_2601_: *mut LeanObject,
    mut v_t_2602_: *mut LeanObject,
    mut v_h_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2602_);
    return v___x_2604_;
}
pub unsafe fn l_Std_TreeSet_max___boxed(
    mut v_00_u03b1_2605_: *mut LeanObject,
    mut v_cmp_2606_: *mut LeanObject,
    mut v_t_2607_: *mut LeanObject,
    mut v_h_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2609_: *mut LeanObject = core::ptr::null_mut();
    v_res_2609_ = l_Std_TreeSet_max(v_00_u03b1_2605_, v_cmp_2606_, v_t_2607_, v_h_2608_);
    lean_dec(v_t_2607_);
    lean_dec_ref(v_cmp_2606_);
    return v_res_2609_;
}
pub unsafe fn l_Std_TreeSet_max_x21___redArg(
    mut v_inst_2610_: *mut LeanObject,
    mut v_t_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    v___x_2612_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2610_, v_t_2611_);
    return v___x_2612_;
}
pub unsafe fn l_Std_TreeSet_max_x21___redArg___boxed(
    mut v_inst_2613_: *mut LeanObject,
    mut v_t_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2615_: *mut LeanObject = core::ptr::null_mut();
    v_res_2615_ = l_Std_TreeSet_max_x21___redArg(v_inst_2613_, v_t_2614_);
    lean_dec(v_t_2614_);
    lean_dec(v_inst_2613_);
    return v_res_2615_;
}
pub unsafe fn l_Std_TreeSet_max_x21(
    mut v_00_u03b1_2616_: *mut LeanObject,
    mut v_cmp_2617_: *mut LeanObject,
    mut v_inst_2618_: *mut LeanObject,
    mut v_t_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    v___x_2620_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2618_, v_t_2619_);
    return v___x_2620_;
}
pub unsafe fn l_Std_TreeSet_max_x21___boxed(
    mut v_00_u03b1_2621_: *mut LeanObject,
    mut v_cmp_2622_: *mut LeanObject,
    mut v_inst_2623_: *mut LeanObject,
    mut v_t_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Std_TreeSet_max_x21(v_00_u03b1_2621_, v_cmp_2622_, v_inst_2623_, v_t_2624_);
    lean_dec(v_t_2624_);
    lean_dec(v_inst_2623_);
    lean_dec_ref(v_cmp_2622_);
    return v_res_2625_;
}
pub unsafe fn l_Std_TreeSet_maxD___redArg(
    mut v_t_2626_: *mut LeanObject,
    mut v_fallback_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    v___x_2628_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2626_, v_fallback_2627_);
    return v___x_2628_;
}
pub unsafe fn l_Std_TreeSet_maxD___redArg___boxed(
    mut v_t_2629_: *mut LeanObject,
    mut v_fallback_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2631_: *mut LeanObject = core::ptr::null_mut();
    v_res_2631_ = l_Std_TreeSet_maxD___redArg(v_t_2629_, v_fallback_2630_);
    lean_dec(v_fallback_2630_);
    lean_dec(v_t_2629_);
    return v_res_2631_;
}
pub unsafe fn l_Std_TreeSet_maxD(
    mut v_00_u03b1_2632_: *mut LeanObject,
    mut v_cmp_2633_: *mut LeanObject,
    mut v_t_2634_: *mut LeanObject,
    mut v_fallback_2635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2634_, v_fallback_2635_);
    return v___x_2636_;
}
pub unsafe fn l_Std_TreeSet_maxD___boxed(
    mut v_00_u03b1_2637_: *mut LeanObject,
    mut v_cmp_2638_: *mut LeanObject,
    mut v_t_2639_: *mut LeanObject,
    mut v_fallback_2640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2641_: *mut LeanObject = core::ptr::null_mut();
    v_res_2641_ = l_Std_TreeSet_maxD(v_00_u03b1_2637_, v_cmp_2638_, v_t_2639_, v_fallback_2640_);
    lean_dec(v_fallback_2640_);
    lean_dec(v_t_2639_);
    lean_dec_ref(v_cmp_2638_);
    return v_res_2641_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f___redArg(
    mut v_t_2642_: *mut LeanObject,
    mut v_n_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2642_, v_n_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f___redArg___boxed(
    mut v_t_2645_: *mut LeanObject,
    mut v_n_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2647_: *mut LeanObject = core::ptr::null_mut();
    v_res_2647_ = l_Std_TreeSet_atIdx_x3f___redArg(v_t_2645_, v_n_2646_);
    lean_dec(v_t_2645_);
    return v_res_2647_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f(
    mut v_00_u03b1_2648_: *mut LeanObject,
    mut v_cmp_2649_: *mut LeanObject,
    mut v_t_2650_: *mut LeanObject,
    mut v_n_2651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2650_, v_n_2651_);
    return v___x_2652_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f___boxed(
    mut v_00_u03b1_2653_: *mut LeanObject,
    mut v_cmp_2654_: *mut LeanObject,
    mut v_t_2655_: *mut LeanObject,
    mut v_n_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2657_: *mut LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Std_TreeSet_atIdx_x3f(v_00_u03b1_2653_, v_cmp_2654_, v_t_2655_, v_n_2656_);
    lean_dec(v_t_2655_);
    lean_dec_ref(v_cmp_2654_);
    return v_res_2657_;
}
pub unsafe fn l_Std_TreeSet_atIdx___redArg(
    mut v_t_2658_: *mut LeanObject,
    mut v_n_2659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    v___x_2660_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2658_, v_n_2659_);
    return v___x_2660_;
}
pub unsafe fn l_Std_TreeSet_atIdx___redArg___boxed(
    mut v_t_2661_: *mut LeanObject,
    mut v_n_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2663_: *mut LeanObject = core::ptr::null_mut();
    v_res_2663_ = l_Std_TreeSet_atIdx___redArg(v_t_2661_, v_n_2662_);
    lean_dec(v_t_2661_);
    return v_res_2663_;
}
pub unsafe fn l_Std_TreeSet_atIdx(
    mut v_00_u03b1_2664_: *mut LeanObject,
    mut v_cmp_2665_: *mut LeanObject,
    mut v_t_2666_: *mut LeanObject,
    mut v_n_2667_: *mut LeanObject,
    mut v_h_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    v___x_2669_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2666_, v_n_2667_);
    return v___x_2669_;
}
pub unsafe fn l_Std_TreeSet_atIdx___boxed(
    mut v_00_u03b1_2670_: *mut LeanObject,
    mut v_cmp_2671_: *mut LeanObject,
    mut v_t_2672_: *mut LeanObject,
    mut v_n_2673_: *mut LeanObject,
    mut v_h_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2675_: *mut LeanObject = core::ptr::null_mut();
    v_res_2675_ = l_Std_TreeSet_atIdx(
        v_00_u03b1_2670_,
        v_cmp_2671_,
        v_t_2672_,
        v_n_2673_,
        v_h_2674_,
    );
    lean_dec(v_t_2672_);
    lean_dec_ref(v_cmp_2671_);
    return v_res_2675_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21___redArg(
    mut v_inst_2676_: *mut LeanObject,
    mut v_t_2677_: *mut LeanObject,
    mut v_n_2678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    v___x_2679_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2676_, v_t_2677_, v_n_2678_);
    return v___x_2679_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21___redArg___boxed(
    mut v_inst_2680_: *mut LeanObject,
    mut v_t_2681_: *mut LeanObject,
    mut v_n_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2683_: *mut LeanObject = core::ptr::null_mut();
    v_res_2683_ = l_Std_TreeSet_atIdx_x21___redArg(v_inst_2680_, v_t_2681_, v_n_2682_);
    lean_dec(v_t_2681_);
    lean_dec(v_inst_2680_);
    return v_res_2683_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21(
    mut v_00_u03b1_2684_: *mut LeanObject,
    mut v_cmp_2685_: *mut LeanObject,
    mut v_inst_2686_: *mut LeanObject,
    mut v_t_2687_: *mut LeanObject,
    mut v_n_2688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    v___x_2689_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2686_, v_t_2687_, v_n_2688_);
    return v___x_2689_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21___boxed(
    mut v_00_u03b1_2690_: *mut LeanObject,
    mut v_cmp_2691_: *mut LeanObject,
    mut v_inst_2692_: *mut LeanObject,
    mut v_t_2693_: *mut LeanObject,
    mut v_n_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2695_: *mut LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_Std_TreeSet_atIdx_x21(
        v_00_u03b1_2690_,
        v_cmp_2691_,
        v_inst_2692_,
        v_t_2693_,
        v_n_2694_,
    );
    lean_dec(v_t_2693_);
    lean_dec(v_inst_2692_);
    lean_dec_ref(v_cmp_2691_);
    return v_res_2695_;
}
pub unsafe fn l_Std_TreeSet_atIdxD___redArg(
    mut v_t_2696_: *mut LeanObject,
    mut v_n_2697_: *mut LeanObject,
    mut v_fallback_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    v___x_2699_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2696_, v_n_2697_, v_fallback_2698_);
    return v___x_2699_;
}
pub unsafe fn l_Std_TreeSet_atIdxD___redArg___boxed(
    mut v_t_2700_: *mut LeanObject,
    mut v_n_2701_: *mut LeanObject,
    mut v_fallback_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2703_: *mut LeanObject = core::ptr::null_mut();
    v_res_2703_ = l_Std_TreeSet_atIdxD___redArg(v_t_2700_, v_n_2701_, v_fallback_2702_);
    lean_dec(v_fallback_2702_);
    lean_dec(v_t_2700_);
    return v_res_2703_;
}
pub unsafe fn l_Std_TreeSet_atIdxD(
    mut v_00_u03b1_2704_: *mut LeanObject,
    mut v_cmp_2705_: *mut LeanObject,
    mut v_t_2706_: *mut LeanObject,
    mut v_n_2707_: *mut LeanObject,
    mut v_fallback_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    v___x_2709_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2706_, v_n_2707_, v_fallback_2708_);
    return v___x_2709_;
}
pub unsafe fn l_Std_TreeSet_atIdxD___boxed(
    mut v_00_u03b1_2710_: *mut LeanObject,
    mut v_cmp_2711_: *mut LeanObject,
    mut v_t_2712_: *mut LeanObject,
    mut v_n_2713_: *mut LeanObject,
    mut v_fallback_2714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2715_: *mut LeanObject = core::ptr::null_mut();
    v_res_2715_ = l_Std_TreeSet_atIdxD(
        v_00_u03b1_2710_,
        v_cmp_2711_,
        v_t_2712_,
        v_n_2713_,
        v_fallback_2714_,
    );
    lean_dec(v_fallback_2714_);
    lean_dec(v_t_2712_);
    lean_dec_ref(v_cmp_2711_);
    return v_res_2715_;
}
pub unsafe fn l_Std_TreeSet_getGE_x3f___redArg(
    mut v_cmp_2716_: *mut LeanObject,
    mut v_t_2717_: *mut LeanObject,
    mut v_k_2718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    v___x_2719_ = lean_box(0);
    v___x_2720_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2716_,
        v_k_2718_,
        v___x_2719_,
        v_t_2717_,
    );
    return v___x_2720_;
}
pub unsafe fn l_Std_TreeSet_getGE_x3f(
    mut v_00_u03b1_2721_: *mut LeanObject,
    mut v_cmp_2722_: *mut LeanObject,
    mut v_t_2723_: *mut LeanObject,
    mut v_k_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    v___x_2725_ = lean_box(0);
    v___x_2726_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2722_,
        v_k_2724_,
        v___x_2725_,
        v_t_2723_,
    );
    return v___x_2726_;
}
pub unsafe fn l_Std_TreeSet_getGT_x3f___redArg(
    mut v_cmp_2727_: *mut LeanObject,
    mut v_t_2728_: *mut LeanObject,
    mut v_k_2729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ = lean_box(0);
    v___x_2731_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2727_,
        v_k_2729_,
        v___x_2730_,
        v_t_2728_,
    );
    return v___x_2731_;
}
pub unsafe fn l_Std_TreeSet_getGT_x3f(
    mut v_00_u03b1_2732_: *mut LeanObject,
    mut v_cmp_2733_: *mut LeanObject,
    mut v_t_2734_: *mut LeanObject,
    mut v_k_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    v___x_2736_ = lean_box(0);
    v___x_2737_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2733_,
        v_k_2735_,
        v___x_2736_,
        v_t_2734_,
    );
    return v___x_2737_;
}
pub unsafe fn l_Std_TreeSet_getLE_x3f___redArg(
    mut v_cmp_2738_: *mut LeanObject,
    mut v_t_2739_: *mut LeanObject,
    mut v_k_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    v___x_2741_ = lean_box(0);
    v___x_2742_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2738_,
        v_k_2740_,
        v___x_2741_,
        v_t_2739_,
    );
    return v___x_2742_;
}
pub unsafe fn l_Std_TreeSet_getLE_x3f(
    mut v_00_u03b1_2743_: *mut LeanObject,
    mut v_cmp_2744_: *mut LeanObject,
    mut v_t_2745_: *mut LeanObject,
    mut v_k_2746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    v___x_2747_ = lean_box(0);
    v___x_2748_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2744_,
        v_k_2746_,
        v___x_2747_,
        v_t_2745_,
    );
    return v___x_2748_;
}
pub unsafe fn l_Std_TreeSet_getLT_x3f___redArg(
    mut v_cmp_2749_: *mut LeanObject,
    mut v_t_2750_: *mut LeanObject,
    mut v_k_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    v___x_2752_ = lean_box(0);
    v___x_2753_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2749_,
        v_k_2751_,
        v___x_2752_,
        v_t_2750_,
    );
    return v___x_2753_;
}
pub unsafe fn l_Std_TreeSet_getLT_x3f(
    mut v_00_u03b1_2754_: *mut LeanObject,
    mut v_cmp_2755_: *mut LeanObject,
    mut v_t_2756_: *mut LeanObject,
    mut v_k_2757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    v___x_2758_ = lean_box(0);
    v___x_2759_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2755_,
        v_k_2757_,
        v___x_2758_,
        v_t_2756_,
    );
    return v___x_2759_;
}
pub unsafe fn _init_l_Std_TreeSet_getGE_x21___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    v___x_2763_ = l_Std_TreeSet_getGE_x21___redArg___closed__2;
    v___x_2764_ = lean_unsigned_to_nat(14);
    v___x_2765_ = lean_unsigned_to_nat(22);
    v___x_2766_ = l_Std_TreeSet_getGE_x21___redArg___closed__1;
    v___x_2767_ = l_Std_TreeSet_getGE_x21___redArg___closed__0;
    v___x_2768_ = l_mkPanicMessageWithDecl(
        v___x_2767_,
        v___x_2766_,
        v___x_2765_,
        v___x_2764_,
        v___x_2763_,
    );
    return v___x_2768_;
}
pub unsafe fn l_Std_TreeSet_getGE_x21___redArg(
    mut v_cmp_2769_: *mut LeanObject,
    mut v_inst_2770_: *mut LeanObject,
    mut v_t_2771_: *mut LeanObject,
    mut v_k_2772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    v___x_2773_ = lean_box(0);
    v___x_2774_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2769_,
        v_k_2772_,
        v___x_2773_,
        v_t_2771_,
    );
    if lean_obj_tag(v___x_2774_) == 0 {
        let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
        v___x_2775_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2776_ = l_panic___redArg(v_inst_2770_, v___x_2775_);
        return v___x_2776_;
    } else {
        let mut v_val_2777_: *mut LeanObject = core::ptr::null_mut();
        v_val_2777_ = lean_ctor_get(v___x_2774_, 0);
        lean_inc(v_val_2777_);
        lean_dec_ref_known(v___x_2774_, 1);
        return v_val_2777_;
    }
}
pub unsafe fn l_Std_TreeSet_getGE_x21___redArg___boxed(
    mut v_cmp_2778_: *mut LeanObject,
    mut v_inst_2779_: *mut LeanObject,
    mut v_t_2780_: *mut LeanObject,
    mut v_k_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2782_: *mut LeanObject = core::ptr::null_mut();
    v_res_2782_ = l_Std_TreeSet_getGE_x21___redArg(v_cmp_2778_, v_inst_2779_, v_t_2780_, v_k_2781_);
    lean_dec(v_inst_2779_);
    return v_res_2782_;
}
pub unsafe fn l_Std_TreeSet_getGE_x21(
    mut v_00_u03b1_2783_: *mut LeanObject,
    mut v_cmp_2784_: *mut LeanObject,
    mut v_inst_2785_: *mut LeanObject,
    mut v_t_2786_: *mut LeanObject,
    mut v_k_2787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    v___x_2788_ = lean_box(0);
    v___x_2789_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2784_,
        v_k_2787_,
        v___x_2788_,
        v_t_2786_,
    );
    if lean_obj_tag(v___x_2789_) == 0 {
        let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
        v___x_2790_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2791_ = l_panic___redArg(v_inst_2785_, v___x_2790_);
        return v___x_2791_;
    } else {
        let mut v_val_2792_: *mut LeanObject = core::ptr::null_mut();
        v_val_2792_ = lean_ctor_get(v___x_2789_, 0);
        lean_inc(v_val_2792_);
        lean_dec_ref_known(v___x_2789_, 1);
        return v_val_2792_;
    }
}
pub unsafe fn l_Std_TreeSet_getGE_x21___boxed(
    mut v_00_u03b1_2793_: *mut LeanObject,
    mut v_cmp_2794_: *mut LeanObject,
    mut v_inst_2795_: *mut LeanObject,
    mut v_t_2796_: *mut LeanObject,
    mut v_k_2797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2798_: *mut LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Std_TreeSet_getGE_x21(
        v_00_u03b1_2793_,
        v_cmp_2794_,
        v_inst_2795_,
        v_t_2796_,
        v_k_2797_,
    );
    lean_dec(v_inst_2795_);
    return v_res_2798_;
}
pub unsafe fn l_Std_TreeSet_getGT_x21___redArg(
    mut v_cmp_2799_: *mut LeanObject,
    mut v_inst_2800_: *mut LeanObject,
    mut v_t_2801_: *mut LeanObject,
    mut v_k_2802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    v___x_2803_ = lean_box(0);
    v___x_2804_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2799_,
        v_k_2802_,
        v___x_2803_,
        v_t_2801_,
    );
    if lean_obj_tag(v___x_2804_) == 0 {
        let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
        v___x_2805_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2806_ = l_panic___redArg(v_inst_2800_, v___x_2805_);
        return v___x_2806_;
    } else {
        let mut v_val_2807_: *mut LeanObject = core::ptr::null_mut();
        v_val_2807_ = lean_ctor_get(v___x_2804_, 0);
        lean_inc(v_val_2807_);
        lean_dec_ref_known(v___x_2804_, 1);
        return v_val_2807_;
    }
}
pub unsafe fn l_Std_TreeSet_getGT_x21___redArg___boxed(
    mut v_cmp_2808_: *mut LeanObject,
    mut v_inst_2809_: *mut LeanObject,
    mut v_t_2810_: *mut LeanObject,
    mut v_k_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2812_: *mut LeanObject = core::ptr::null_mut();
    v_res_2812_ = l_Std_TreeSet_getGT_x21___redArg(v_cmp_2808_, v_inst_2809_, v_t_2810_, v_k_2811_);
    lean_dec(v_inst_2809_);
    return v_res_2812_;
}
pub unsafe fn l_Std_TreeSet_getGT_x21(
    mut v_00_u03b1_2813_: *mut LeanObject,
    mut v_cmp_2814_: *mut LeanObject,
    mut v_inst_2815_: *mut LeanObject,
    mut v_t_2816_: *mut LeanObject,
    mut v_k_2817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    v___x_2818_ = lean_box(0);
    v___x_2819_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2814_,
        v_k_2817_,
        v___x_2818_,
        v_t_2816_,
    );
    if lean_obj_tag(v___x_2819_) == 0 {
        let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
        v___x_2820_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2821_ = l_panic___redArg(v_inst_2815_, v___x_2820_);
        return v___x_2821_;
    } else {
        let mut v_val_2822_: *mut LeanObject = core::ptr::null_mut();
        v_val_2822_ = lean_ctor_get(v___x_2819_, 0);
        lean_inc(v_val_2822_);
        lean_dec_ref_known(v___x_2819_, 1);
        return v_val_2822_;
    }
}
pub unsafe fn l_Std_TreeSet_getGT_x21___boxed(
    mut v_00_u03b1_2823_: *mut LeanObject,
    mut v_cmp_2824_: *mut LeanObject,
    mut v_inst_2825_: *mut LeanObject,
    mut v_t_2826_: *mut LeanObject,
    mut v_k_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2828_: *mut LeanObject = core::ptr::null_mut();
    v_res_2828_ = l_Std_TreeSet_getGT_x21(
        v_00_u03b1_2823_,
        v_cmp_2824_,
        v_inst_2825_,
        v_t_2826_,
        v_k_2827_,
    );
    lean_dec(v_inst_2825_);
    return v_res_2828_;
}
pub unsafe fn l_Std_TreeSet_getLE_x21___redArg(
    mut v_cmp_2829_: *mut LeanObject,
    mut v_inst_2830_: *mut LeanObject,
    mut v_t_2831_: *mut LeanObject,
    mut v_k_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    v___x_2833_ = lean_box(0);
    v___x_2834_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2829_,
        v_k_2832_,
        v___x_2833_,
        v_t_2831_,
    );
    if lean_obj_tag(v___x_2834_) == 0 {
        let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
        v___x_2835_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2836_ = l_panic___redArg(v_inst_2830_, v___x_2835_);
        return v___x_2836_;
    } else {
        let mut v_val_2837_: *mut LeanObject = core::ptr::null_mut();
        v_val_2837_ = lean_ctor_get(v___x_2834_, 0);
        lean_inc(v_val_2837_);
        lean_dec_ref_known(v___x_2834_, 1);
        return v_val_2837_;
    }
}
pub unsafe fn l_Std_TreeSet_getLE_x21___redArg___boxed(
    mut v_cmp_2838_: *mut LeanObject,
    mut v_inst_2839_: *mut LeanObject,
    mut v_t_2840_: *mut LeanObject,
    mut v_k_2841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2842_: *mut LeanObject = core::ptr::null_mut();
    v_res_2842_ = l_Std_TreeSet_getLE_x21___redArg(v_cmp_2838_, v_inst_2839_, v_t_2840_, v_k_2841_);
    lean_dec(v_inst_2839_);
    return v_res_2842_;
}
pub unsafe fn l_Std_TreeSet_getLE_x21(
    mut v_00_u03b1_2843_: *mut LeanObject,
    mut v_cmp_2844_: *mut LeanObject,
    mut v_inst_2845_: *mut LeanObject,
    mut v_t_2846_: *mut LeanObject,
    mut v_k_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    v___x_2848_ = lean_box(0);
    v___x_2849_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2844_,
        v_k_2847_,
        v___x_2848_,
        v_t_2846_,
    );
    if lean_obj_tag(v___x_2849_) == 0 {
        let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
        v___x_2850_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2851_ = l_panic___redArg(v_inst_2845_, v___x_2850_);
        return v___x_2851_;
    } else {
        let mut v_val_2852_: *mut LeanObject = core::ptr::null_mut();
        v_val_2852_ = lean_ctor_get(v___x_2849_, 0);
        lean_inc(v_val_2852_);
        lean_dec_ref_known(v___x_2849_, 1);
        return v_val_2852_;
    }
}
pub unsafe fn l_Std_TreeSet_getLE_x21___boxed(
    mut v_00_u03b1_2853_: *mut LeanObject,
    mut v_cmp_2854_: *mut LeanObject,
    mut v_inst_2855_: *mut LeanObject,
    mut v_t_2856_: *mut LeanObject,
    mut v_k_2857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2858_: *mut LeanObject = core::ptr::null_mut();
    v_res_2858_ = l_Std_TreeSet_getLE_x21(
        v_00_u03b1_2853_,
        v_cmp_2854_,
        v_inst_2855_,
        v_t_2856_,
        v_k_2857_,
    );
    lean_dec(v_inst_2855_);
    return v_res_2858_;
}
pub unsafe fn l_Std_TreeSet_getLT_x21___redArg(
    mut v_cmp_2859_: *mut LeanObject,
    mut v_inst_2860_: *mut LeanObject,
    mut v_t_2861_: *mut LeanObject,
    mut v_k_2862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    v___x_2863_ = lean_box(0);
    v___x_2864_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2859_,
        v_k_2862_,
        v___x_2863_,
        v_t_2861_,
    );
    if lean_obj_tag(v___x_2864_) == 0 {
        let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
        v___x_2865_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2866_ = l_panic___redArg(v_inst_2860_, v___x_2865_);
        return v___x_2866_;
    } else {
        let mut v_val_2867_: *mut LeanObject = core::ptr::null_mut();
        v_val_2867_ = lean_ctor_get(v___x_2864_, 0);
        lean_inc(v_val_2867_);
        lean_dec_ref_known(v___x_2864_, 1);
        return v_val_2867_;
    }
}
pub unsafe fn l_Std_TreeSet_getLT_x21___redArg___boxed(
    mut v_cmp_2868_: *mut LeanObject,
    mut v_inst_2869_: *mut LeanObject,
    mut v_t_2870_: *mut LeanObject,
    mut v_k_2871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2872_: *mut LeanObject = core::ptr::null_mut();
    v_res_2872_ = l_Std_TreeSet_getLT_x21___redArg(v_cmp_2868_, v_inst_2869_, v_t_2870_, v_k_2871_);
    lean_dec(v_inst_2869_);
    return v_res_2872_;
}
pub unsafe fn l_Std_TreeSet_getLT_x21(
    mut v_00_u03b1_2873_: *mut LeanObject,
    mut v_cmp_2874_: *mut LeanObject,
    mut v_inst_2875_: *mut LeanObject,
    mut v_t_2876_: *mut LeanObject,
    mut v_k_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    v___x_2878_ = lean_box(0);
    v___x_2879_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2874_,
        v_k_2877_,
        v___x_2878_,
        v_t_2876_,
    );
    if lean_obj_tag(v___x_2879_) == 0 {
        let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
        v___x_2880_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2881_ = l_panic___redArg(v_inst_2875_, v___x_2880_);
        return v___x_2881_;
    } else {
        let mut v_val_2882_: *mut LeanObject = core::ptr::null_mut();
        v_val_2882_ = lean_ctor_get(v___x_2879_, 0);
        lean_inc(v_val_2882_);
        lean_dec_ref_known(v___x_2879_, 1);
        return v_val_2882_;
    }
}
pub unsafe fn l_Std_TreeSet_getLT_x21___boxed(
    mut v_00_u03b1_2883_: *mut LeanObject,
    mut v_cmp_2884_: *mut LeanObject,
    mut v_inst_2885_: *mut LeanObject,
    mut v_t_2886_: *mut LeanObject,
    mut v_k_2887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2888_: *mut LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_Std_TreeSet_getLT_x21(
        v_00_u03b1_2883_,
        v_cmp_2884_,
        v_inst_2885_,
        v_t_2886_,
        v_k_2887_,
    );
    lean_dec(v_inst_2885_);
    return v_res_2888_;
}
pub unsafe fn l_Std_TreeSet_getGED___redArg(
    mut v_cmp_2889_: *mut LeanObject,
    mut v_t_2890_: *mut LeanObject,
    mut v_k_2891_: *mut LeanObject,
    mut v_fallback_2892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    v___x_2893_ = lean_box(0);
    v___x_2894_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2889_,
        v_k_2891_,
        v___x_2893_,
        v_t_2890_,
    );
    if lean_obj_tag(v___x_2894_) == 0 {
        lean_inc(v_fallback_2892_);
        return v_fallback_2892_;
    } else {
        let mut v_val_2895_: *mut LeanObject = core::ptr::null_mut();
        v_val_2895_ = lean_ctor_get(v___x_2894_, 0);
        lean_inc(v_val_2895_);
        lean_dec_ref_known(v___x_2894_, 1);
        return v_val_2895_;
    }
}
pub unsafe fn l_Std_TreeSet_getGED___redArg___boxed(
    mut v_cmp_2896_: *mut LeanObject,
    mut v_t_2897_: *mut LeanObject,
    mut v_k_2898_: *mut LeanObject,
    mut v_fallback_2899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2900_: *mut LeanObject = core::ptr::null_mut();
    v_res_2900_ =
        l_Std_TreeSet_getGED___redArg(v_cmp_2896_, v_t_2897_, v_k_2898_, v_fallback_2899_);
    lean_dec(v_fallback_2899_);
    return v_res_2900_;
}
pub unsafe fn l_Std_TreeSet_getGED(
    mut v_00_u03b1_2901_: *mut LeanObject,
    mut v_cmp_2902_: *mut LeanObject,
    mut v_t_2903_: *mut LeanObject,
    mut v_k_2904_: *mut LeanObject,
    mut v_fallback_2905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    v___x_2906_ = lean_box(0);
    v___x_2907_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2902_,
        v_k_2904_,
        v___x_2906_,
        v_t_2903_,
    );
    if lean_obj_tag(v___x_2907_) == 0 {
        lean_inc(v_fallback_2905_);
        return v_fallback_2905_;
    } else {
        let mut v_val_2908_: *mut LeanObject = core::ptr::null_mut();
        v_val_2908_ = lean_ctor_get(v___x_2907_, 0);
        lean_inc(v_val_2908_);
        lean_dec_ref_known(v___x_2907_, 1);
        return v_val_2908_;
    }
}
pub unsafe fn l_Std_TreeSet_getGED___boxed(
    mut v_00_u03b1_2909_: *mut LeanObject,
    mut v_cmp_2910_: *mut LeanObject,
    mut v_t_2911_: *mut LeanObject,
    mut v_k_2912_: *mut LeanObject,
    mut v_fallback_2913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2914_: *mut LeanObject = core::ptr::null_mut();
    v_res_2914_ = l_Std_TreeSet_getGED(
        v_00_u03b1_2909_,
        v_cmp_2910_,
        v_t_2911_,
        v_k_2912_,
        v_fallback_2913_,
    );
    lean_dec(v_fallback_2913_);
    return v_res_2914_;
}
pub unsafe fn l_Std_TreeSet_getGTD___redArg(
    mut v_cmp_2915_: *mut LeanObject,
    mut v_t_2916_: *mut LeanObject,
    mut v_k_2917_: *mut LeanObject,
    mut v_fallback_2918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    v___x_2919_ = lean_box(0);
    v___x_2920_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2915_,
        v_k_2917_,
        v___x_2919_,
        v_t_2916_,
    );
    if lean_obj_tag(v___x_2920_) == 0 {
        lean_inc(v_fallback_2918_);
        return v_fallback_2918_;
    } else {
        let mut v_val_2921_: *mut LeanObject = core::ptr::null_mut();
        v_val_2921_ = lean_ctor_get(v___x_2920_, 0);
        lean_inc(v_val_2921_);
        lean_dec_ref_known(v___x_2920_, 1);
        return v_val_2921_;
    }
}
pub unsafe fn l_Std_TreeSet_getGTD___redArg___boxed(
    mut v_cmp_2922_: *mut LeanObject,
    mut v_t_2923_: *mut LeanObject,
    mut v_k_2924_: *mut LeanObject,
    mut v_fallback_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2926_: *mut LeanObject = core::ptr::null_mut();
    v_res_2926_ =
        l_Std_TreeSet_getGTD___redArg(v_cmp_2922_, v_t_2923_, v_k_2924_, v_fallback_2925_);
    lean_dec(v_fallback_2925_);
    return v_res_2926_;
}
pub unsafe fn l_Std_TreeSet_getGTD(
    mut v_00_u03b1_2927_: *mut LeanObject,
    mut v_cmp_2928_: *mut LeanObject,
    mut v_t_2929_: *mut LeanObject,
    mut v_k_2930_: *mut LeanObject,
    mut v_fallback_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    v___x_2932_ = lean_box(0);
    v___x_2933_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2928_,
        v_k_2930_,
        v___x_2932_,
        v_t_2929_,
    );
    if lean_obj_tag(v___x_2933_) == 0 {
        lean_inc(v_fallback_2931_);
        return v_fallback_2931_;
    } else {
        let mut v_val_2934_: *mut LeanObject = core::ptr::null_mut();
        v_val_2934_ = lean_ctor_get(v___x_2933_, 0);
        lean_inc(v_val_2934_);
        lean_dec_ref_known(v___x_2933_, 1);
        return v_val_2934_;
    }
}
pub unsafe fn l_Std_TreeSet_getGTD___boxed(
    mut v_00_u03b1_2935_: *mut LeanObject,
    mut v_cmp_2936_: *mut LeanObject,
    mut v_t_2937_: *mut LeanObject,
    mut v_k_2938_: *mut LeanObject,
    mut v_fallback_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2940_: *mut LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Std_TreeSet_getGTD(
        v_00_u03b1_2935_,
        v_cmp_2936_,
        v_t_2937_,
        v_k_2938_,
        v_fallback_2939_,
    );
    lean_dec(v_fallback_2939_);
    return v_res_2940_;
}
pub unsafe fn l_Std_TreeSet_getLED___redArg(
    mut v_cmp_2941_: *mut LeanObject,
    mut v_t_2942_: *mut LeanObject,
    mut v_k_2943_: *mut LeanObject,
    mut v_fallback_2944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    v___x_2945_ = lean_box(0);
    v___x_2946_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2941_,
        v_k_2943_,
        v___x_2945_,
        v_t_2942_,
    );
    if lean_obj_tag(v___x_2946_) == 0 {
        lean_inc(v_fallback_2944_);
        return v_fallback_2944_;
    } else {
        let mut v_val_2947_: *mut LeanObject = core::ptr::null_mut();
        v_val_2947_ = lean_ctor_get(v___x_2946_, 0);
        lean_inc(v_val_2947_);
        lean_dec_ref_known(v___x_2946_, 1);
        return v_val_2947_;
    }
}
pub unsafe fn l_Std_TreeSet_getLED___redArg___boxed(
    mut v_cmp_2948_: *mut LeanObject,
    mut v_t_2949_: *mut LeanObject,
    mut v_k_2950_: *mut LeanObject,
    mut v_fallback_2951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2952_: *mut LeanObject = core::ptr::null_mut();
    v_res_2952_ =
        l_Std_TreeSet_getLED___redArg(v_cmp_2948_, v_t_2949_, v_k_2950_, v_fallback_2951_);
    lean_dec(v_fallback_2951_);
    return v_res_2952_;
}
pub unsafe fn l_Std_TreeSet_getLED(
    mut v_00_u03b1_2953_: *mut LeanObject,
    mut v_cmp_2954_: *mut LeanObject,
    mut v_t_2955_: *mut LeanObject,
    mut v_k_2956_: *mut LeanObject,
    mut v_fallback_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    v___x_2958_ = lean_box(0);
    v___x_2959_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2954_,
        v_k_2956_,
        v___x_2958_,
        v_t_2955_,
    );
    if lean_obj_tag(v___x_2959_) == 0 {
        lean_inc(v_fallback_2957_);
        return v_fallback_2957_;
    } else {
        let mut v_val_2960_: *mut LeanObject = core::ptr::null_mut();
        v_val_2960_ = lean_ctor_get(v___x_2959_, 0);
        lean_inc(v_val_2960_);
        lean_dec_ref_known(v___x_2959_, 1);
        return v_val_2960_;
    }
}
pub unsafe fn l_Std_TreeSet_getLED___boxed(
    mut v_00_u03b1_2961_: *mut LeanObject,
    mut v_cmp_2962_: *mut LeanObject,
    mut v_t_2963_: *mut LeanObject,
    mut v_k_2964_: *mut LeanObject,
    mut v_fallback_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2966_: *mut LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Std_TreeSet_getLED(
        v_00_u03b1_2961_,
        v_cmp_2962_,
        v_t_2963_,
        v_k_2964_,
        v_fallback_2965_,
    );
    lean_dec(v_fallback_2965_);
    return v_res_2966_;
}
pub unsafe fn l_Std_TreeSet_getLTD___redArg(
    mut v_cmp_2967_: *mut LeanObject,
    mut v_t_2968_: *mut LeanObject,
    mut v_k_2969_: *mut LeanObject,
    mut v_fallback_2970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    v___x_2971_ = lean_box(0);
    v___x_2972_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2967_,
        v_k_2969_,
        v___x_2971_,
        v_t_2968_,
    );
    if lean_obj_tag(v___x_2972_) == 0 {
        lean_inc(v_fallback_2970_);
        return v_fallback_2970_;
    } else {
        let mut v_val_2973_: *mut LeanObject = core::ptr::null_mut();
        v_val_2973_ = lean_ctor_get(v___x_2972_, 0);
        lean_inc(v_val_2973_);
        lean_dec_ref_known(v___x_2972_, 1);
        return v_val_2973_;
    }
}
pub unsafe fn l_Std_TreeSet_getLTD___redArg___boxed(
    mut v_cmp_2974_: *mut LeanObject,
    mut v_t_2975_: *mut LeanObject,
    mut v_k_2976_: *mut LeanObject,
    mut v_fallback_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2978_: *mut LeanObject = core::ptr::null_mut();
    v_res_2978_ =
        l_Std_TreeSet_getLTD___redArg(v_cmp_2974_, v_t_2975_, v_k_2976_, v_fallback_2977_);
    lean_dec(v_fallback_2977_);
    return v_res_2978_;
}
pub unsafe fn l_Std_TreeSet_getLTD(
    mut v_00_u03b1_2979_: *mut LeanObject,
    mut v_cmp_2980_: *mut LeanObject,
    mut v_t_2981_: *mut LeanObject,
    mut v_k_2982_: *mut LeanObject,
    mut v_fallback_2983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    v___x_2984_ = lean_box(0);
    v___x_2985_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2980_,
        v_k_2982_,
        v___x_2984_,
        v_t_2981_,
    );
    if lean_obj_tag(v___x_2985_) == 0 {
        lean_inc(v_fallback_2983_);
        return v_fallback_2983_;
    } else {
        let mut v_val_2986_: *mut LeanObject = core::ptr::null_mut();
        v_val_2986_ = lean_ctor_get(v___x_2985_, 0);
        lean_inc(v_val_2986_);
        lean_dec_ref_known(v___x_2985_, 1);
        return v_val_2986_;
    }
}
pub unsafe fn l_Std_TreeSet_getLTD___boxed(
    mut v_00_u03b1_2987_: *mut LeanObject,
    mut v_cmp_2988_: *mut LeanObject,
    mut v_t_2989_: *mut LeanObject,
    mut v_k_2990_: *mut LeanObject,
    mut v_fallback_2991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2992_: *mut LeanObject = core::ptr::null_mut();
    v_res_2992_ = l_Std_TreeSet_getLTD(
        v_00_u03b1_2987_,
        v_cmp_2988_,
        v_t_2989_,
        v_k_2990_,
        v_fallback_2991_,
    );
    lean_dec(v_fallback_2991_);
    return v_res_2992_;
}
pub unsafe fn l_Std_TreeSet_filter___redArg___lam__0(
    mut v_f_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_x_2995_: *mut LeanObject,
) -> u8 {
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    v___x_2996_ = lean_apply_1(v_f_2993_, v_a_2994_);
    v___x_2997_ = (lean_unbox(v___x_2996_) as u8);
    return v___x_2997_;
}
pub unsafe fn l_Std_TreeSet_filter___redArg___lam__0___boxed(
    mut v_f_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
    mut v_x_3000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3001_: u8 = 0;
    let mut v_r_3002_: *mut LeanObject = core::ptr::null_mut();
    v_res_3001_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_2998_, v_a_2999_, v_x_3000_);
    v_r_3002_ = lean_box((v_res_3001_) as usize);
    return v_r_3002_;
}
pub unsafe fn l_Std_TreeSet_filter___redArg(
    mut v_f_3003_: *mut LeanObject,
    mut v_m_3004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    v___f_3005_ = lean_alloc_closure(
        l_Std_TreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3005_, 0, v_f_3003_);
    v___x_3006_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_3005_, v_m_3004_);
    return v___x_3006_;
}
pub unsafe fn l_Std_TreeSet_filter(
    mut v_00_u03b1_3007_: *mut LeanObject,
    mut v_cmp_3008_: *mut LeanObject,
    mut v_f_3009_: *mut LeanObject,
    mut v_m_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    v___f_3011_ = lean_alloc_closure(
        l_Std_TreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3011_, 0, v_f_3009_);
    v___x_3012_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_3011_, v_m_3010_);
    return v___x_3012_;
}
pub unsafe fn l_Std_TreeSet_filter___boxed(
    mut v_00_u03b1_3013_: *mut LeanObject,
    mut v_cmp_3014_: *mut LeanObject,
    mut v_f_3015_: *mut LeanObject,
    mut v_m_3016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3017_: *mut LeanObject = core::ptr::null_mut();
    v_res_3017_ = l_Std_TreeSet_filter(v_00_u03b1_3013_, v_cmp_3014_, v_f_3015_, v_m_3016_);
    lean_dec_ref(v_cmp_3014_);
    return v_res_3017_;
}
pub unsafe fn l_Std_TreeSet_foldlM___redArg___lam__0(
    mut v_f_3018_: *mut LeanObject,
    mut v_c_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
    mut v_x_3021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    v___x_3022_ = lean_apply_2(v_f_3018_, v_c_3019_, v_a_3020_);
    return v___x_3022_;
}
pub unsafe fn l_Std_TreeSet_foldlM___redArg(
    mut v_inst_3023_: *mut LeanObject,
    mut v_f_3024_: *mut LeanObject,
    mut v_init_3025_: *mut LeanObject,
    mut v_t_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    v___f_3027_ = lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3027_, 0, v_f_3024_);
    v___x_3028_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3023_,
        v___f_3027_,
        v_init_3025_,
        v_t_3026_,
    );
    return v___x_3028_;
}
pub unsafe fn l_Std_TreeSet_foldlM(
    mut v_00_u03b1_3029_: *mut LeanObject,
    mut v_cmp_3030_: *mut LeanObject,
    mut v_m_3031_: *mut LeanObject,
    mut v_00_u03b4_3032_: *mut LeanObject,
    mut v_inst_3033_: *mut LeanObject,
    mut v_f_3034_: *mut LeanObject,
    mut v_init_3035_: *mut LeanObject,
    mut v_t_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    v___f_3037_ = lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3037_, 0, v_f_3034_);
    v___x_3038_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3033_,
        v___f_3037_,
        v_init_3035_,
        v_t_3036_,
    );
    return v___x_3038_;
}
pub unsafe fn l_Std_TreeSet_foldlM___boxed(
    mut v_00_u03b1_3039_: *mut LeanObject,
    mut v_cmp_3040_: *mut LeanObject,
    mut v_m_3041_: *mut LeanObject,
    mut v_00_u03b4_3042_: *mut LeanObject,
    mut v_inst_3043_: *mut LeanObject,
    mut v_f_3044_: *mut LeanObject,
    mut v_init_3045_: *mut LeanObject,
    mut v_t_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3047_: *mut LeanObject = core::ptr::null_mut();
    v_res_3047_ = l_Std_TreeSet_foldlM(
        v_00_u03b1_3039_,
        v_cmp_3040_,
        v_m_3041_,
        v_00_u03b4_3042_,
        v_inst_3043_,
        v_f_3044_,
        v_init_3045_,
        v_t_3046_,
    );
    lean_dec_ref(v_cmp_3040_);
    return v_res_3047_;
}
pub unsafe fn l_Std_TreeSet_foldl___redArg(
    mut v_f_3048_: *mut LeanObject,
    mut v_init_3049_: *mut LeanObject,
    mut v_t_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    v___f_3051_ = lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3051_, 0, v_f_3048_);
    v___x_3052_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3051_, v_init_3049_, v_t_3050_);
    return v___x_3052_;
}
pub unsafe fn l_Std_TreeSet_foldl(
    mut v_00_u03b1_3053_: *mut LeanObject,
    mut v_cmp_3054_: *mut LeanObject,
    mut v_00_u03b4_3055_: *mut LeanObject,
    mut v_f_3056_: *mut LeanObject,
    mut v_init_3057_: *mut LeanObject,
    mut v_t_3058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    v___f_3059_ = lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3059_, 0, v_f_3056_);
    v___x_3060_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3059_, v_init_3057_, v_t_3058_);
    return v___x_3060_;
}
pub unsafe fn l_Std_TreeSet_foldl___boxed(
    mut v_00_u03b1_3061_: *mut LeanObject,
    mut v_cmp_3062_: *mut LeanObject,
    mut v_00_u03b4_3063_: *mut LeanObject,
    mut v_f_3064_: *mut LeanObject,
    mut v_init_3065_: *mut LeanObject,
    mut v_t_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3067_: *mut LeanObject = core::ptr::null_mut();
    v_res_3067_ = l_Std_TreeSet_foldl(
        v_00_u03b1_3061_,
        v_cmp_3062_,
        v_00_u03b4_3063_,
        v_f_3064_,
        v_init_3065_,
        v_t_3066_,
    );
    lean_dec_ref(v_cmp_3062_);
    return v_res_3067_;
}
pub unsafe fn l_Std_TreeSet_foldrM___redArg___lam__0(
    mut v_f_3068_: *mut LeanObject,
    mut v_a_3069_: *mut LeanObject,
    mut v_x_3070_: *mut LeanObject,
    mut v_acc_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    v___x_3072_ = lean_apply_2(v_f_3068_, v_a_3069_, v_acc_3071_);
    return v___x_3072_;
}
pub unsafe fn l_Std_TreeSet_foldrM___redArg(
    mut v_inst_3073_: *mut LeanObject,
    mut v_f_3074_: *mut LeanObject,
    mut v_init_3075_: *mut LeanObject,
    mut v_t_3076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    v___f_3077_ = lean_alloc_closure(
        l_Std_TreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3077_, 0, v_f_3074_);
    v___x_3078_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_3073_,
        v___f_3077_,
        v_init_3075_,
        v_t_3076_,
    );
    return v___x_3078_;
}
pub unsafe fn l_Std_TreeSet_foldrM(
    mut v_00_u03b1_3079_: *mut LeanObject,
    mut v_cmp_3080_: *mut LeanObject,
    mut v_m_3081_: *mut LeanObject,
    mut v_00_u03b4_3082_: *mut LeanObject,
    mut v_inst_3083_: *mut LeanObject,
    mut v_f_3084_: *mut LeanObject,
    mut v_init_3085_: *mut LeanObject,
    mut v_t_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    v___f_3087_ = lean_alloc_closure(
        l_Std_TreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3087_, 0, v_f_3084_);
    v___x_3088_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_3083_,
        v___f_3087_,
        v_init_3085_,
        v_t_3086_,
    );
    return v___x_3088_;
}
pub unsafe fn l_Std_TreeSet_foldrM___boxed(
    mut v_00_u03b1_3089_: *mut LeanObject,
    mut v_cmp_3090_: *mut LeanObject,
    mut v_m_3091_: *mut LeanObject,
    mut v_00_u03b4_3092_: *mut LeanObject,
    mut v_inst_3093_: *mut LeanObject,
    mut v_f_3094_: *mut LeanObject,
    mut v_init_3095_: *mut LeanObject,
    mut v_t_3096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3097_: *mut LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Std_TreeSet_foldrM(
        v_00_u03b1_3089_,
        v_cmp_3090_,
        v_m_3091_,
        v_00_u03b4_3092_,
        v_inst_3093_,
        v_f_3094_,
        v_init_3095_,
        v_t_3096_,
    );
    lean_dec_ref(v_cmp_3090_);
    return v_res_3097_;
}
pub unsafe fn l_Std_TreeSet_foldr___redArg___lam__0(
    mut v_f_3098_: *mut LeanObject,
    mut v_x1_3099_: *mut LeanObject,
    mut v_x2_3100_: *mut LeanObject,
    mut v_x3_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    v___x_3102_ = lean_apply_2(v_f_3098_, v_x1_3099_, v_x3_3101_);
    return v___x_3102_;
}
pub unsafe fn l_Std_TreeSet_foldr___redArg(
    mut v_f_3122_: *mut LeanObject,
    mut v_init_3123_: *mut LeanObject,
    mut v_t_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    v___f_3125_ = lean_alloc_closure(
        l_Std_TreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3125_, 0, v_f_3122_);
    v___x_3126_ = l_Std_TreeSet_foldr___redArg___closed__9;
    v___x_3127_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3126_,
        v___f_3125_,
        v_init_3123_,
        v_t_3124_,
    );
    return v___x_3127_;
}
pub unsafe fn l_Std_TreeSet_foldr(
    mut v_00_u03b1_3128_: *mut LeanObject,
    mut v_cmp_3129_: *mut LeanObject,
    mut v_00_u03b4_3130_: *mut LeanObject,
    mut v_f_3131_: *mut LeanObject,
    mut v_init_3132_: *mut LeanObject,
    mut v_t_3133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    v___f_3134_ = lean_alloc_closure(
        l_Std_TreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3134_, 0, v_f_3131_);
    v___x_3135_ = l_Std_TreeSet_foldr___redArg___closed__9;
    v___x_3136_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3135_,
        v___f_3134_,
        v_init_3132_,
        v_t_3133_,
    );
    return v___x_3136_;
}
pub unsafe fn l_Std_TreeSet_foldr___boxed(
    mut v_00_u03b1_3137_: *mut LeanObject,
    mut v_cmp_3138_: *mut LeanObject,
    mut v_00_u03b4_3139_: *mut LeanObject,
    mut v_f_3140_: *mut LeanObject,
    mut v_init_3141_: *mut LeanObject,
    mut v_t_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3143_: *mut LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Std_TreeSet_foldr(
        v_00_u03b1_3137_,
        v_cmp_3138_,
        v_00_u03b4_3139_,
        v_f_3140_,
        v_init_3141_,
        v_t_3142_,
    );
    lean_dec_ref(v_cmp_3138_);
    return v_res_3143_;
}
pub unsafe fn l_Std_TreeSet_partition___redArg___lam__0(
    mut v_f_3144_: *mut LeanObject,
    mut v_cmp_3145_: *mut LeanObject,
    mut v_x_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_b_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: u8 = 0;
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3149_ = lean_ctor_get(v_x_3146_, 0);
                v_snd_3150_ = lean_ctor_get(v_x_3146_, 1);
                v_isSharedCheck_3164_ = (!lean_is_exclusive(v_x_3146_)) as u8;
                if v_isSharedCheck_3164_ == 0 {
                    v___x_3152_ = v_x_3146_;
                    v_isShared_3153_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3150_);
                    lean_inc(v_fst_3149_);
                    lean_dec(v_x_3146_);
                    v___x_3152_ = lean_box(0);
                    v_isShared_3153_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_3147_);
                v___x_3154_ = lean_apply_1(v_f_3144_, v_a_3147_);
                v___x_3155_ = (lean_unbox(v___x_3154_) as u8);
                if v___x_3155_ == 0 {
                    v___x_3156_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_3145_,
                        v_a_3147_,
                        v_b_3148_,
                        v_snd_3150_,
                    );
                    if v_isShared_3153_ == 0 {
                        lean_ctor_set(v___x_3152_, 1, v___x_3156_);
                        v___x_3158_ = v___x_3152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_fst_3149_);
                        lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3156_);
                        v___x_3158_ = v_reuseFailAlloc_3159_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3160_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_3145_,
                        v_a_3147_,
                        v_b_3148_,
                        v_fst_3149_,
                    );
                    if v_isShared_3153_ == 0 {
                        lean_ctor_set(v___x_3152_, 0, v___x_3160_);
                        v___x_3162_ = v___x_3152_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
                        lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_snd_3150_);
                        v___x_3162_ = v_reuseFailAlloc_3163_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3158_;
            }
            3 => {
                return v___x_3162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_partition___redArg(
    mut v_cmp_3167_: *mut LeanObject,
    mut v_f_3168_: *mut LeanObject,
    mut v_t_3169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3170_ = lean_alloc_closure(
                    l_Std_TreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_3170_, 0, v_f_3168_);
                lean_closure_set(v___f_3170_, 1, v_cmp_3167_);
                v___x_3171_ = l_Std_TreeSet_partition___redArg___closed__0;
                v_p_3172_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3170_,
                    v___x_3171_,
                    v_t_3169_,
                );
                v_fst_3173_ = lean_ctor_get(v_p_3172_, 0);
                v_snd_3174_ = lean_ctor_get(v_p_3172_, 1);
                v_isSharedCheck_3181_ = (!lean_is_exclusive(v_p_3172_)) as u8;
                if v_isSharedCheck_3181_ == 0 {
                    v___x_3176_ = v_p_3172_;
                    v_isShared_3177_ = v_isSharedCheck_3181_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3174_);
                    lean_inc(v_fst_3173_);
                    lean_dec(v_p_3172_);
                    v___x_3176_ = lean_box(0);
                    v_isShared_3177_ = v_isSharedCheck_3181_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3177_ == 0 {
                    v___x_3179_ = v___x_3176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_fst_3173_);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_snd_3174_);
                    v___x_3179_ = v_reuseFailAlloc_3180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_partition(
    mut v_00_u03b1_3182_: *mut LeanObject,
    mut v_cmp_3183_: *mut LeanObject,
    mut v_f_3184_: *mut LeanObject,
    mut v_t_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3186_ = lean_alloc_closure(
                    l_Std_TreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_3186_, 0, v_f_3184_);
                lean_closure_set(v___f_3186_, 1, v_cmp_3183_);
                v___x_3187_ = l_Std_TreeSet_partition___redArg___closed__0;
                v_p_3188_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3186_,
                    v___x_3187_,
                    v_t_3185_,
                );
                v_fst_3189_ = lean_ctor_get(v_p_3188_, 0);
                v_snd_3190_ = lean_ctor_get(v_p_3188_, 1);
                v_isSharedCheck_3197_ = (!lean_is_exclusive(v_p_3188_)) as u8;
                if v_isSharedCheck_3197_ == 0 {
                    v___x_3192_ = v_p_3188_;
                    v_isShared_3193_ = v_isSharedCheck_3197_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3190_);
                    lean_inc(v_fst_3189_);
                    lean_dec(v_p_3188_);
                    v___x_3192_ = lean_box(0);
                    v_isShared_3193_ = v_isSharedCheck_3197_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3193_ == 0 {
                    v___x_3195_ = v___x_3192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_fst_3189_);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_snd_3190_);
                    v___x_3195_ = v_reuseFailAlloc_3196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_forM___redArg___lam__0(
    mut v_f_3198_: *mut LeanObject,
    mut v_x_3199_: *mut LeanObject,
    mut v_k_3200_: *mut LeanObject,
    mut v_v_3201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    v___x_3202_ = lean_apply_1(v_f_3198_, v_k_3200_);
    return v___x_3202_;
}
pub unsafe fn l_Std_TreeSet_forM___redArg(
    mut v_inst_3203_: *mut LeanObject,
    mut v_f_3204_: *mut LeanObject,
    mut v_t_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    v___f_3206_ = lean_alloc_closure(
        l_Std_TreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3206_, 0, v_f_3204_);
    v___x_3207_ = lean_box(0);
    v___x_3208_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3203_,
        v___f_3206_,
        v___x_3207_,
        v_t_3205_,
    );
    return v___x_3208_;
}
pub unsafe fn l_Std_TreeSet_forM(
    mut v_00_u03b1_3209_: *mut LeanObject,
    mut v_cmp_3210_: *mut LeanObject,
    mut v_m_3211_: *mut LeanObject,
    mut v_inst_3212_: *mut LeanObject,
    mut v_f_3213_: *mut LeanObject,
    mut v_t_3214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    v___f_3215_ = lean_alloc_closure(
        l_Std_TreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3215_, 0, v_f_3213_);
    v___x_3216_ = lean_box(0);
    v___x_3217_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3212_,
        v___f_3215_,
        v___x_3216_,
        v_t_3214_,
    );
    return v___x_3217_;
}
pub unsafe fn l_Std_TreeSet_forM___boxed(
    mut v_00_u03b1_3218_: *mut LeanObject,
    mut v_cmp_3219_: *mut LeanObject,
    mut v_m_3220_: *mut LeanObject,
    mut v_inst_3221_: *mut LeanObject,
    mut v_f_3222_: *mut LeanObject,
    mut v_t_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3224_: *mut LeanObject = core::ptr::null_mut();
    v_res_3224_ = l_Std_TreeSet_forM(
        v_00_u03b1_3218_,
        v_cmp_3219_,
        v_m_3220_,
        v_inst_3221_,
        v_f_3222_,
        v_t_3223_,
    );
    lean_dec_ref(v_cmp_3219_);
    return v_res_3224_;
}
pub unsafe fn l_Std_TreeSet_forIn___redArg___lam__0(
    mut v_f_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_b_3227_: *mut LeanObject,
    mut v_c_3228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    v___x_3229_ = lean_apply_2(v_f_3225_, v_a_3226_, v_c_3228_);
    return v___x_3229_;
}
pub unsafe fn l_Std_TreeSet_forIn___redArg___lam__1(
    mut v_toPure_3230_: *mut LeanObject,
    mut v_____do__lift_3231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    v_a_3232_ = lean_ctor_get(v_____do__lift_3231_, 0);
    lean_inc(v_a_3232_);
    lean_dec_ref(v_____do__lift_3231_);
    v___x_3233_ = lean_apply_2(v_toPure_3230_, lean_box(0), v_a_3232_);
    return v___x_3233_;
}
pub unsafe fn l_Std_TreeSet_forIn___redArg(
    mut v_inst_3234_: *mut LeanObject,
    mut v_f_3235_: *mut LeanObject,
    mut v_init_3236_: *mut LeanObject,
    mut v_t_3237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3238_ = lean_ctor_get(v_inst_3234_, 0);
    v_toBind_3239_ = lean_ctor_get(v_inst_3234_, 1);
    lean_inc(v_toBind_3239_);
    v_toPure_3240_ = lean_ctor_get(v_toApplicative_3238_, 1);
    lean_inc(v_toPure_3240_);
    v___f_3241_ = lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3241_, 0, v_f_3235_);
    v___x_3242_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3234_,
        v___f_3241_,
        v_init_3236_,
        v_t_3237_,
    );
    v___f_3243_ = lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3243_, 0, v_toPure_3240_);
    v___x_3244_ = lean_apply_4(
        v_toBind_3239_,
        lean_box(0),
        lean_box(0),
        v___x_3242_,
        v___f_3243_,
    );
    return v___x_3244_;
}
pub unsafe fn l_Std_TreeSet_forIn(
    mut v_00_u03b1_3245_: *mut LeanObject,
    mut v_cmp_3246_: *mut LeanObject,
    mut v_00_u03b4_3247_: *mut LeanObject,
    mut v_m_3248_: *mut LeanObject,
    mut v_inst_3249_: *mut LeanObject,
    mut v_f_3250_: *mut LeanObject,
    mut v_init_3251_: *mut LeanObject,
    mut v_t_3252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3253_ = lean_ctor_get(v_inst_3249_, 0);
    v_toBind_3254_ = lean_ctor_get(v_inst_3249_, 1);
    lean_inc(v_toBind_3254_);
    v_toPure_3255_ = lean_ctor_get(v_toApplicative_3253_, 1);
    lean_inc(v_toPure_3255_);
    v___f_3256_ = lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3256_, 0, v_f_3250_);
    v___x_3257_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3249_,
        v___f_3256_,
        v_init_3251_,
        v_t_3252_,
    );
    v___f_3258_ = lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3258_, 0, v_toPure_3255_);
    v___x_3259_ = lean_apply_4(
        v_toBind_3254_,
        lean_box(0),
        lean_box(0),
        v___x_3257_,
        v___f_3258_,
    );
    return v___x_3259_;
}
pub unsafe fn l_Std_TreeSet_forIn___boxed(
    mut v_00_u03b1_3260_: *mut LeanObject,
    mut v_cmp_3261_: *mut LeanObject,
    mut v_00_u03b4_3262_: *mut LeanObject,
    mut v_m_3263_: *mut LeanObject,
    mut v_inst_3264_: *mut LeanObject,
    mut v_f_3265_: *mut LeanObject,
    mut v_init_3266_: *mut LeanObject,
    mut v_t_3267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3268_: *mut LeanObject = core::ptr::null_mut();
    v_res_3268_ = l_Std_TreeSet_forIn(
        v_00_u03b1_3260_,
        v_cmp_3261_,
        v_00_u03b4_3262_,
        v_m_3263_,
        v_inst_3264_,
        v_f_3265_,
        v_init_3266_,
        v_t_3267_,
    );
    lean_dec_ref(v_cmp_3261_);
    return v_res_3268_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad___redArg___lam__1(
    mut v_inst_3269_: *mut LeanObject,
    mut v_t_3270_: *mut LeanObject,
    mut v_f_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    v___f_3272_ = lean_alloc_closure(
        l_Std_TreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3272_, 0, v_f_3271_);
    v___x_3273_ = lean_box(0);
    v___x_3274_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3269_,
        v___f_3272_,
        v___x_3273_,
        v_t_3270_,
    );
    return v___x_3274_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad___redArg(
    mut v_inst_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3276_: *mut LeanObject = core::ptr::null_mut();
    v___f_3276_ = lean_alloc_closure(
        l_Std_TreeSet_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3276_, 0, v_inst_3275_);
    return v___f_3276_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad(
    mut v_00_u03b1_3277_: *mut LeanObject,
    mut v_cmp_3278_: *mut LeanObject,
    mut v_m_3279_: *mut LeanObject,
    mut v_inst_3280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3281_: *mut LeanObject = core::ptr::null_mut();
    v___f_3281_ = lean_alloc_closure(
        l_Std_TreeSet_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3281_, 0, v_inst_3280_);
    return v___f_3281_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad___boxed(
    mut v_00_u03b1_3282_: *mut LeanObject,
    mut v_cmp_3283_: *mut LeanObject,
    mut v_m_3284_: *mut LeanObject,
    mut v_inst_3285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3286_: *mut LeanObject = core::ptr::null_mut();
    v_res_3286_ =
        l_Std_TreeSet_instForMOfMonad(v_00_u03b1_3282_, v_cmp_3283_, v_m_3284_, v_inst_3285_);
    lean_dec_ref(v_cmp_3283_);
    return v_res_3286_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad___redArg___lam__2(
    mut v_inst_3287_: *mut LeanObject,
    mut v_00_u03b2_3288_: *mut LeanObject,
    mut v_m_3289_: *mut LeanObject,
    mut v_init_3290_: *mut LeanObject,
    mut v_f_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3292_ = lean_ctor_get(v_inst_3287_, 0);
    v_toBind_3293_ = lean_ctor_get(v_inst_3287_, 1);
    lean_inc(v_toBind_3293_);
    v_toPure_3294_ = lean_ctor_get(v_toApplicative_3292_, 1);
    lean_inc(v_toPure_3294_);
    v___f_3295_ = lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3295_, 0, v_f_3291_);
    v___x_3296_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3287_,
        v___f_3295_,
        v_init_3290_,
        v_m_3289_,
    );
    v___f_3297_ = lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3297_, 0, v_toPure_3294_);
    v___x_3298_ = lean_apply_4(
        v_toBind_3293_,
        lean_box(0),
        lean_box(0),
        v___x_3296_,
        v___f_3297_,
    );
    return v___x_3298_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad___redArg(
    mut v_inst_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3300_: *mut LeanObject = core::ptr::null_mut();
    v___f_3300_ = lean_alloc_closure(
        l_Std_TreeSet_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3300_, 0, v_inst_3299_);
    return v___f_3300_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad(
    mut v_00_u03b1_3301_: *mut LeanObject,
    mut v_cmp_3302_: *mut LeanObject,
    mut v_m_3303_: *mut LeanObject,
    mut v_inst_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3305_: *mut LeanObject = core::ptr::null_mut();
    v___f_3305_ = lean_alloc_closure(
        l_Std_TreeSet_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3305_, 0, v_inst_3304_);
    return v___f_3305_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad___boxed(
    mut v_00_u03b1_3306_: *mut LeanObject,
    mut v_cmp_3307_: *mut LeanObject,
    mut v_m_3308_: *mut LeanObject,
    mut v_inst_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3310_: *mut LeanObject = core::ptr::null_mut();
    v_res_3310_ =
        l_Std_TreeSet_instForInOfMonad(v_00_u03b1_3306_, v_cmp_3307_, v_m_3308_, v_inst_3309_);
    lean_dec_ref(v_cmp_3307_);
    return v_res_3310_;
}
pub unsafe fn l_Std_TreeSet_any___redArg___lam__0(
    mut v_p_3311_: *mut LeanObject,
    mut v___x_3312_: *mut LeanObject,
    mut v___x_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_b_3315_: *mut LeanObject,
    mut v_acc_3316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    v___x_3317_ = lean_apply_1(v_p_3311_, v_a_3314_);
    v___x_3318_ = (lean_unbox(v___x_3317_) as u8);
    if v___x_3318_ == 0 {
        let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
        v___x_3319_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3319_, 0, v___x_3312_);
        return v___x_3319_;
    } else {
        let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_3312_);
        v___x_3320_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3320_, 0, v___x_3317_);
        v___x_3321_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3321_, 0, v___x_3320_);
        lean_ctor_set(v___x_3321_, 1, v___x_3313_);
        v___x_3322_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3322_, 0, v___x_3321_);
        return v___x_3322_;
    }
}
pub unsafe fn l_Std_TreeSet_any___redArg___lam__0___boxed(
    mut v_p_3323_: *mut LeanObject,
    mut v___x_3324_: *mut LeanObject,
    mut v___x_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
    mut v_b_3327_: *mut LeanObject,
    mut v_acc_3328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3329_: *mut LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Std_TreeSet_any___redArg___lam__0(
        v_p_3323_,
        v___x_3324_,
        v___x_3325_,
        v_a_3326_,
        v_b_3327_,
        v_acc_3328_,
    );
    lean_dec_ref(v_acc_3328_);
    return v_res_3329_;
}
pub unsafe fn l_Std_TreeSet_any___redArg(
    mut v_t_3333_: *mut LeanObject,
    mut v_p_3334_: *mut LeanObject,
) -> u8 {
    let mut v___y_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    let mut v_val_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3341_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3342_ = lean_box(0);
                v___x_3343_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3344_ = lean_alloc_closure(
                    l_Std_TreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3344_, 0, v_p_3334_);
                lean_closure_set(v___f_3344_, 1, v___x_3343_);
                lean_closure_set(v___f_3344_, 2, v___x_3342_);
                v___x_3345_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3341_,
                    v___f_3344_,
                    v___x_3343_,
                    v_t_3333_,
                );
                v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
                lean_inc(v_a_3346_);
                lean_dec(v___x_3345_);
                v___y_3336_ = v_a_3346_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3337_ = lean_ctor_get(v___y_3336_, 0);
                lean_inc(v_fst_3337_);
                lean_dec_ref(v___y_3336_);
                if lean_obj_tag(v_fst_3337_) == 0 {
                    v___x_3338_ = 0;
                    return v___x_3338_;
                } else {
                    v_val_3339_ = lean_ctor_get(v_fst_3337_, 0);
                    lean_inc(v_val_3339_);
                    lean_dec_ref_known(v_fst_3337_, 1);
                    v___x_3340_ = (lean_unbox(v_val_3339_) as u8);
                    lean_dec(v_val_3339_);
                    return v___x_3340_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_any___redArg___boxed(
    mut v_t_3347_: *mut LeanObject,
    mut v_p_3348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3349_: u8 = 0;
    let mut v_r_3350_: *mut LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Std_TreeSet_any___redArg(v_t_3347_, v_p_3348_);
    v_r_3350_ = lean_box((v_res_3349_) as usize);
    return v_r_3350_;
}
pub unsafe fn l_Std_TreeSet_any(
    mut v_00_u03b1_3351_: *mut LeanObject,
    mut v_cmp_3352_: *mut LeanObject,
    mut v_t_3353_: *mut LeanObject,
    mut v_p_3354_: *mut LeanObject,
) -> u8 {
    let mut v___y_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v_val_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3361_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3362_ = lean_box(0);
                v___x_3363_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3364_ = lean_alloc_closure(
                    l_Std_TreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3364_, 0, v_p_3354_);
                lean_closure_set(v___f_3364_, 1, v___x_3363_);
                lean_closure_set(v___f_3364_, 2, v___x_3362_);
                v___x_3365_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3361_,
                    v___f_3364_,
                    v___x_3363_,
                    v_t_3353_,
                );
                v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
                lean_inc(v_a_3366_);
                lean_dec(v___x_3365_);
                v___y_3356_ = v_a_3366_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3357_ = lean_ctor_get(v___y_3356_, 0);
                lean_inc(v_fst_3357_);
                lean_dec_ref(v___y_3356_);
                if lean_obj_tag(v_fst_3357_) == 0 {
                    v___x_3358_ = 0;
                    return v___x_3358_;
                } else {
                    v_val_3359_ = lean_ctor_get(v_fst_3357_, 0);
                    lean_inc(v_val_3359_);
                    lean_dec_ref_known(v_fst_3357_, 1);
                    v___x_3360_ = (lean_unbox(v_val_3359_) as u8);
                    lean_dec(v_val_3359_);
                    return v___x_3360_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_any___boxed(
    mut v_00_u03b1_3367_: *mut LeanObject,
    mut v_cmp_3368_: *mut LeanObject,
    mut v_t_3369_: *mut LeanObject,
    mut v_p_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3371_: u8 = 0;
    let mut v_r_3372_: *mut LeanObject = core::ptr::null_mut();
    v_res_3371_ = l_Std_TreeSet_any(v_00_u03b1_3367_, v_cmp_3368_, v_t_3369_, v_p_3370_);
    lean_dec_ref(v_cmp_3368_);
    v_r_3372_ = lean_box((v_res_3371_) as usize);
    return v_r_3372_;
}
pub unsafe fn l_Std_TreeSet_all___redArg___lam__0(
    mut v_p_3373_: *mut LeanObject,
    mut v___x_3374_: *mut LeanObject,
    mut v___x_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_b_3377_: *mut LeanObject,
    mut v_acc_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: u8 = 0;
    v___x_3379_ = lean_apply_1(v_p_3373_, v_a_3376_);
    v___x_3380_ = (lean_unbox(v___x_3379_) as u8);
    if v___x_3380_ == 0 {
        let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_3375_);
        v___x_3381_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3381_, 0, v___x_3379_);
        v___x_3382_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3382_, 0, v___x_3381_);
        lean_ctor_set(v___x_3382_, 1, v___x_3374_);
        v___x_3383_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3383_, 0, v___x_3382_);
        return v___x_3383_;
    } else {
        let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
        v___x_3384_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3384_, 0, v___x_3375_);
        return v___x_3384_;
    }
}
pub unsafe fn l_Std_TreeSet_all___redArg___lam__0___boxed(
    mut v_p_3385_: *mut LeanObject,
    mut v___x_3386_: *mut LeanObject,
    mut v___x_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
    mut v_b_3389_: *mut LeanObject,
    mut v_acc_3390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3391_: *mut LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Std_TreeSet_all___redArg___lam__0(
        v_p_3385_,
        v___x_3386_,
        v___x_3387_,
        v_a_3388_,
        v_b_3389_,
        v_acc_3390_,
    );
    lean_dec_ref(v_acc_3390_);
    return v_res_3391_;
}
pub unsafe fn l_Std_TreeSet_all___redArg(
    mut v_t_3392_: *mut LeanObject,
    mut v_p_3393_: *mut LeanObject,
) -> u8 {
    let mut v___y_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v_val_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3400_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3401_ = lean_box(0);
                v___x_3402_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3403_ = lean_alloc_closure(
                    l_Std_TreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3403_, 0, v_p_3393_);
                lean_closure_set(v___f_3403_, 1, v___x_3401_);
                lean_closure_set(v___f_3403_, 2, v___x_3402_);
                v___x_3404_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3400_,
                    v___f_3403_,
                    v___x_3402_,
                    v_t_3392_,
                );
                v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
                lean_inc(v_a_3405_);
                lean_dec(v___x_3404_);
                v___y_3395_ = v_a_3405_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3396_ = lean_ctor_get(v___y_3395_, 0);
                lean_inc(v_fst_3396_);
                lean_dec_ref(v___y_3395_);
                if lean_obj_tag(v_fst_3396_) == 0 {
                    v___x_3397_ = 1;
                    return v___x_3397_;
                } else {
                    v_val_3398_ = lean_ctor_get(v_fst_3396_, 0);
                    lean_inc(v_val_3398_);
                    lean_dec_ref_known(v_fst_3396_, 1);
                    v___x_3399_ = (lean_unbox(v_val_3398_) as u8);
                    lean_dec(v_val_3398_);
                    return v___x_3399_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_all___redArg___boxed(
    mut v_t_3406_: *mut LeanObject,
    mut v_p_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3408_: u8 = 0;
    let mut v_r_3409_: *mut LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Std_TreeSet_all___redArg(v_t_3406_, v_p_3407_);
    v_r_3409_ = lean_box((v_res_3408_) as usize);
    return v_r_3409_;
}
pub unsafe fn l_Std_TreeSet_all(
    mut v_00_u03b1_3410_: *mut LeanObject,
    mut v_cmp_3411_: *mut LeanObject,
    mut v_t_3412_: *mut LeanObject,
    mut v_p_3413_: *mut LeanObject,
) -> u8 {
    let mut v___y_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v_val_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: u8 = 0;
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3420_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3421_ = lean_box(0);
                v___x_3422_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3423_ = lean_alloc_closure(
                    l_Std_TreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3423_, 0, v_p_3413_);
                lean_closure_set(v___f_3423_, 1, v___x_3421_);
                lean_closure_set(v___f_3423_, 2, v___x_3422_);
                v___x_3424_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3420_,
                    v___f_3423_,
                    v___x_3422_,
                    v_t_3412_,
                );
                v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
                lean_inc(v_a_3425_);
                lean_dec(v___x_3424_);
                v___y_3415_ = v_a_3425_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3416_ = lean_ctor_get(v___y_3415_, 0);
                lean_inc(v_fst_3416_);
                lean_dec_ref(v___y_3415_);
                if lean_obj_tag(v_fst_3416_) == 0 {
                    v___x_3417_ = 1;
                    return v___x_3417_;
                } else {
                    v_val_3418_ = lean_ctor_get(v_fst_3416_, 0);
                    lean_inc(v_val_3418_);
                    lean_dec_ref_known(v_fst_3416_, 1);
                    v___x_3419_ = (lean_unbox(v_val_3418_) as u8);
                    lean_dec(v_val_3418_);
                    return v___x_3419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_all___boxed(
    mut v_00_u03b1_3426_: *mut LeanObject,
    mut v_cmp_3427_: *mut LeanObject,
    mut v_t_3428_: *mut LeanObject,
    mut v_p_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3430_: u8 = 0;
    let mut v_r_3431_: *mut LeanObject = core::ptr::null_mut();
    v_res_3430_ = l_Std_TreeSet_all(v_00_u03b1_3426_, v_cmp_3427_, v_t_3428_, v_p_3429_);
    lean_dec_ref(v_cmp_3427_);
    v_r_3431_ = lean_box((v_res_3430_) as usize);
    return v_r_3431_;
}
pub unsafe fn l_Std_TreeSet_toList___redArg___lam__0(
    mut v_x1_3432_: *mut LeanObject,
    mut v_x2_3433_: *mut LeanObject,
    mut v_x3_3434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    v___x_3435_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3435_, 0, v_x1_3432_);
    lean_ctor_set(v___x_3435_, 1, v_x3_3434_);
    return v___x_3435_;
}
pub unsafe fn l_Std_TreeSet_toList___redArg(mut v_t_3437_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    v___f_3438_ = l_Std_TreeSet_toList___redArg___closed__0;
    v___x_3439_ = lean_box(0);
    v___x_3440_ = l_Std_TreeSet_foldr___redArg___closed__9;
    v___x_3441_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3440_,
        v___f_3438_,
        v___x_3439_,
        v_t_3437_,
    );
    return v___x_3441_;
}
pub unsafe fn l_Std_TreeSet_toList(
    mut v_00_u03b1_3442_: *mut LeanObject,
    mut v_cmp_3443_: *mut LeanObject,
    mut v_t_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    v___f_3445_ = l_Std_TreeSet_toList___redArg___closed__0;
    v___x_3446_ = lean_box(0);
    v___x_3447_ = l_Std_TreeSet_foldr___redArg___closed__9;
    v___x_3448_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3447_,
        v___f_3445_,
        v___x_3446_,
        v_t_3444_,
    );
    return v___x_3448_;
}
pub unsafe fn l_Std_TreeSet_toList___boxed(
    mut v_00_u03b1_3449_: *mut LeanObject,
    mut v_cmp_3450_: *mut LeanObject,
    mut v_t_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3452_: *mut LeanObject = core::ptr::null_mut();
    v_res_3452_ = l_Std_TreeSet_toList(v_00_u03b1_3449_, v_cmp_3450_, v_t_3451_);
    lean_dec_ref(v_cmp_3450_);
    return v_res_3452_;
}
pub unsafe fn _init_l_Std_TreeSet_ofList___auto__1() -> *mut LeanObject {
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    v___x_3453_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26_once),
        _init_l_Std_TreeSet___auto__1___closed__26,
    );
    return v___x_3453_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(
    mut v_cmp_3454_: *mut LeanObject,
    mut v_k_3455_: *mut LeanObject,
    mut v_v_3456_: *mut LeanObject,
    mut v_t_3457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v_impl_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v_size_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_unused_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_unused_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3561_: u8 = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3569_: u8 = 0;
    let mut v_unused_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v_k_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3593_: u8 = 0;
    let mut v_unused_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3597_: u8 = 0;
    let mut v_unused_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v_size_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: u8 = 0;
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3680_: u8 = 0;
    let mut v_unused_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v_unused_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3699_: u8 = 0;
    let mut v_k_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut v_unused_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_unused_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_unused_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3457_) == 0 {
                    v_size_3458_ = lean_ctor_get(v_t_3457_, 0);
                    v_k_3459_ = lean_ctor_get(v_t_3457_, 1);
                    v_v_3460_ = lean_ctor_get(v_t_3457_, 2);
                    v_l_3461_ = lean_ctor_get(v_t_3457_, 3);
                    v_r_3462_ = lean_ctor_get(v_t_3457_, 4);
                    v_isSharedCheck_3743_ = (!lean_is_exclusive(v_t_3457_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3464_ = v_t_3457_;
                        v_isShared_3465_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3462_);
                        lean_inc(v_l_3461_);
                        lean_inc(v_v_3460_);
                        lean_inc(v_k_3459_);
                        lean_inc(v_size_3458_);
                        lean_dec(v_t_3457_);
                        v___x_3464_ = lean_box(0);
                        v_isShared_3465_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_cmp_3454_);
                    v___x_3744_ = lean_unsigned_to_nat(1);
                    v___x_3745_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3745_, 0, v___x_3744_);
                    lean_ctor_set(v___x_3745_, 1, v_k_3455_);
                    lean_ctor_set(v___x_3745_, 2, v_v_3456_);
                    lean_ctor_set(v___x_3745_, 3, v_t_3457_);
                    lean_ctor_set(v___x_3745_, 4, v_t_3457_);
                    return v___x_3745_;
                }
            }
            1 => {
                lean_inc_ref(v_cmp_3454_);
                lean_inc(v_k_3459_);
                lean_inc(v_k_3455_);
                v___x_3466_ = lean_apply_2(v_cmp_3454_, v_k_3455_, v_k_3459_);
                v___x_3467_ = (lean_unbox(v___x_3466_) as u8);
                match v___x_3467_ {
                    0 => {
                        lean_dec(v_size_3458_);
                        v_impl_3468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_3454_, v_k_3455_, v_v_3456_, v_l_3461_);
                        v___x_3469_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_3462_) == 0 {
                            v_size_3470_ = lean_ctor_get(v_r_3462_, 0);
                            v_size_3471_ = lean_ctor_get(v_impl_3468_, 0);
                            lean_inc(v_size_3471_);
                            v_k_3472_ = lean_ctor_get(v_impl_3468_, 1);
                            lean_inc(v_k_3472_);
                            v_v_3473_ = lean_ctor_get(v_impl_3468_, 2);
                            lean_inc(v_v_3473_);
                            v_l_3474_ = lean_ctor_get(v_impl_3468_, 3);
                            lean_inc(v_l_3474_);
                            v_r_3475_ = lean_ctor_get(v_impl_3468_, 4);
                            lean_inc(v_r_3475_);
                            v___x_3476_ = lean_unsigned_to_nat(3);
                            v___x_3477_ = lean_nat_mul(v___x_3476_, v_size_3470_);
                            v___x_3478_ = lean_nat_dec_lt(v___x_3477_, v_size_3471_);
                            lean_dec(v___x_3477_);
                            if v___x_3478_ == 0 {
                                lean_dec(v_r_3475_);
                                lean_dec(v_l_3474_);
                                lean_dec(v_v_3473_);
                                lean_dec(v_k_3472_);
                                v___x_3479_ = lean_nat_add(v___x_3469_, v_size_3471_);
                                lean_dec(v_size_3471_);
                                v___x_3480_ = lean_nat_add(v___x_3479_, v_size_3470_);
                                lean_dec(v___x_3479_);
                                if v_isShared_3465_ == 0 {
                                    lean_ctor_set(v___x_3464_, 3, v_impl_3468_);
                                    lean_ctor_set(v___x_3464_, 0, v___x_3480_);
                                    v___x_3482_ = v___x_3464_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
                                    lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_3459_);
                                    lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_3460_);
                                    lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_impl_3468_);
                                    lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_r_3462_);
                                    v___x_3482_ = v_reuseFailAlloc_3483_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3549_ = (!lean_is_exclusive(v_impl_3468_)) as u8;
                                if v_isSharedCheck_3549_ == 0 {
                                    v_unused_3550_ = lean_ctor_get(v_impl_3468_, 4);
                                    lean_dec(v_unused_3550_);
                                    v_unused_3551_ = lean_ctor_get(v_impl_3468_, 3);
                                    lean_dec(v_unused_3551_);
                                    v_unused_3552_ = lean_ctor_get(v_impl_3468_, 2);
                                    lean_dec(v_unused_3552_);
                                    v_unused_3553_ = lean_ctor_get(v_impl_3468_, 1);
                                    lean_dec(v_unused_3553_);
                                    v_unused_3554_ = lean_ctor_get(v_impl_3468_, 0);
                                    lean_dec(v_unused_3554_);
                                    v___x_3485_ = v_impl_3468_;
                                    v_isShared_3486_ = v_isSharedCheck_3549_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_3468_);
                                    v___x_3485_ = lean_box(0);
                                    v_isShared_3486_ = v_isSharedCheck_3549_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3555_ = lean_ctor_get(v_impl_3468_, 3);
                            lean_inc(v_l_3555_);
                            if lean_obj_tag(v_l_3555_) == 0 {
                                v_r_3556_ = lean_ctor_get(v_impl_3468_, 4);
                                v_k_3557_ = lean_ctor_get(v_impl_3468_, 1);
                                v_v_3558_ = lean_ctor_get(v_impl_3468_, 2);
                                v_isSharedCheck_3569_ = (!lean_is_exclusive(v_impl_3468_)) as u8;
                                if v_isSharedCheck_3569_ == 0 {
                                    v_unused_3570_ = lean_ctor_get(v_impl_3468_, 3);
                                    lean_dec(v_unused_3570_);
                                    v_unused_3571_ = lean_ctor_get(v_impl_3468_, 0);
                                    lean_dec(v_unused_3571_);
                                    v___x_3560_ = v_impl_3468_;
                                    v_isShared_3561_ = v_isSharedCheck_3569_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_3556_);
                                    lean_inc(v_v_3558_);
                                    lean_inc(v_k_3557_);
                                    lean_dec(v_impl_3468_);
                                    v___x_3560_ = lean_box(0);
                                    v_isShared_3561_ = v_isSharedCheck_3569_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3572_ = lean_ctor_get(v_impl_3468_, 4);
                                lean_inc(v_r_3572_);
                                if lean_obj_tag(v_r_3572_) == 0 {
                                    v_k_3573_ = lean_ctor_get(v_impl_3468_, 1);
                                    v_v_3574_ = lean_ctor_get(v_impl_3468_, 2);
                                    v_isSharedCheck_3597_ =
                                        (!lean_is_exclusive(v_impl_3468_)) as u8;
                                    if v_isSharedCheck_3597_ == 0 {
                                        v_unused_3598_ = lean_ctor_get(v_impl_3468_, 4);
                                        lean_dec(v_unused_3598_);
                                        v_unused_3599_ = lean_ctor_get(v_impl_3468_, 3);
                                        lean_dec(v_unused_3599_);
                                        v_unused_3600_ = lean_ctor_get(v_impl_3468_, 0);
                                        lean_dec(v_unused_3600_);
                                        v___x_3576_ = v_impl_3468_;
                                        v_isShared_3577_ = v_isSharedCheck_3597_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3574_);
                                        lean_inc(v_k_3573_);
                                        lean_dec(v_impl_3468_);
                                        v___x_3576_ = lean_box(0);
                                        v_isShared_3577_ = v_isSharedCheck_3597_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_3601_ = lean_unsigned_to_nat(2);
                                    if v_isShared_3465_ == 0 {
                                        lean_ctor_set(v___x_3464_, 4, v_r_3572_);
                                        lean_ctor_set(v___x_3464_, 3, v_impl_3468_);
                                        lean_ctor_set(v___x_3464_, 0, v___x_3601_);
                                        v___x_3603_ = v___x_3464_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
                                        lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_k_3459_);
                                        lean_ctor_set(v_reuseFailAlloc_3604_, 2, v_v_3460_);
                                        lean_ctor_set(v_reuseFailAlloc_3604_, 3, v_impl_3468_);
                                        lean_ctor_set(v_reuseFailAlloc_3604_, 4, v_r_3572_);
                                        v___x_3603_ = v_reuseFailAlloc_3604_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_3460_);
                        lean_dec(v_k_3459_);
                        lean_dec_ref(v_cmp_3454_);
                        if v_isShared_3465_ == 0 {
                            lean_ctor_set(v___x_3464_, 2, v_v_3456_);
                            lean_ctor_set(v___x_3464_, 1, v_k_3455_);
                            v___x_3606_ = v___x_3464_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_size_3458_);
                            lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_k_3455_);
                            lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_v_3456_);
                            lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_l_3461_);
                            lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_r_3462_);
                            v___x_3606_ = v_reuseFailAlloc_3607_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_3458_);
                        v_impl_3608_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_3454_, v_k_3455_, v_v_3456_, v_r_3462_);
                        v___x_3609_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_3461_) == 0 {
                            v_size_3610_ = lean_ctor_get(v_l_3461_, 0);
                            v_size_3611_ = lean_ctor_get(v_impl_3608_, 0);
                            lean_inc(v_size_3611_);
                            v_k_3612_ = lean_ctor_get(v_impl_3608_, 1);
                            lean_inc(v_k_3612_);
                            v_v_3613_ = lean_ctor_get(v_impl_3608_, 2);
                            lean_inc(v_v_3613_);
                            v_l_3614_ = lean_ctor_get(v_impl_3608_, 3);
                            lean_inc(v_l_3614_);
                            v_r_3615_ = lean_ctor_get(v_impl_3608_, 4);
                            lean_inc(v_r_3615_);
                            v___x_3616_ = lean_unsigned_to_nat(3);
                            v___x_3617_ = lean_nat_mul(v___x_3616_, v_size_3610_);
                            v___x_3618_ = lean_nat_dec_lt(v___x_3617_, v_size_3611_);
                            lean_dec(v___x_3617_);
                            if v___x_3618_ == 0 {
                                lean_dec(v_r_3615_);
                                lean_dec(v_l_3614_);
                                lean_dec(v_v_3613_);
                                lean_dec(v_k_3612_);
                                v___x_3619_ = lean_nat_add(v___x_3609_, v_size_3610_);
                                v___x_3620_ = lean_nat_add(v___x_3619_, v_size_3611_);
                                lean_dec(v_size_3611_);
                                lean_dec(v___x_3619_);
                                if v_isShared_3465_ == 0 {
                                    lean_ctor_set(v___x_3464_, 4, v_impl_3608_);
                                    lean_ctor_set(v___x_3464_, 0, v___x_3620_);
                                    v___x_3622_ = v___x_3464_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
                                    lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_k_3459_);
                                    lean_ctor_set(v_reuseFailAlloc_3623_, 2, v_v_3460_);
                                    lean_ctor_set(v_reuseFailAlloc_3623_, 3, v_l_3461_);
                                    lean_ctor_set(v_reuseFailAlloc_3623_, 4, v_impl_3608_);
                                    v___x_3622_ = v_reuseFailAlloc_3623_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3687_ = (!lean_is_exclusive(v_impl_3608_)) as u8;
                                if v_isSharedCheck_3687_ == 0 {
                                    v_unused_3688_ = lean_ctor_get(v_impl_3608_, 4);
                                    lean_dec(v_unused_3688_);
                                    v_unused_3689_ = lean_ctor_get(v_impl_3608_, 3);
                                    lean_dec(v_unused_3689_);
                                    v_unused_3690_ = lean_ctor_get(v_impl_3608_, 2);
                                    lean_dec(v_unused_3690_);
                                    v_unused_3691_ = lean_ctor_get(v_impl_3608_, 1);
                                    lean_dec(v_unused_3691_);
                                    v_unused_3692_ = lean_ctor_get(v_impl_3608_, 0);
                                    lean_dec(v_unused_3692_);
                                    v___x_3625_ = v_impl_3608_;
                                    v_isShared_3626_ = v_isSharedCheck_3687_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_3608_);
                                    v___x_3625_ = lean_box(0);
                                    v_isShared_3626_ = v_isSharedCheck_3687_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3693_ = lean_ctor_get(v_impl_3608_, 3);
                            lean_inc(v_l_3693_);
                            if lean_obj_tag(v_l_3693_) == 0 {
                                v_r_3694_ = lean_ctor_get(v_impl_3608_, 4);
                                v_k_3695_ = lean_ctor_get(v_impl_3608_, 1);
                                v_v_3696_ = lean_ctor_get(v_impl_3608_, 2);
                                v_isSharedCheck_3719_ = (!lean_is_exclusive(v_impl_3608_)) as u8;
                                if v_isSharedCheck_3719_ == 0 {
                                    v_unused_3720_ = lean_ctor_get(v_impl_3608_, 3);
                                    lean_dec(v_unused_3720_);
                                    v_unused_3721_ = lean_ctor_get(v_impl_3608_, 0);
                                    lean_dec(v_unused_3721_);
                                    v___x_3698_ = v_impl_3608_;
                                    v_isShared_3699_ = v_isSharedCheck_3719_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_3694_);
                                    lean_inc(v_v_3696_);
                                    lean_inc(v_k_3695_);
                                    lean_dec(v_impl_3608_);
                                    v___x_3698_ = lean_box(0);
                                    v_isShared_3699_ = v_isSharedCheck_3719_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3722_ = lean_ctor_get(v_impl_3608_, 4);
                                lean_inc(v_r_3722_);
                                if lean_obj_tag(v_r_3722_) == 0 {
                                    v_k_3723_ = lean_ctor_get(v_impl_3608_, 1);
                                    v_v_3724_ = lean_ctor_get(v_impl_3608_, 2);
                                    v_isSharedCheck_3735_ =
                                        (!lean_is_exclusive(v_impl_3608_)) as u8;
                                    if v_isSharedCheck_3735_ == 0 {
                                        v_unused_3736_ = lean_ctor_get(v_impl_3608_, 4);
                                        lean_dec(v_unused_3736_);
                                        v_unused_3737_ = lean_ctor_get(v_impl_3608_, 3);
                                        lean_dec(v_unused_3737_);
                                        v_unused_3738_ = lean_ctor_get(v_impl_3608_, 0);
                                        lean_dec(v_unused_3738_);
                                        v___x_3726_ = v_impl_3608_;
                                        v_isShared_3727_ = v_isSharedCheck_3735_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3724_);
                                        lean_inc(v_k_3723_);
                                        lean_dec(v_impl_3608_);
                                        v___x_3726_ = lean_box(0);
                                        v_isShared_3727_ = v_isSharedCheck_3735_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3739_ = lean_unsigned_to_nat(2);
                                    if v_isShared_3465_ == 0 {
                                        lean_ctor_set(v___x_3464_, 4, v_impl_3608_);
                                        lean_ctor_set(v___x_3464_, 3, v_r_3722_);
                                        lean_ctor_set(v___x_3464_, 0, v___x_3739_);
                                        v___x_3741_ = v___x_3464_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
                                        lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_k_3459_);
                                        lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_v_3460_);
                                        lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_r_3722_);
                                        lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_impl_3608_);
                                        v___x_3741_ = v_reuseFailAlloc_3742_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3482_;
            }
            3 => {
                v_size_3487_ = lean_ctor_get(v_l_3474_, 0);
                v_size_3488_ = lean_ctor_get(v_r_3475_, 0);
                v_k_3489_ = lean_ctor_get(v_r_3475_, 1);
                v_v_3490_ = lean_ctor_get(v_r_3475_, 2);
                v_l_3491_ = lean_ctor_get(v_r_3475_, 3);
                v_r_3492_ = lean_ctor_get(v_r_3475_, 4);
                v___x_3493_ = lean_unsigned_to_nat(2);
                v___x_3494_ = lean_nat_mul(v___x_3493_, v_size_3487_);
                v___x_3495_ = lean_nat_dec_lt(v_size_3488_, v___x_3494_);
                lean_dec(v___x_3494_);
                if v___x_3495_ == 0 {
                    lean_inc(v_r_3492_);
                    lean_inc(v_l_3491_);
                    lean_inc(v_v_3490_);
                    lean_inc(v_k_3489_);
                    v_isSharedCheck_3524_ = (!lean_is_exclusive(v_r_3475_)) as u8;
                    if v_isSharedCheck_3524_ == 0 {
                        v_unused_3525_ = lean_ctor_get(v_r_3475_, 4);
                        lean_dec(v_unused_3525_);
                        v_unused_3526_ = lean_ctor_get(v_r_3475_, 3);
                        lean_dec(v_unused_3526_);
                        v_unused_3527_ = lean_ctor_get(v_r_3475_, 2);
                        lean_dec(v_unused_3527_);
                        v_unused_3528_ = lean_ctor_get(v_r_3475_, 1);
                        lean_dec(v_unused_3528_);
                        v_unused_3529_ = lean_ctor_get(v_r_3475_, 0);
                        lean_dec(v_unused_3529_);
                        v___x_3497_ = v_r_3475_;
                        v_isShared_3498_ = v_isSharedCheck_3524_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_3475_);
                        v___x_3497_ = lean_box(0);
                        v_isShared_3498_ = v_isSharedCheck_3524_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3464_);
                    v___x_3530_ = lean_nat_add(v___x_3469_, v_size_3471_);
                    lean_dec(v_size_3471_);
                    v___x_3531_ = lean_nat_add(v___x_3530_, v_size_3470_);
                    lean_dec(v___x_3530_);
                    v___x_3532_ = lean_nat_add(v___x_3469_, v_size_3470_);
                    v___x_3533_ = lean_nat_add(v___x_3532_, v_size_3488_);
                    lean_dec(v___x_3532_);
                    lean_inc_ref(v_r_3462_);
                    if v_isShared_3486_ == 0 {
                        lean_ctor_set(v___x_3485_, 4, v_r_3462_);
                        lean_ctor_set(v___x_3485_, 3, v_r_3475_);
                        lean_ctor_set(v___x_3485_, 2, v_v_3460_);
                        lean_ctor_set(v___x_3485_, 1, v_k_3459_);
                        lean_ctor_set(v___x_3485_, 0, v___x_3533_);
                        v___x_3535_ = v___x_3485_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3533_);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3459_);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_v_3460_);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_r_3475_);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 4, v_r_3462_);
                        v___x_3535_ = v_reuseFailAlloc_3548_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3499_ = lean_nat_add(v___x_3469_, v_size_3471_);
                lean_dec(v_size_3471_);
                v___x_3500_ = lean_nat_add(v___x_3499_, v_size_3470_);
                lean_dec(v___x_3499_);
                v___x_3512_ = lean_nat_add(v___x_3469_, v_size_3487_);
                if lean_obj_tag(v_l_3491_) == 0 {
                    v_size_3522_ = lean_ctor_get(v_l_3491_, 0);
                    lean_inc(v_size_3522_);
                    v___y_3514_ = v_size_3522_;
                    state = 8;
                    continue;
                } else {
                    v___x_3523_ = lean_unsigned_to_nat(0);
                    v___y_3514_ = v___x_3523_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3505_ = lean_nat_add(v___y_3502_, v___y_3504_);
                lean_dec(v___y_3504_);
                lean_dec(v___y_3502_);
                if v_isShared_3498_ == 0 {
                    lean_ctor_set(v___x_3497_, 4, v_r_3462_);
                    lean_ctor_set(v___x_3497_, 3, v_r_3492_);
                    lean_ctor_set(v___x_3497_, 2, v_v_3460_);
                    lean_ctor_set(v___x_3497_, 1, v_k_3459_);
                    lean_ctor_set(v___x_3497_, 0, v___x_3505_);
                    v___x_3507_ = v___x_3497_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3505_);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_k_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 2, v_v_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 3, v_r_3492_);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 4, v_r_3462_);
                    v___x_3507_ = v_reuseFailAlloc_3511_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3486_ == 0 {
                    lean_ctor_set(v___x_3485_, 4, v___x_3507_);
                    lean_ctor_set(v___x_3485_, 3, v___y_3503_);
                    lean_ctor_set(v___x_3485_, 2, v_v_3490_);
                    lean_ctor_set(v___x_3485_, 1, v_k_3489_);
                    lean_ctor_set(v___x_3485_, 0, v___x_3500_);
                    v___x_3509_ = v___x_3485_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3500_);
                    lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_k_3489_);
                    lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_v_3490_);
                    lean_ctor_set(v_reuseFailAlloc_3510_, 3, v___y_3503_);
                    lean_ctor_set(v_reuseFailAlloc_3510_, 4, v___x_3507_);
                    v___x_3509_ = v_reuseFailAlloc_3510_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3509_;
            }
            8 => {
                v___x_3515_ = lean_nat_add(v___x_3512_, v___y_3514_);
                lean_dec(v___y_3514_);
                lean_dec(v___x_3512_);
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 4, v_l_3491_);
                    lean_ctor_set(v___x_3464_, 3, v_l_3474_);
                    lean_ctor_set(v___x_3464_, 2, v_v_3473_);
                    lean_ctor_set(v___x_3464_, 1, v_k_3472_);
                    lean_ctor_set(v___x_3464_, 0, v___x_3515_);
                    v___x_3517_ = v___x_3464_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3515_);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3472_);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3473_);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_l_3474_);
                    lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_l_3491_);
                    v___x_3517_ = v_reuseFailAlloc_3521_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3518_ = lean_nat_add(v___x_3469_, v_size_3470_);
                if lean_obj_tag(v_r_3492_) == 0 {
                    v_size_3519_ = lean_ctor_get(v_r_3492_, 0);
                    lean_inc(v_size_3519_);
                    v___y_3502_ = v___x_3518_;
                    v___y_3503_ = v___x_3517_;
                    v___y_3504_ = v_size_3519_;
                    state = 5;
                    continue;
                } else {
                    v___x_3520_ = lean_unsigned_to_nat(0);
                    v___y_3502_ = v___x_3518_;
                    v___y_3503_ = v___x_3517_;
                    v___y_3504_ = v___x_3520_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3542_ = (!lean_is_exclusive(v_r_3462_)) as u8;
                if v_isSharedCheck_3542_ == 0 {
                    v_unused_3543_ = lean_ctor_get(v_r_3462_, 4);
                    lean_dec(v_unused_3543_);
                    v_unused_3544_ = lean_ctor_get(v_r_3462_, 3);
                    lean_dec(v_unused_3544_);
                    v_unused_3545_ = lean_ctor_get(v_r_3462_, 2);
                    lean_dec(v_unused_3545_);
                    v_unused_3546_ = lean_ctor_get(v_r_3462_, 1);
                    lean_dec(v_unused_3546_);
                    v_unused_3547_ = lean_ctor_get(v_r_3462_, 0);
                    lean_dec(v_unused_3547_);
                    v___x_3537_ = v_r_3462_;
                    v_isShared_3538_ = v_isSharedCheck_3542_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_3462_);
                    v___x_3537_ = lean_box(0);
                    v_isShared_3538_ = v_isSharedCheck_3542_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3538_ == 0 {
                    lean_ctor_set(v___x_3537_, 4, v___x_3535_);
                    lean_ctor_set(v___x_3537_, 3, v_l_3474_);
                    lean_ctor_set(v___x_3537_, 2, v_v_3473_);
                    lean_ctor_set(v___x_3537_, 1, v_k_3472_);
                    lean_ctor_set(v___x_3537_, 0, v___x_3531_);
                    v___x_3540_ = v___x_3537_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3531_);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_k_3472_);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_v_3473_);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 3, v_l_3474_);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 4, v___x_3535_);
                    v___x_3540_ = v_reuseFailAlloc_3541_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3540_;
            }
            13 => {
                v___x_3562_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_3556_);
                if v_isShared_3561_ == 0 {
                    lean_ctor_set(v___x_3560_, 3, v_r_3556_);
                    lean_ctor_set(v___x_3560_, 2, v_v_3460_);
                    lean_ctor_set(v___x_3560_, 1, v_k_3459_);
                    lean_ctor_set(v___x_3560_, 0, v___x_3469_);
                    v___x_3564_ = v___x_3560_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3469_);
                    lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_k_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_v_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_r_3556_);
                    lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_r_3556_);
                    v___x_3564_ = v_reuseFailAlloc_3568_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 4, v___x_3564_);
                    lean_ctor_set(v___x_3464_, 3, v_l_3555_);
                    lean_ctor_set(v___x_3464_, 2, v_v_3558_);
                    lean_ctor_set(v___x_3464_, 1, v_k_3557_);
                    lean_ctor_set(v___x_3464_, 0, v___x_3562_);
                    v___x_3566_ = v___x_3464_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3562_);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_k_3557_);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 2, v_v_3558_);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 3, v_l_3555_);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 4, v___x_3564_);
                    v___x_3566_ = v_reuseFailAlloc_3567_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3566_;
            }
            16 => {
                v_k_3578_ = lean_ctor_get(v_r_3572_, 1);
                v_v_3579_ = lean_ctor_get(v_r_3572_, 2);
                v_isSharedCheck_3593_ = (!lean_is_exclusive(v_r_3572_)) as u8;
                if v_isSharedCheck_3593_ == 0 {
                    v_unused_3594_ = lean_ctor_get(v_r_3572_, 4);
                    lean_dec(v_unused_3594_);
                    v_unused_3595_ = lean_ctor_get(v_r_3572_, 3);
                    lean_dec(v_unused_3595_);
                    v_unused_3596_ = lean_ctor_get(v_r_3572_, 0);
                    lean_dec(v_unused_3596_);
                    v___x_3581_ = v_r_3572_;
                    v_isShared_3582_ = v_isSharedCheck_3593_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_3579_);
                    lean_inc(v_k_3578_);
                    lean_dec(v_r_3572_);
                    v___x_3581_ = lean_box(0);
                    v_isShared_3582_ = v_isSharedCheck_3593_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3583_ = lean_unsigned_to_nat(3);
                if v_isShared_3582_ == 0 {
                    lean_ctor_set(v___x_3581_, 4, v_l_3555_);
                    lean_ctor_set(v___x_3581_, 3, v_l_3555_);
                    lean_ctor_set(v___x_3581_, 2, v_v_3574_);
                    lean_ctor_set(v___x_3581_, 1, v_k_3573_);
                    lean_ctor_set(v___x_3581_, 0, v___x_3469_);
                    v___x_3585_ = v___x_3581_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3469_);
                    lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_k_3573_);
                    lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_v_3574_);
                    lean_ctor_set(v_reuseFailAlloc_3592_, 3, v_l_3555_);
                    lean_ctor_set(v_reuseFailAlloc_3592_, 4, v_l_3555_);
                    v___x_3585_ = v_reuseFailAlloc_3592_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3577_ == 0 {
                    lean_ctor_set(v___x_3576_, 4, v_l_3555_);
                    lean_ctor_set(v___x_3576_, 2, v_v_3460_);
                    lean_ctor_set(v___x_3576_, 1, v_k_3459_);
                    lean_ctor_set(v___x_3576_, 0, v___x_3469_);
                    v___x_3587_ = v___x_3576_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3469_);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_k_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 2, v_v_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 3, v_l_3555_);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 4, v_l_3555_);
                    v___x_3587_ = v_reuseFailAlloc_3591_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 4, v___x_3587_);
                    lean_ctor_set(v___x_3464_, 3, v___x_3585_);
                    lean_ctor_set(v___x_3464_, 2, v_v_3579_);
                    lean_ctor_set(v___x_3464_, 1, v_k_3578_);
                    lean_ctor_set(v___x_3464_, 0, v___x_3583_);
                    v___x_3589_ = v___x_3464_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3583_);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_k_3578_);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_v_3579_);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 3, v___x_3585_);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 4, v___x_3587_);
                    v___x_3589_ = v_reuseFailAlloc_3590_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3589_;
            }
            21 => {
                return v___x_3603_;
            }
            22 => {
                return v___x_3606_;
            }
            23 => {
                return v___x_3622_;
            }
            24 => {
                v_size_3627_ = lean_ctor_get(v_l_3614_, 0);
                v_k_3628_ = lean_ctor_get(v_l_3614_, 1);
                v_v_3629_ = lean_ctor_get(v_l_3614_, 2);
                v_l_3630_ = lean_ctor_get(v_l_3614_, 3);
                v_r_3631_ = lean_ctor_get(v_l_3614_, 4);
                v_size_3632_ = lean_ctor_get(v_r_3615_, 0);
                v___x_3633_ = lean_unsigned_to_nat(2);
                v___x_3634_ = lean_nat_mul(v___x_3633_, v_size_3632_);
                v___x_3635_ = lean_nat_dec_lt(v_size_3627_, v___x_3634_);
                lean_dec(v___x_3634_);
                if v___x_3635_ == 0 {
                    lean_inc(v_r_3631_);
                    lean_inc(v_l_3630_);
                    lean_inc(v_v_3629_);
                    lean_inc(v_k_3628_);
                    v_isSharedCheck_3663_ = (!lean_is_exclusive(v_l_3614_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v_unused_3664_ = lean_ctor_get(v_l_3614_, 4);
                        lean_dec(v_unused_3664_);
                        v_unused_3665_ = lean_ctor_get(v_l_3614_, 3);
                        lean_dec(v_unused_3665_);
                        v_unused_3666_ = lean_ctor_get(v_l_3614_, 2);
                        lean_dec(v_unused_3666_);
                        v_unused_3667_ = lean_ctor_get(v_l_3614_, 1);
                        lean_dec(v_unused_3667_);
                        v_unused_3668_ = lean_ctor_get(v_l_3614_, 0);
                        lean_dec(v_unused_3668_);
                        v___x_3637_ = v_l_3614_;
                        v_isShared_3638_ = v_isSharedCheck_3663_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_3614_);
                        v___x_3637_ = lean_box(0);
                        v_isShared_3638_ = v_isSharedCheck_3663_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3464_);
                    v___x_3669_ = lean_nat_add(v___x_3609_, v_size_3610_);
                    v___x_3670_ = lean_nat_add(v___x_3669_, v_size_3611_);
                    lean_dec(v_size_3611_);
                    v___x_3671_ = lean_nat_add(v___x_3669_, v_size_3627_);
                    lean_dec(v___x_3669_);
                    lean_inc_ref(v_l_3461_);
                    if v_isShared_3626_ == 0 {
                        lean_ctor_set(v___x_3625_, 4, v_l_3614_);
                        lean_ctor_set(v___x_3625_, 3, v_l_3461_);
                        lean_ctor_set(v___x_3625_, 2, v_v_3460_);
                        lean_ctor_set(v___x_3625_, 1, v_k_3459_);
                        lean_ctor_set(v___x_3625_, 0, v___x_3671_);
                        v___x_3673_ = v___x_3625_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3671_);
                        lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_k_3459_);
                        lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_v_3460_);
                        lean_ctor_set(v_reuseFailAlloc_3686_, 3, v_l_3461_);
                        lean_ctor_set(v_reuseFailAlloc_3686_, 4, v_l_3614_);
                        v___x_3673_ = v_reuseFailAlloc_3686_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3639_ = lean_nat_add(v___x_3609_, v_size_3610_);
                v___x_3640_ = lean_nat_add(v___x_3639_, v_size_3611_);
                lean_dec(v_size_3611_);
                if lean_obj_tag(v_l_3630_) == 0 {
                    v_size_3661_ = lean_ctor_get(v_l_3630_, 0);
                    lean_inc(v_size_3661_);
                    v___y_3653_ = v_size_3661_;
                    state = 29;
                    continue;
                } else {
                    v___x_3662_ = lean_unsigned_to_nat(0);
                    v___y_3653_ = v___x_3662_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3645_ = lean_nat_add(v___y_3643_, v___y_3644_);
                lean_dec(v___y_3644_);
                lean_dec(v___y_3643_);
                if v_isShared_3638_ == 0 {
                    lean_ctor_set(v___x_3637_, 4, v_r_3615_);
                    lean_ctor_set(v___x_3637_, 3, v_r_3631_);
                    lean_ctor_set(v___x_3637_, 2, v_v_3613_);
                    lean_ctor_set(v___x_3637_, 1, v_k_3612_);
                    lean_ctor_set(v___x_3637_, 0, v___x_3645_);
                    v___x_3647_ = v___x_3637_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3645_);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3612_);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3613_);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_r_3631_);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_r_3615_);
                    v___x_3647_ = v_reuseFailAlloc_3651_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3626_ == 0 {
                    lean_ctor_set(v___x_3625_, 4, v___x_3647_);
                    lean_ctor_set(v___x_3625_, 3, v___y_3642_);
                    lean_ctor_set(v___x_3625_, 2, v_v_3629_);
                    lean_ctor_set(v___x_3625_, 1, v_k_3628_);
                    lean_ctor_set(v___x_3625_, 0, v___x_3640_);
                    v___x_3649_ = v___x_3625_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3640_);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_k_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_v_3629_);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 3, v___y_3642_);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 4, v___x_3647_);
                    v___x_3649_ = v_reuseFailAlloc_3650_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3649_;
            }
            29 => {
                v___x_3654_ = lean_nat_add(v___x_3639_, v___y_3653_);
                lean_dec(v___y_3653_);
                lean_dec(v___x_3639_);
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 4, v_l_3630_);
                    lean_ctor_set(v___x_3464_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3464_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3654_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_l_3461_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_l_3630_);
                    v___x_3656_ = v_reuseFailAlloc_3660_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3657_ = lean_nat_add(v___x_3609_, v_size_3632_);
                if lean_obj_tag(v_r_3631_) == 0 {
                    v_size_3658_ = lean_ctor_get(v_r_3631_, 0);
                    lean_inc(v_size_3658_);
                    v___y_3642_ = v___x_3656_;
                    v___y_3643_ = v___x_3657_;
                    v___y_3644_ = v_size_3658_;
                    state = 26;
                    continue;
                } else {
                    v___x_3659_ = lean_unsigned_to_nat(0);
                    v___y_3642_ = v___x_3656_;
                    v___y_3643_ = v___x_3657_;
                    v___y_3644_ = v___x_3659_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3680_ = (!lean_is_exclusive(v_l_3461_)) as u8;
                if v_isSharedCheck_3680_ == 0 {
                    v_unused_3681_ = lean_ctor_get(v_l_3461_, 4);
                    lean_dec(v_unused_3681_);
                    v_unused_3682_ = lean_ctor_get(v_l_3461_, 3);
                    lean_dec(v_unused_3682_);
                    v_unused_3683_ = lean_ctor_get(v_l_3461_, 2);
                    lean_dec(v_unused_3683_);
                    v_unused_3684_ = lean_ctor_get(v_l_3461_, 1);
                    lean_dec(v_unused_3684_);
                    v_unused_3685_ = lean_ctor_get(v_l_3461_, 0);
                    lean_dec(v_unused_3685_);
                    v___x_3675_ = v_l_3461_;
                    v_isShared_3676_ = v_isSharedCheck_3680_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_3461_);
                    v___x_3675_ = lean_box(0);
                    v_isShared_3676_ = v_isSharedCheck_3680_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3676_ == 0 {
                    lean_ctor_set(v___x_3675_, 4, v_r_3615_);
                    lean_ctor_set(v___x_3675_, 3, v___x_3673_);
                    lean_ctor_set(v___x_3675_, 2, v_v_3613_);
                    lean_ctor_set(v___x_3675_, 1, v_k_3612_);
                    lean_ctor_set(v___x_3675_, 0, v___x_3670_);
                    v___x_3678_ = v___x_3675_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3670_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_k_3612_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_v_3613_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 3, v___x_3673_);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 4, v_r_3615_);
                    v___x_3678_ = v_reuseFailAlloc_3679_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3678_;
            }
            34 => {
                v_k_3700_ = lean_ctor_get(v_l_3693_, 1);
                v_v_3701_ = lean_ctor_get(v_l_3693_, 2);
                v_isSharedCheck_3715_ = (!lean_is_exclusive(v_l_3693_)) as u8;
                if v_isSharedCheck_3715_ == 0 {
                    v_unused_3716_ = lean_ctor_get(v_l_3693_, 4);
                    lean_dec(v_unused_3716_);
                    v_unused_3717_ = lean_ctor_get(v_l_3693_, 3);
                    lean_dec(v_unused_3717_);
                    v_unused_3718_ = lean_ctor_get(v_l_3693_, 0);
                    lean_dec(v_unused_3718_);
                    v___x_3703_ = v_l_3693_;
                    v_isShared_3704_ = v_isSharedCheck_3715_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_3701_);
                    lean_inc(v_k_3700_);
                    lean_dec(v_l_3693_);
                    v___x_3703_ = lean_box(0);
                    v_isShared_3704_ = v_isSharedCheck_3715_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3705_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_3694_, 2);
                if v_isShared_3704_ == 0 {
                    lean_ctor_set(v___x_3703_, 4, v_r_3694_);
                    lean_ctor_set(v___x_3703_, 3, v_r_3694_);
                    lean_ctor_set(v___x_3703_, 2, v_v_3460_);
                    lean_ctor_set(v___x_3703_, 1, v_k_3459_);
                    lean_ctor_set(v___x_3703_, 0, v___x_3609_);
                    v___x_3707_ = v___x_3703_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3609_);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_k_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_v_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_r_3694_);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 4, v_r_3694_);
                    v___x_3707_ = v_reuseFailAlloc_3714_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_3694_);
                if v_isShared_3699_ == 0 {
                    lean_ctor_set(v___x_3698_, 3, v_r_3694_);
                    lean_ctor_set(v___x_3698_, 0, v___x_3609_);
                    v___x_3709_ = v___x_3698_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3609_);
                    lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3695_);
                    lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3696_);
                    lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_r_3694_);
                    lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_r_3694_);
                    v___x_3709_ = v_reuseFailAlloc_3713_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 4, v___x_3709_);
                    lean_ctor_set(v___x_3464_, 3, v___x_3707_);
                    lean_ctor_set(v___x_3464_, 2, v_v_3701_);
                    lean_ctor_set(v___x_3464_, 1, v_k_3700_);
                    lean_ctor_set(v___x_3464_, 0, v___x_3705_);
                    v___x_3711_ = v___x_3464_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3705_);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_k_3700_);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 2, v_v_3701_);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 3, v___x_3707_);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 4, v___x_3709_);
                    v___x_3711_ = v_reuseFailAlloc_3712_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3711_;
            }
            39 => {
                v___x_3728_ = lean_unsigned_to_nat(3);
                if v_isShared_3727_ == 0 {
                    lean_ctor_set(v___x_3726_, 4, v_l_3693_);
                    lean_ctor_set(v___x_3726_, 2, v_v_3460_);
                    lean_ctor_set(v___x_3726_, 1, v_k_3459_);
                    lean_ctor_set(v___x_3726_, 0, v___x_3609_);
                    v___x_3730_ = v___x_3726_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3609_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_k_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_v_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_l_3693_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_l_3693_);
                    v___x_3730_ = v_reuseFailAlloc_3734_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 4, v_r_3722_);
                    lean_ctor_set(v___x_3464_, 3, v___x_3730_);
                    lean_ctor_set(v___x_3464_, 2, v_v_3724_);
                    lean_ctor_set(v___x_3464_, 1, v_k_3723_);
                    lean_ctor_set(v___x_3464_, 0, v___x_3728_);
                    v___x_3732_ = v___x_3464_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3728_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3723_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3724_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 3, v___x_3730_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_r_3722_);
                    v___x_3732_ = v_reuseFailAlloc_3733_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3732_;
            }
            42 => {
                return v___x_3741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(
    mut v_cmp_3746_: *mut LeanObject,
    mut v_k_3747_: *mut LeanObject,
    mut v_t_3748_: *mut LeanObject,
) -> u8 {
    let mut v_k_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3748_) == 0 {
                    v_k_3749_ = lean_ctor_get(v_t_3748_, 1);
                    lean_inc(v_k_3749_);
                    v_l_3750_ = lean_ctor_get(v_t_3748_, 3);
                    lean_inc(v_l_3750_);
                    v_r_3751_ = lean_ctor_get(v_t_3748_, 4);
                    lean_inc(v_r_3751_);
                    lean_dec_ref_known(v_t_3748_, 5);
                    lean_inc_ref(v_cmp_3746_);
                    lean_inc(v_k_3747_);
                    v___x_3752_ = lean_apply_2(v_cmp_3746_, v_k_3747_, v_k_3749_);
                    v___x_3753_ = (lean_unbox(v___x_3752_) as u8);
                    match v___x_3753_ {
                        0 => {
                            lean_dec(v_r_3751_);
                            v_t_3748_ = v_l_3750_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_3751_);
                            lean_dec(v_l_3750_);
                            lean_dec(v_k_3747_);
                            lean_dec_ref(v_cmp_3746_);
                            v___x_3755_ = 1;
                            return v___x_3755_;
                        }
                        _ => {
                            lean_dec(v_l_3750_);
                            v_t_3748_ = v_r_3751_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_3747_);
                    lean_dec_ref(v_cmp_3746_);
                    v___x_3757_ = 0;
                    return v___x_3757_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(
    mut v_cmp_3758_: *mut LeanObject,
    mut v_k_3759_: *mut LeanObject,
    mut v_t_3760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3761_: u8 = 0;
    let mut v_r_3762_: *mut LeanObject = core::ptr::null_mut();
    v_res_3761_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(
            v_cmp_3758_,
            v_k_3759_,
            v_t_3760_,
        );
    v_r_3762_ = lean_box((v_res_3761_) as usize);
    return v_r_3762_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
    mut v_cmp_3763_: *mut LeanObject,
    mut v_as_x27_3764_: *mut LeanObject,
    mut v_b_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3764_) == 0 {
                    lean_dec_ref(v_cmp_3763_);
                    return v_b_3765_;
                } else {
                    v_head_3766_ = lean_ctor_get(v_as_x27_3764_, 0);
                    v_tail_3767_ = lean_ctor_get(v_as_x27_3764_, 1);
                    lean_inc(v_b_3765_);
                    lean_inc(v_head_3766_);
                    lean_inc_ref(v_cmp_3763_);
                    v___x_3768_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_3763_, v_head_3766_, v_b_3765_);
                    if v___x_3768_ == 0 {
                        v___x_3769_ = lean_box(0);
                        lean_inc(v_head_3766_);
                        lean_inc_ref(v_cmp_3763_);
                        v___x_3770_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_3763_, v_head_3766_, v___x_3769_, v_b_3765_);
                        v_as_x27_3764_ = v_tail_3767_;
                        v_b_3765_ = v___x_3770_;
                        state = 0;
                        continue;
                    } else {
                        v_as_x27_3764_ = v_tail_3767_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg___boxed(
    mut v_cmp_3773_: *mut LeanObject,
    mut v_as_x27_3774_: *mut LeanObject,
    mut v_b_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3776_: *mut LeanObject = core::ptr::null_mut();
    v_res_3776_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
        v_cmp_3773_,
        v_as_x27_3774_,
        v_b_3775_,
    );
    lean_dec(v_as_x27_3774_);
    return v_res_3776_;
}
pub unsafe fn l_Std_TreeSet_ofList___redArg(
    mut v_l_3777_: *mut LeanObject,
    mut v_cmp_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    v_r_3779_ = lean_box(1);
    v___x_3780_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
        v_cmp_3778_,
        v_l_3777_,
        v_r_3779_,
    );
    return v___x_3780_;
}
pub unsafe fn l_Std_TreeSet_ofList___redArg___boxed(
    mut v_l_3781_: *mut LeanObject,
    mut v_cmp_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3783_: *mut LeanObject = core::ptr::null_mut();
    v_res_3783_ = l_Std_TreeSet_ofList___redArg(v_l_3781_, v_cmp_3782_);
    lean_dec(v_l_3781_);
    return v_res_3783_;
}
pub unsafe fn l_Std_TreeSet_ofList(
    mut v_00_u03b1_3784_: *mut LeanObject,
    mut v_l_3785_: *mut LeanObject,
    mut v_cmp_3786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    v___x_3787_ = l_Std_TreeSet_ofList___redArg(v_l_3785_, v_cmp_3786_);
    return v___x_3787_;
}
pub unsafe fn l_Std_TreeSet_ofList___boxed(
    mut v_00_u03b1_3788_: *mut LeanObject,
    mut v_l_3789_: *mut LeanObject,
    mut v_cmp_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3791_: *mut LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Std_TreeSet_ofList(v_00_u03b1_3788_, v_l_3789_, v_cmp_3790_);
    lean_dec(v_l_3789_);
    return v_res_3791_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(
    mut v_00_u03b1_3792_: *mut LeanObject,
    mut v_cmp_3793_: *mut LeanObject,
    mut v_00_u03b2_3794_: *mut LeanObject,
    mut v_k_3795_: *mut LeanObject,
    mut v_t_3796_: *mut LeanObject,
) -> u8 {
    let mut v___x_3797_: u8 = 0;
    v___x_3797_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(
            v_cmp_3793_,
            v_k_3795_,
            v_t_3796_,
        );
    return v___x_3797_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___boxed(
    mut v_00_u03b1_3798_: *mut LeanObject,
    mut v_cmp_3799_: *mut LeanObject,
    mut v_00_u03b2_3800_: *mut LeanObject,
    mut v_k_3801_: *mut LeanObject,
    mut v_t_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3803_: u8 = 0;
    let mut v_r_3804_: *mut LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(
        v_00_u03b1_3798_,
        v_cmp_3799_,
        v_00_u03b2_3800_,
        v_k_3801_,
        v_t_3802_,
    );
    v_r_3804_ = lean_box((v_res_3803_) as usize);
    return v_r_3804_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(
    mut v_00_u03b1_3805_: *mut LeanObject,
    mut v_cmp_3806_: *mut LeanObject,
    mut v_00_u03b2_3807_: *mut LeanObject,
    mut v_k_3808_: *mut LeanObject,
    mut v_v_3809_: *mut LeanObject,
    mut v_t_3810_: *mut LeanObject,
    mut v_hl_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(
        v_cmp_3806_,
        v_k_3808_,
        v_v_3809_,
        v_t_3810_,
    );
    return v___x_3812_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(
    mut v_00_u03b1_3813_: *mut LeanObject,
    mut v_cmp_3814_: *mut LeanObject,
    mut v_as_3815_: *mut LeanObject,
    mut v_as_x27_3816_: *mut LeanObject,
    mut v_b_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v___x_3819_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
        v_cmp_3814_,
        v_as_x27_3816_,
        v_b_3817_,
    );
    return v___x_3819_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(
    mut v_00_u03b1_3820_: *mut LeanObject,
    mut v_cmp_3821_: *mut LeanObject,
    mut v_as_3822_: *mut LeanObject,
    mut v_as_x27_3823_: *mut LeanObject,
    mut v_b_3824_: *mut LeanObject,
    mut v_a_3825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3826_: *mut LeanObject = core::ptr::null_mut();
    v_res_3826_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(
        v_00_u03b1_3820_,
        v_cmp_3821_,
        v_as_3822_,
        v_as_x27_3823_,
        v_b_3824_,
        v_a_3825_,
    );
    lean_dec(v_as_x27_3823_);
    lean_dec(v_as_3822_);
    return v_res_3826_;
}
pub unsafe fn l_Std_TreeSet_toArray___redArg___lam__0(
    mut v_l_3827_: *mut LeanObject,
    mut v_k_3828_: *mut LeanObject,
    mut v_x_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = lean_array_push(v_l_3827_, v_k_3828_);
    return v___x_3830_;
}
pub unsafe fn l_Std_TreeSet_toArray___redArg(mut v_t_3832_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3833_ = l_Std_TreeSet_toArray___redArg___closed__0;
                if lean_obj_tag(v_t_3832_) == 0 {
                    v_size_3838_ = lean_ctor_get(v_t_3832_, 0);
                    lean_inc(v_size_3838_);
                    v___y_3835_ = v_size_3838_;
                    state = 1;
                    continue;
                } else {
                    v___x_3839_ = lean_unsigned_to_nat(0);
                    v___y_3835_ = v___x_3839_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3836_ = lean_mk_empty_array_with_capacity(v___y_3835_);
                lean_dec(v___y_3835_);
                v___x_3837_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3833_,
                    v___x_3836_,
                    v_t_3832_,
                );
                return v___x_3837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_toArray(
    mut v_00_u03b1_3840_: *mut LeanObject,
    mut v_cmp_3841_: *mut LeanObject,
    mut v_t_3842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3843_ = l_Std_TreeSet_toArray___redArg___closed__0;
                if lean_obj_tag(v_t_3842_) == 0 {
                    v_size_3848_ = lean_ctor_get(v_t_3842_, 0);
                    lean_inc(v_size_3848_);
                    v___y_3845_ = v_size_3848_;
                    state = 1;
                    continue;
                } else {
                    v___x_3849_ = lean_unsigned_to_nat(0);
                    v___y_3845_ = v___x_3849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3846_ = lean_mk_empty_array_with_capacity(v___y_3845_);
                lean_dec(v___y_3845_);
                v___x_3847_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3843_,
                    v___x_3846_,
                    v_t_3842_,
                );
                return v___x_3847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_toArray___boxed(
    mut v_00_u03b1_3850_: *mut LeanObject,
    mut v_cmp_3851_: *mut LeanObject,
    mut v_t_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3853_: *mut LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Std_TreeSet_toArray(v_00_u03b1_3850_, v_cmp_3851_, v_t_3852_);
    lean_dec_ref(v_cmp_3851_);
    return v_res_3853_;
}
pub unsafe fn _init_l_Std_TreeSet_ofArray___auto__1() -> *mut LeanObject {
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3854_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26_once),
        _init_l_Std_TreeSet___auto__1___closed__26,
    );
    return v___x_3854_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(
    mut v_cmp_3855_: *mut LeanObject,
    mut v_as_3856_: *mut LeanObject,
    mut v_sz_3857_: usize,
    mut v_i_3858_: usize,
    mut v_b_3859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: usize = 0;
    let mut v___x_3863_: usize = 0;
    let mut v___x_3865_: u8 = 0;
    let mut v_a_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3865_ = lean_usize_dec_lt(v_i_3858_, v_sz_3857_);
                if v___x_3865_ == 0 {
                    lean_dec_ref(v_cmp_3855_);
                    return v_b_3859_;
                } else {
                    v_a_3866_ = lean_array_uget_borrowed(v_as_3856_, v_i_3858_);
                    lean_inc(v_b_3859_);
                    lean_inc(v_a_3866_);
                    lean_inc_ref(v_cmp_3855_);
                    v___x_3867_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_3855_, v_a_3866_, v_b_3859_);
                    if v___x_3867_ == 0 {
                        v___x_3868_ = lean_box(0);
                        lean_inc(v_a_3866_);
                        lean_inc_ref(v_cmp_3855_);
                        v___x_3869_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_3855_, v_a_3866_, v___x_3868_, v_b_3859_);
                        v___y_3861_ = v___x_3869_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3861_ = v_b_3859_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3862_ = 1usize;
                v___x_3863_ = lean_usize_add(v_i_3858_, v___x_3862_);
                v_i_3858_ = v___x_3863_;
                v_b_3859_ = v___y_3861_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg___boxed(
    mut v_cmp_3870_: *mut LeanObject,
    mut v_as_3871_: *mut LeanObject,
    mut v_sz_3872_: *mut LeanObject,
    mut v_i_3873_: *mut LeanObject,
    mut v_b_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3875_: usize = 0;
    let mut v_i_boxed_3876_: usize = 0;
    let mut v_res_3877_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3872_);
    lean_dec(v_sz_3872_);
    v_i_boxed_3876_ = lean_unbox_usize(v_i_3873_);
    lean_dec(v_i_3873_);
    v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_3870_, v_as_3871_, v_sz_boxed_3875_, v_i_boxed_3876_, v_b_3874_);
    lean_dec_ref(v_as_3871_);
    return v_res_3877_;
}
pub unsafe fn l_Std_TreeSet_ofArray___redArg(
    mut v_a_3878_: *mut LeanObject,
    mut v_cmp_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3881_: usize = 0;
    let mut v___x_3882_: usize = 0;
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    v_r_3880_ = lean_box(1);
    v_sz_3881_ = lean_array_size(v_a_3878_);
    v___x_3882_ = 0usize;
    v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_3879_, v_a_3878_, v_sz_3881_, v___x_3882_, v_r_3880_);
    return v___x_3883_;
}
pub unsafe fn l_Std_TreeSet_ofArray___redArg___boxed(
    mut v_a_3884_: *mut LeanObject,
    mut v_cmp_3885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3886_: *mut LeanObject = core::ptr::null_mut();
    v_res_3886_ = l_Std_TreeSet_ofArray___redArg(v_a_3884_, v_cmp_3885_);
    lean_dec_ref(v_a_3884_);
    return v_res_3886_;
}
pub unsafe fn l_Std_TreeSet_ofArray(
    mut v_00_u03b1_3887_: *mut LeanObject,
    mut v_a_3888_: *mut LeanObject,
    mut v_cmp_3889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    v___x_3890_ = l_Std_TreeSet_ofArray___redArg(v_a_3888_, v_cmp_3889_);
    return v___x_3890_;
}
pub unsafe fn l_Std_TreeSet_ofArray___boxed(
    mut v_00_u03b1_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_cmp_3893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3894_: *mut LeanObject = core::ptr::null_mut();
    v_res_3894_ = l_Std_TreeSet_ofArray(v_00_u03b1_3891_, v_a_3892_, v_cmp_3893_);
    lean_dec_ref(v_a_3892_);
    return v_res_3894_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(
    mut v_00_u03b1_3895_: *mut LeanObject,
    mut v_cmp_3896_: *mut LeanObject,
    mut v_as_3897_: *mut LeanObject,
    mut v_sz_3898_: usize,
    mut v_i_3899_: usize,
    mut v_b_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_3896_, v_as_3897_, v_sz_3898_, v_i_3899_, v_b_3900_);
    return v___x_3901_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(
    mut v_00_u03b1_3902_: *mut LeanObject,
    mut v_cmp_3903_: *mut LeanObject,
    mut v_as_3904_: *mut LeanObject,
    mut v_sz_3905_: *mut LeanObject,
    mut v_i_3906_: *mut LeanObject,
    mut v_b_3907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3908_: usize = 0;
    let mut v_i_boxed_3909_: usize = 0;
    let mut v_res_3910_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3908_ = lean_unbox_usize(v_sz_3905_);
    lean_dec(v_sz_3905_);
    v_i_boxed_3909_ = lean_unbox_usize(v_i_3906_);
    lean_dec(v_i_3906_);
    v_res_3910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(v_00_u03b1_3902_, v_cmp_3903_, v_as_3904_, v_sz_boxed_3908_, v_i_boxed_3909_, v_b_3907_);
    lean_dec_ref(v_as_3904_);
    return v_res_3910_;
}
pub unsafe fn l_Std_TreeSet_merge___redArg___lam__0(
    mut v_b_u2082_3913_: *mut LeanObject,
    mut v_x_3914_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3914_) == 0 {
        let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
        v___x_3915_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3915_, 0, v_b_u2082_3913_);
        return v___x_3915_;
    } else {
        let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
        v___x_3916_ = l_Std_TreeSet_merge___redArg___lam__0___closed__0;
        return v___x_3916_;
    }
}
pub unsafe fn l_Std_TreeSet_merge___redArg___lam__0___boxed(
    mut v_b_u2082_3917_: *mut LeanObject,
    mut v_x_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3919_: *mut LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Std_TreeSet_merge___redArg___lam__0(v_b_u2082_3917_, v_x_3918_);
    lean_dec(v_x_3918_);
    return v_res_3919_;
}
pub unsafe fn l_Std_TreeSet_merge___redArg___lam__1(
    mut v_cmp_3920_: *mut LeanObject,
    mut v_t_3921_: *mut LeanObject,
    mut v_a_3922_: *mut LeanObject,
    mut v_b_u2082_3923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    v___f_3924_ = lean_alloc_closure(
        l_Std_TreeSet_merge___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3924_, 0, v_b_u2082_3923_);
    v___x_3925_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_3920_,
        v_a_3922_,
        v___f_3924_,
        v_t_3921_,
    );
    return v___x_3925_;
}
pub unsafe fn l_Std_TreeSet_merge___redArg(
    mut v_cmp_3926_: *mut LeanObject,
    mut v_t_u2081_3927_: *mut LeanObject,
    mut v_t_u2082_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    v___f_3929_ = lean_alloc_closure(
        l_Std_TreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3929_, 0, v_cmp_3926_);
    v___x_3930_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3929_, v_t_u2081_3927_, v_t_u2082_3928_);
    return v___x_3930_;
}
pub unsafe fn l_Std_TreeSet_merge(
    mut v_00_u03b1_3931_: *mut LeanObject,
    mut v_cmp_3932_: *mut LeanObject,
    mut v_t_u2081_3933_: *mut LeanObject,
    mut v_t_u2082_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    v___f_3935_ = lean_alloc_closure(
        l_Std_TreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3935_, 0, v_cmp_3932_);
    v___x_3936_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3935_, v_t_u2081_3933_, v_t_u2082_3934_);
    return v___x_3936_;
}
pub unsafe fn l_Std_TreeSet_insertMany___redArg___lam__0(
    mut v_cmp_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_____s_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3940_: u8 = 0;
    lean_inc(v_____s_3939_);
    lean_inc(v_a_3938_);
    lean_inc_ref(v_cmp_3937_);
    v___x_3940_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3937_, v_a_3938_, v_____s_3939_);
    if v___x_3940_ == 0 {
        let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
        v___x_3941_ = lean_box(0);
        v___x_3942_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_3937_,
            v_a_3938_,
            v___x_3941_,
            v_____s_3939_,
        );
        v___x_3943_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3943_, 0, v___x_3942_);
        return v___x_3943_;
    } else {
        let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_3938_);
        lean_dec_ref(v_cmp_3937_);
        v___x_3944_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3944_, 0, v_____s_3939_);
        return v___x_3944_;
    }
}
pub unsafe fn l_Std_TreeSet_insertMany___redArg(
    mut v_cmp_3945_: *mut LeanObject,
    mut v_inst_3946_: *mut LeanObject,
    mut v_t_3947_: *mut LeanObject,
    mut v_l_3948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    v___f_3949_ = lean_alloc_closure(
        l_Std_TreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3949_, 0, v_cmp_3945_);
    v___x_3950_ = lean_apply_4(v_inst_3946_, lean_box(0), v_l_3948_, v_t_3947_, v___f_3949_);
    return v___x_3950_;
}
pub unsafe fn l_Std_TreeSet_insertMany(
    mut v_00_u03b1_3951_: *mut LeanObject,
    mut v_cmp_3952_: *mut LeanObject,
    mut v_00_u03c1_3953_: *mut LeanObject,
    mut v_inst_3954_: *mut LeanObject,
    mut v_t_3955_: *mut LeanObject,
    mut v_l_3956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    v___f_3957_ = lean_alloc_closure(
        l_Std_TreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3957_, 0, v_cmp_3952_);
    v___x_3958_ = lean_apply_4(v_inst_3954_, lean_box(0), v_l_3956_, v_t_3955_, v___f_3957_);
    return v___x_3958_;
}
pub unsafe fn l_Std_TreeSet_union___redArg(
    mut v_cmp_3959_: *mut LeanObject,
    mut v_t_u2081_3960_: *mut LeanObject,
    mut v_t_u2082_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    v___x_3962_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3959_,
        v_t_u2081_3960_,
        v_t_u2082_3961_,
    );
    return v___x_3962_;
}
pub unsafe fn l_Std_TreeSet_union(
    mut v_00_u03b1_3963_: *mut LeanObject,
    mut v_cmp_3964_: *mut LeanObject,
    mut v_t_u2081_3965_: *mut LeanObject,
    mut v_t_u2082_3966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    v___x_3967_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3964_,
        v_t_u2081_3965_,
        v_t_u2082_3966_,
    );
    return v___x_3967_;
}
pub unsafe fn l_Std_TreeSet_instUnion___redArg(
    mut v_cmp_3968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    v___x_3969_ = lean_alloc_closure(l_Std_TreeSet_union as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3969_, 0, lean_box(0));
    lean_closure_set(v___x_3969_, 1, v_cmp_3968_);
    return v___x_3969_;
}
pub unsafe fn l_Std_TreeSet_instUnion(
    mut v_00_u03b1_3970_: *mut LeanObject,
    mut v_cmp_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    v___x_3972_ = lean_alloc_closure(l_Std_TreeSet_union as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3972_, 0, lean_box(0));
    lean_closure_set(v___x_3972_, 1, v_cmp_3971_);
    return v___x_3972_;
}
pub unsafe fn l_Std_TreeSet_inter___redArg(
    mut v_cmp_3973_: *mut LeanObject,
    mut v_t_u2081_3974_: *mut LeanObject,
    mut v_t_u2082_3975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    v___x_3976_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3973_,
        v_t_u2081_3974_,
        v_t_u2082_3975_,
    );
    return v___x_3976_;
}
pub unsafe fn l_Std_TreeSet_inter(
    mut v_00_u03b1_3977_: *mut LeanObject,
    mut v_cmp_3978_: *mut LeanObject,
    mut v_t_u2081_3979_: *mut LeanObject,
    mut v_t_u2082_3980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    v___x_3981_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3978_,
        v_t_u2081_3979_,
        v_t_u2082_3980_,
    );
    return v___x_3981_;
}
pub unsafe fn l_Std_TreeSet_instInter___redArg(
    mut v_cmp_3982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    v___x_3983_ = lean_alloc_closure(l_Std_TreeSet_inter as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3983_, 0, lean_box(0));
    lean_closure_set(v___x_3983_, 1, v_cmp_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Std_TreeSet_instInter(
    mut v_00_u03b1_3984_: *mut LeanObject,
    mut v_cmp_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    v___x_3986_ = lean_alloc_closure(l_Std_TreeSet_inter as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3986_, 0, lean_box(0));
    lean_closure_set(v___x_3986_, 1, v_cmp_3985_);
    return v___x_3986_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_cmp_3987_: *mut LeanObject,
    mut v_t_3988_: *mut LeanObject,
    mut v_k_3989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3988_) == 0 {
                    v_k_3990_ = lean_ctor_get(v_t_3988_, 1);
                    lean_inc(v_k_3990_);
                    v_v_3991_ = lean_ctor_get(v_t_3988_, 2);
                    lean_inc(v_v_3991_);
                    v_l_3992_ = lean_ctor_get(v_t_3988_, 3);
                    lean_inc(v_l_3992_);
                    v_r_3993_ = lean_ctor_get(v_t_3988_, 4);
                    lean_inc(v_r_3993_);
                    lean_dec_ref_known(v_t_3988_, 5);
                    lean_inc_ref(v_cmp_3987_);
                    lean_inc(v_k_3989_);
                    v___x_3994_ = lean_apply_2(v_cmp_3987_, v_k_3989_, v_k_3990_);
                    v___x_3995_ = (lean_unbox(v___x_3994_) as u8);
                    match v___x_3995_ {
                        0 => {
                            lean_dec(v_r_3993_);
                            lean_dec(v_v_3991_);
                            v_t_3988_ = v_l_3992_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_3993_);
                            lean_dec(v_l_3992_);
                            lean_dec(v_k_3989_);
                            lean_dec_ref(v_cmp_3987_);
                            v___x_3997_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3997_, 0, v_v_3991_);
                            return v___x_3997_;
                        }
                        _ => {
                            lean_dec(v_l_3992_);
                            lean_dec(v_v_3991_);
                            v_t_3988_ = v_r_3993_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_3989_);
                    lean_dec_ref(v_cmp_3987_);
                    v___x_3999_ = lean_box(0);
                    return v___x_3999_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(
    mut v_x_4000_: *mut LeanObject,
    mut v_x_4001_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4000_) == 0 {
        if lean_obj_tag(v_x_4001_) == 0 {
            let mut v___x_4002_: u8 = 0;
            v___x_4002_ = 1;
            return v___x_4002_;
        } else {
            let mut v___x_4003_: u8 = 0;
            v___x_4003_ = 0;
            return v___x_4003_;
        }
    } else {
        if lean_obj_tag(v_x_4001_) == 0 {
            let mut v___x_4004_: u8 = 0;
            v___x_4004_ = 0;
            return v___x_4004_;
        } else {
            let mut v___x_4005_: u8 = 0;
            v___x_4005_ = 1;
            return v___x_4005_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_x_4006_: *mut LeanObject,
    mut v_x_4007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4008_: u8 = 0;
    let mut v_r_4009_: *mut LeanObject = core::ptr::null_mut();
    v_res_4008_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_4006_, v_x_4007_);
    lean_dec(v_x_4007_);
    lean_dec(v_x_4006_);
    v_r_4009_ = lean_box((v_res_4008_) as usize);
    return v_r_4009_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_cmp_4010_: *mut LeanObject,
    mut v_t_u2082_4011_: *mut LeanObject,
    mut v_init_4012_: *mut LeanObject,
    mut v_x_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: u8 = 0;
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut v_unused_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4013_) == 0 {
                    v_k_4014_ = lean_ctor_get(v_x_4013_, 1);
                    lean_inc(v_k_4014_);
                    v_v_4015_ = lean_ctor_get(v_x_4013_, 2);
                    lean_inc(v_v_4015_);
                    v_l_4016_ = lean_ctor_get(v_x_4013_, 3);
                    lean_inc(v_l_4016_);
                    v_r_4017_ = lean_ctor_get(v_x_4013_, 4);
                    lean_inc(v_r_4017_);
                    lean_dec_ref_known(v_x_4013_, 5);
                    lean_inc(v_t_u2082_4011_);
                    lean_inc_ref(v_cmp_4010_);
                    v___x_4018_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_4010_, v_t_u2082_4011_, v_init_4012_, v_l_4016_);
                    if lean_obj_tag(v___x_4018_) == 0 {
                        lean_dec(v_r_4017_);
                        lean_dec(v_v_4015_);
                        lean_dec(v_k_4014_);
                        lean_dec(v_t_u2082_4011_);
                        lean_dec_ref(v_cmp_4010_);
                        return v___x_4018_;
                    } else {
                        v_isSharedCheck_4034_ = (!lean_is_exclusive(v___x_4018_)) as u8;
                        if v_isSharedCheck_4034_ == 0 {
                            v_unused_4035_ = lean_ctor_get(v___x_4018_, 0);
                            lean_dec(v_unused_4035_);
                            v___x_4020_ = v___x_4018_;
                            v_isShared_4021_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4018_);
                            v___x_4020_ = lean_box(0);
                            v_isShared_4021_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_t_u2082_4011_);
                    lean_dec_ref(v_cmp_4010_);
                    v___x_4036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4036_, 0, v_init_4012_);
                    return v___x_4036_;
                }
            }
            1 => {
                v___x_4022_ = lean_box(0);
                lean_inc(v_t_u2082_4011_);
                lean_inc_ref(v_cmp_4010_);
                v___x_4023_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_4010_, v_t_u2082_4011_, v_k_4014_);
                v___x_4024_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4024_, 0, v_v_4015_);
                v___x_4025_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v___x_4023_, v___x_4024_);
                lean_dec_ref_known(v___x_4024_, 1);
                lean_dec(v___x_4023_);
                if v___x_4025_ == 0 {
                    lean_dec(v_r_4017_);
                    lean_dec(v_t_u2082_4011_);
                    lean_dec_ref(v_cmp_4010_);
                    v___x_4026_ = lean_box((v___x_4025_) as usize);
                    v___x_4027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4027_, 0, v___x_4026_);
                    v___x_4028_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4028_, 0, v___x_4027_);
                    lean_ctor_set(v___x_4028_, 1, v___x_4022_);
                    if v_isShared_4021_ == 0 {
                        lean_ctor_set_tag(v___x_4020_, 0);
                        lean_ctor_set(v___x_4020_, 0, v___x_4028_);
                        v___x_4030_ = v___x_4020_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
                        v___x_4030_ = v_reuseFailAlloc_4031_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4020_);
                    v___x_4032_ = l_Std_TreeSet_any___redArg___closed__0;
                    v_init_4012_ = v___x_4032_;
                    v_x_4013_ = v_r_4017_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_4030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(
    mut v_cmp_4037_: *mut LeanObject,
    mut v_t_u2081_4038_: *mut LeanObject,
    mut v_t_u2082_4039_: *mut LeanObject,
) -> u8 {
    let mut v___y_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u8 = 0;
    let mut v_val_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: u8 = 0;
    let mut v___y_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_u2081_4038_) == 0 {
                    v_size_4057_ = lean_ctor_get(v_t_u2081_4038_, 0);
                    lean_inc(v_size_4057_);
                    v___y_4054_ = v_size_4057_;
                    state = 3;
                    continue;
                } else {
                    v___x_4058_ = lean_unsigned_to_nat(0);
                    v___y_4054_ = v___x_4058_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_fst_4042_ = lean_ctor_get(v___y_4041_, 0);
                lean_inc(v_fst_4042_);
                lean_dec_ref(v___y_4041_);
                if lean_obj_tag(v_fst_4042_) == 0 {
                    v___x_4043_ = 1;
                    return v___x_4043_;
                } else {
                    v_val_4044_ = lean_ctor_get(v_fst_4042_, 0);
                    lean_inc(v_val_4044_);
                    lean_dec_ref_known(v_fst_4042_, 1);
                    v___x_4045_ = (lean_unbox(v_val_4044_) as u8);
                    lean_dec(v_val_4044_);
                    return v___x_4045_;
                }
            }
            2 => {
                v___x_4049_ = lean_nat_dec_eq(v___y_4047_, v___y_4048_);
                lean_dec(v___y_4048_);
                lean_dec(v___y_4047_);
                if v___x_4049_ == 0 {
                    lean_dec(v_t_u2082_4039_);
                    lean_dec(v_t_u2081_4038_);
                    lean_dec_ref(v_cmp_4037_);
                    return v___x_4049_;
                } else {
                    v___x_4050_ = l_Std_TreeSet_any___redArg___closed__0;
                    v___x_4051_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_4037_, v_t_u2082_4039_, v___x_4050_, v_t_u2081_4038_);
                    v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
                    lean_inc(v_a_4052_);
                    lean_dec_ref(v___x_4051_);
                    v___y_4041_ = v_a_4052_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_t_u2082_4039_) == 0 {
                    v_size_4055_ = lean_ctor_get(v_t_u2082_4039_, 0);
                    lean_inc(v_size_4055_);
                    v___y_4047_ = v___y_4054_;
                    v___y_4048_ = v_size_4055_;
                    state = 2;
                    continue;
                } else {
                    v___x_4056_ = lean_unsigned_to_nat(0);
                    v___y_4047_ = v___y_4054_;
                    v___y_4048_ = v___x_4056_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_cmp_4059_: *mut LeanObject,
    mut v_t_u2081_4060_: *mut LeanObject,
    mut v_t_u2082_4061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4062_: u8 = 0;
    let mut v_r_4063_: *mut LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4059_, v_t_u2081_4060_, v_t_u2082_4061_);
    v_r_4063_ = lean_box((v_res_4062_) as usize);
    return v_r_4063_;
}
pub unsafe fn l_Std_TreeSet_beq___redArg(
    mut v_cmp_4064_: *mut LeanObject,
    mut v_t_u2081_4065_: *mut LeanObject,
    mut v_t_u2082_4066_: *mut LeanObject,
) -> u8 {
    let mut v___x_4067_: u8 = 0;
    v___x_4067_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4064_, v_t_u2081_4065_, v_t_u2082_4066_);
    return v___x_4067_;
}
pub unsafe fn l_Std_TreeSet_beq___redArg___boxed(
    mut v_cmp_4068_: *mut LeanObject,
    mut v_t_u2081_4069_: *mut LeanObject,
    mut v_t_u2082_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4071_: u8 = 0;
    let mut v_r_4072_: *mut LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Std_TreeSet_beq___redArg(v_cmp_4068_, v_t_u2081_4069_, v_t_u2082_4070_);
    v_r_4072_ = lean_box((v_res_4071_) as usize);
    return v_r_4072_;
}
pub unsafe fn l_Std_TreeSet_beq(
    mut v_00_u03b1_4073_: *mut LeanObject,
    mut v_cmp_4074_: *mut LeanObject,
    mut v_t_u2081_4075_: *mut LeanObject,
    mut v_t_u2082_4076_: *mut LeanObject,
) -> u8 {
    let mut v___x_4077_: u8 = 0;
    v___x_4077_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4074_, v_t_u2081_4075_, v_t_u2082_4076_);
    return v___x_4077_;
}
pub unsafe fn l_Std_TreeSet_beq___boxed(
    mut v_00_u03b1_4078_: *mut LeanObject,
    mut v_cmp_4079_: *mut LeanObject,
    mut v_t_u2081_4080_: *mut LeanObject,
    mut v_t_u2082_4081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4082_: u8 = 0;
    let mut v_r_4083_: *mut LeanObject = core::ptr::null_mut();
    v_res_4082_ = l_Std_TreeSet_beq(
        v_00_u03b1_4078_,
        v_cmp_4079_,
        v_t_u2081_4080_,
        v_t_u2082_4081_,
    );
    v_r_4083_ = lean_box((v_res_4082_) as usize);
    return v_r_4083_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(
    mut v_cmp_4084_: *mut LeanObject,
    mut v_t_u2081_4085_: *mut LeanObject,
    mut v_t_u2082_4086_: *mut LeanObject,
) -> u8 {
    let mut v___x_4087_: u8 = 0;
    v___x_4087_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4084_, v_t_u2081_4085_, v_t_u2082_4086_);
    return v___x_4087_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(
    mut v_cmp_4088_: *mut LeanObject,
    mut v_t_u2081_4089_: *mut LeanObject,
    mut v_t_u2082_4090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4091_: u8 = 0;
    let mut v_r_4092_: *mut LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(
        v_cmp_4088_,
        v_t_u2081_4089_,
        v_t_u2082_4090_,
    );
    v_r_4092_ = lean_box((v_res_4091_) as usize);
    return v_r_4092_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(
    mut v_00_u03b1_4093_: *mut LeanObject,
    mut v_cmp_4094_: *mut LeanObject,
    mut v_t_u2081_4095_: *mut LeanObject,
    mut v_t_u2082_4096_: *mut LeanObject,
) -> u8 {
    let mut v___x_4097_: u8 = 0;
    v___x_4097_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4094_, v_t_u2081_4095_, v_t_u2082_4096_);
    return v___x_4097_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(
    mut v_00_u03b1_4098_: *mut LeanObject,
    mut v_cmp_4099_: *mut LeanObject,
    mut v_t_u2081_4100_: *mut LeanObject,
    mut v_t_u2082_4101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4102_: u8 = 0;
    let mut v_r_4103_: *mut LeanObject = core::ptr::null_mut();
    v_res_4102_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(
        v_00_u03b1_4098_,
        v_cmp_4099_,
        v_t_u2081_4100_,
        v_t_u2082_4101_,
    );
    v_r_4103_ = lean_box((v_res_4102_) as usize);
    return v_r_4103_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(
    mut v_cmp_4104_: *mut LeanObject,
    mut v_t_u2081_4105_: *mut LeanObject,
    mut v_t_u2082_4106_: *mut LeanObject,
) -> u8 {
    let mut v___x_4107_: u8 = 0;
    v___x_4107_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4104_, v_t_u2081_4105_, v_t_u2082_4106_);
    return v___x_4107_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(
    mut v_cmp_4108_: *mut LeanObject,
    mut v_t_u2081_4109_: *mut LeanObject,
    mut v_t_u2082_4110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4111_: u8 = 0;
    let mut v_r_4112_: *mut LeanObject = core::ptr::null_mut();
    v_res_4111_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_4108_, v_t_u2081_4109_, v_t_u2082_4110_);
    v_r_4112_ = lean_box((v_res_4111_) as usize);
    return v_r_4112_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(
    mut v_00_u03b1_4113_: *mut LeanObject,
    mut v_cmp_4114_: *mut LeanObject,
    mut v_t_u2081_4115_: *mut LeanObject,
    mut v_t_u2082_4116_: *mut LeanObject,
) -> u8 {
    let mut v___x_4117_: u8 = 0;
    v___x_4117_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4114_, v_t_u2081_4115_, v_t_u2082_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(
    mut v_00_u03b1_4118_: *mut LeanObject,
    mut v_cmp_4119_: *mut LeanObject,
    mut v_t_u2081_4120_: *mut LeanObject,
    mut v_t_u2082_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4122_: u8 = 0;
    let mut v_r_4123_: *mut LeanObject = core::ptr::null_mut();
    v_res_4122_ =
        l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(
            v_00_u03b1_4118_,
            v_cmp_4119_,
            v_t_u2081_4120_,
            v_t_u2082_4121_,
        );
    v_r_4123_ = lean_box((v_res_4122_) as usize);
    return v_r_4123_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4124_: *mut LeanObject,
    mut v_cmp_4125_: *mut LeanObject,
    mut v_t_u2081_4126_: *mut LeanObject,
    mut v_t_u2082_4127_: *mut LeanObject,
) -> u8 {
    let mut v___x_4128_: u8 = 0;
    v___x_4128_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4125_, v_t_u2081_4126_, v_t_u2082_4127_);
    return v___x_4128_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4129_: *mut LeanObject,
    mut v_cmp_4130_: *mut LeanObject,
    mut v_t_u2081_4131_: *mut LeanObject,
    mut v_t_u2082_4132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4133_: u8 = 0;
    let mut v_r_4134_: *mut LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(v_00_u03b1_4129_, v_cmp_4130_, v_t_u2081_4131_, v_t_u2082_4132_);
    v_r_4134_ = lean_box((v_res_4133_) as usize);
    return v_r_4134_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4135_: *mut LeanObject,
    mut v_cmp_4136_: *mut LeanObject,
    mut v_00_u03b4_4137_: *mut LeanObject,
    mut v_t_4138_: *mut LeanObject,
    mut v_k_4139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_4136_, v_t_4138_, v_k_4139_);
    return v___x_4140_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_4141_: *mut LeanObject,
    mut v_cmp_4142_: *mut LeanObject,
    mut v_t_u2082_4143_: *mut LeanObject,
    mut v_init_4144_: *mut LeanObject,
    mut v_x_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_4142_, v_t_u2082_4143_, v_init_4144_, v_x_4145_);
    return v___x_4146_;
}
pub unsafe fn l_Std_TreeSet_instBEq___redArg(mut v_cmp_4147_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    v___x_4148_ = lean_alloc_closure(l_Std_TreeSet_beq___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_4148_, 0, lean_box(0));
    lean_closure_set(v___x_4148_, 1, v_cmp_4147_);
    return v___x_4148_;
}
pub unsafe fn l_Std_TreeSet_instBEq(
    mut v_00_u03b1_4149_: *mut LeanObject,
    mut v_cmp_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    v___x_4151_ = lean_alloc_closure(l_Std_TreeSet_beq___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_4151_, 0, lean_box(0));
    lean_closure_set(v___x_4151_, 1, v_cmp_4150_);
    return v___x_4151_;
}
pub unsafe fn l_Std_TreeSet_diff___redArg(
    mut v_cmp_4152_: *mut LeanObject,
    mut v_t_u2081_4153_: *mut LeanObject,
    mut v_t_u2082_4154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    v___x_4155_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_4152_,
        v_t_u2081_4153_,
        v_t_u2082_4154_,
    );
    return v___x_4155_;
}
pub unsafe fn l_Std_TreeSet_diff(
    mut v_00_u03b1_4156_: *mut LeanObject,
    mut v_cmp_4157_: *mut LeanObject,
    mut v_t_u2081_4158_: *mut LeanObject,
    mut v_t_u2082_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_4157_,
        v_t_u2081_4158_,
        v_t_u2082_4159_,
    );
    return v___x_4160_;
}
pub unsafe fn l_Std_TreeSet_instSDiff___redArg(
    mut v_cmp_4161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162_ = lean_alloc_closure(l_Std_TreeSet_diff as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_4162_, 0, lean_box(0));
    lean_closure_set(v___x_4162_, 1, v_cmp_4161_);
    return v___x_4162_;
}
pub unsafe fn l_Std_TreeSet_instSDiff(
    mut v_00_u03b1_4163_: *mut LeanObject,
    mut v_cmp_4164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    v___x_4165_ = lean_alloc_closure(l_Std_TreeSet_diff as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_4165_, 0, lean_box(0));
    lean_closure_set(v___x_4165_, 1, v_cmp_4164_);
    return v___x_4165_;
}
pub unsafe fn l_Std_TreeSet_eraseMany___redArg___lam__0(
    mut v_cmp_4166_: *mut LeanObject,
    mut v_a_4167_: *mut LeanObject,
    mut v_____s_4168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    v_r_4169_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4166_, v_a_4167_, v_____s_4168_);
    v___x_4170_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4170_, 0, v_r_4169_);
    return v___x_4170_;
}
pub unsafe fn l_Std_TreeSet_eraseMany___redArg(
    mut v_cmp_4171_: *mut LeanObject,
    mut v_inst_4172_: *mut LeanObject,
    mut v_t_4173_: *mut LeanObject,
    mut v_l_4174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    v___f_4175_ = lean_alloc_closure(
        l_Std_TreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4175_, 0, v_cmp_4171_);
    v___x_4176_ = lean_apply_4(v_inst_4172_, lean_box(0), v_l_4174_, v_t_4173_, v___f_4175_);
    return v___x_4176_;
}
pub unsafe fn l_Std_TreeSet_eraseMany(
    mut v_00_u03b1_4177_: *mut LeanObject,
    mut v_cmp_4178_: *mut LeanObject,
    mut v_00_u03c1_4179_: *mut LeanObject,
    mut v_inst_4180_: *mut LeanObject,
    mut v_t_4181_: *mut LeanObject,
    mut v_l_4182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    v___f_4183_ = lean_alloc_closure(
        l_Std_TreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4183_, 0, v_cmp_4178_);
    v___x_4184_ = lean_apply_4(v_inst_4180_, lean_box(0), v_l_4182_, v_t_4181_, v___f_4183_);
    return v___x_4184_;
}
pub unsafe fn l_Std_TreeSet_instRepr___redArg___lam__1(
    mut v___f_4188_: *mut LeanObject,
    mut v_inst_4189_: *mut LeanObject,
    mut v_m_4190_: *mut LeanObject,
    mut v_prec_4191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    v___x_4192_ = l_Std_TreeSet_instRepr___redArg___lam__1___closed__1;
    v___x_4193_ = lean_box(0);
    v___x_4194_ = l_Std_TreeSet_foldr___redArg___closed__9;
    v___x_4195_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4194_,
        v___f_4188_,
        v___x_4193_,
        v_m_4190_,
    );
    v___x_4196_ = l_List_repr___redArg(v_inst_4189_, v___x_4195_);
    v___x_4197_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4197_, 0, v___x_4192_);
    lean_ctor_set(v___x_4197_, 1, v___x_4196_);
    v___x_4198_ = l_Repr_addAppParen(v___x_4197_, v_prec_4191_);
    return v___x_4198_;
}
pub unsafe fn l_Std_TreeSet_instRepr___redArg___lam__1___boxed(
    mut v___f_4199_: *mut LeanObject,
    mut v_inst_4200_: *mut LeanObject,
    mut v_m_4201_: *mut LeanObject,
    mut v_prec_4202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4203_: *mut LeanObject = core::ptr::null_mut();
    v_res_4203_ = l_Std_TreeSet_instRepr___redArg___lam__1(
        v___f_4199_,
        v_inst_4200_,
        v_m_4201_,
        v_prec_4202_,
    );
    lean_dec(v_prec_4202_);
    return v_res_4203_;
}
pub unsafe fn l_Std_TreeSet_instRepr___redArg(
    mut v_inst_4204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4206_: *mut LeanObject = core::ptr::null_mut();
    v___f_4205_ = l_Std_TreeSet_toList___redArg___closed__0;
    v___f_4206_ = lean_alloc_closure(
        l_Std_TreeSet_instRepr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_4206_, 0, v___f_4205_);
    lean_closure_set(v___f_4206_, 1, v_inst_4204_);
    return v___f_4206_;
}
pub unsafe fn l_Std_TreeSet_instRepr(
    mut v_00_u03b1_4207_: *mut LeanObject,
    mut v_cmp_4208_: *mut LeanObject,
    mut v_inst_4209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    v___x_4210_ = l_Std_TreeSet_instRepr___redArg(v_inst_4209_);
    return v___x_4210_;
}
pub unsafe fn l_Std_TreeSet_instRepr___boxed(
    mut v_00_u03b1_4211_: *mut LeanObject,
    mut v_cmp_4212_: *mut LeanObject,
    mut v_inst_4213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4214_: *mut LeanObject = core::ptr::null_mut();
    v_res_4214_ = l_Std_TreeSet_instRepr(v_00_u03b1_4211_, v_cmp_4212_, v_inst_4213_);
    lean_dec_ref(v_cmp_4212_);
    return v_res_4214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeSet___auto__1 = _init_l_Std_TreeSet___auto__1();
    lean_mark_persistent(l_Std_TreeSet___auto__1);
    l_Std_TreeSet_ofList___auto__1 = _init_l_Std_TreeSet_ofList___auto__1();
    lean_mark_persistent(l_Std_TreeSet_ofList___auto__1);
    l_Std_TreeSet_ofArray___auto__1 = _init_l_Std_TreeSet_ofArray___auto__1();
    lean_mark_persistent(l_Std_TreeSet_ofArray___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Basic(builtin);
}
