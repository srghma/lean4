// Lean compiler output
// Module: Std.Data.ExtTreeSet.Basic
// Imports: Std.Data.ExtTreeMap.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_alter___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_beq___redArg, l_Std_DTreeMap_Internal_Impl_erase___redArg,
    l_Std_DTreeMap_Internal_Impl_filter___redArg, l_Std_DTreeMap_Internal_Impl_insert___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_contains___redArg, l_Std_DTreeMap_Internal_Impl_foldl___redArg,
    l_Std_DTreeMap_Internal_Impl_foldlM___redArg, l_Std_DTreeMap_Internal_Impl_foldrM___redArg,
    l_Std_DTreeMap_Internal_Impl_forInStep___redArg, l_Std_DTreeMap_Internal_Impl_getKey___redArg,
    l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyD___redArg, l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg,
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
use crate::r#gen::Std::Data::ExtTreeMap::Basic::{
    initialize_Std_Data_ExtTreeMap_Basic, runtime_initialize_Std_Data_ExtTreeMap_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_nat_mul, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Std_ExtTreeSet___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__3_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__3_value) as *mut LeanObject;
static l_Std_ExtTreeSet___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_ExtTreeSet___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_ExtTreeSet___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_ExtTreeSet___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__6_value) as *mut LeanObject;
static l_Std_ExtTreeSet___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_ExtTreeSet___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_ExtTreeSet___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_ExtTreeSet___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__10_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__10_value) as *mut LeanObject;
static l_Std_ExtTreeSet___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_ExtTreeSet___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_ExtTreeSet___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_ExtTreeSet___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__10_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Std_ExtTreeSet___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet___auto__1___closed__14_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__14_value) as *mut LeanObject;
static mut l_Std_ExtTreeSet___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet___auto__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__14_value) as *mut LeanObject,
        16710690322389477741 as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__17_value) as *mut LeanObject;
static mut l_Std_ExtTreeSet___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_ExtTreeSet___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet_getGE_x21___redArg___closed__0_value: LeanStringObject<26> =
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
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_getGE_x21___redArg___closed__1_value: LeanStringObject<12> =
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
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_getGE_x21___redArg___closed__2_value: LeanStringObject<14> =
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
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet_foldr___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_ExtTreeSet_foldr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Std_ExtTreeSet_foldr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Std_ExtTreeSet_foldr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Std_ExtTreeSet_foldr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Std_ExtTreeSet_foldr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Std_ExtTreeSet_foldr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Std_ExtTreeSet_foldr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet_foldr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet_foldr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_ExtTreeSet_foldr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_partition___redArg___closed__0_value: LeanCtorObject<2> =
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
static mut l_Std_ExtTreeSet_partition___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_partition___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_any___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Std_ExtTreeSet_any___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_any___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_ExtTreeSet_toList___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeSet_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_toList___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_Std_ExtTreeSet_ofList___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet_toArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeSet_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_Std_ExtTreeSet_ofArray___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 69, 120, 116, 84, 114, 101, 101, 83, 101, 116, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1_value: LeanCtorObject<
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
        l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Std_ExtTreeSet___auto__1___closed__10;
    v___x_2044_ = l_Lean_mkAtom(v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    v___x_2045_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__12_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__12,
    );
    v___x_2046_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2047_ = lean_array_push(v___x_2046_, v___x_2045_);
    return v___x_2047_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Std_ExtTreeSet___auto__1___closed__14;
    v___x_2050_ = lean_string_utf8_byte_size(v___x_2049_);
    return v___x_2050_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    v___x_2051_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__15_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__15,
    );
    v___x_2052_ = lean_unsigned_to_nat(0);
    v___x_2053_ = l_Std_ExtTreeSet___auto__1___closed__14;
    v___x_2054_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2054_, 0, v___x_2053_);
    lean_ctor_set(v___x_2054_, 1, v___x_2052_);
    lean_ctor_set(v___x_2054_, 2, v___x_2051_);
    return v___x_2054_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    v___x_2057_ = lean_box(0);
    v___x_2058_ = l_Std_ExtTreeSet___auto__1___closed__17;
    v___x_2059_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__16_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__16,
    );
    v___x_2060_ = lean_box(2);
    v___x_2061_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_2061_, 0, v___x_2060_);
    lean_ctor_set(v___x_2061_, 1, v___x_2059_);
    lean_ctor_set(v___x_2061_, 2, v___x_2058_);
    lean_ctor_set(v___x_2061_, 3, v___x_2057_);
    return v___x_2061_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    v___x_2062_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__18_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__18,
    );
    v___x_2063_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__13_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__13,
    );
    v___x_2064_ = lean_array_push(v___x_2063_, v___x_2062_);
    return v___x_2064_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__19_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__19,
    );
    v___x_2066_ = l_Std_ExtTreeSet___auto__1___closed__11;
    v___x_2067_ = lean_box(2);
    v___x_2068_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2068_, 0, v___x_2067_);
    lean_ctor_set(v___x_2068_, 1, v___x_2066_);
    lean_ctor_set(v___x_2068_, 2, v___x_2065_);
    return v___x_2068_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    v___x_2069_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__20_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__20,
    );
    v___x_2070_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2071_ = lean_array_push(v___x_2070_, v___x_2069_);
    return v___x_2071_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v___x_2072_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__21_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__21,
    );
    v___x_2073_ = l_Std_ExtTreeSet___auto__1___closed__9;
    v___x_2074_ = lean_box(2);
    v___x_2075_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2075_, 0, v___x_2074_);
    lean_ctor_set(v___x_2075_, 1, v___x_2073_);
    lean_ctor_set(v___x_2075_, 2, v___x_2072_);
    return v___x_2075_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    v___x_2076_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__22_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__22,
    );
    v___x_2077_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2078_ = lean_array_push(v___x_2077_, v___x_2076_);
    return v___x_2078_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    v___x_2079_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__23_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__23,
    );
    v___x_2080_ = l_Std_ExtTreeSet___auto__1___closed__7;
    v___x_2081_ = lean_box(2);
    v___x_2082_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2082_, 0, v___x_2081_);
    lean_ctor_set(v___x_2082_, 1, v___x_2080_);
    lean_ctor_set(v___x_2082_, 2, v___x_2079_);
    return v___x_2082_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    v___x_2083_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__24_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__24,
    );
    v___x_2084_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2085_ = lean_array_push(v___x_2084_, v___x_2083_);
    return v___x_2085_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    v___x_2086_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__25_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__25,
    );
    v___x_2087_ = l_Std_ExtTreeSet___auto__1___closed__4;
    v___x_2088_ = lean_box(2);
    v___x_2089_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2089_, 0, v___x_2088_);
    lean_ctor_set(v___x_2089_, 1, v___x_2087_);
    lean_ctor_set(v___x_2089_, 2, v___x_2086_);
    return v___x_2089_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1() -> *mut LeanObject {
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___x_2090_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__26,
    );
    return v___x_2090_;
}
pub unsafe fn l_Std_ExtTreeSet_empty(
    mut v_00_u03b1_2091_: *mut LeanObject,
    mut v_cmp_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    v___x_2093_ = lean_box(1);
    return v___x_2093_;
}
pub unsafe fn l_Std_ExtTreeSet_empty___boxed(
    mut v_00_u03b1_2094_: *mut LeanObject,
    mut v_cmp_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2096_: *mut LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Std_ExtTreeSet_empty(v_00_u03b1_2094_, v_cmp_2095_);
    lean_dec_ref(v_cmp_2095_);
    return v_res_2096_;
}
pub unsafe fn l_Std_ExtTreeSet_instEmptyCollection(
    mut v_00_u03b1_2097_: *mut LeanObject,
    mut v_cmp_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    v___x_2099_ = lean_box(1);
    return v___x_2099_;
}
pub unsafe fn l_Std_ExtTreeSet_instEmptyCollection___boxed(
    mut v_00_u03b1_2100_: *mut LeanObject,
    mut v_cmp_2101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2102_: *mut LeanObject = core::ptr::null_mut();
    v_res_2102_ = l_Std_ExtTreeSet_instEmptyCollection(v_00_u03b1_2100_, v_cmp_2101_);
    lean_dec_ref(v_cmp_2101_);
    return v_res_2102_;
}
pub unsafe fn l_Std_ExtTreeSet_instInhabited(
    mut v_00_u03b1_2103_: *mut LeanObject,
    mut v_cmp_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v___x_2105_ = lean_box(1);
    return v___x_2105_;
}
pub unsafe fn l_Std_ExtTreeSet_instInhabited___boxed(
    mut v_00_u03b1_2106_: *mut LeanObject,
    mut v_cmp_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2108_: *mut LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_ExtTreeSet_instInhabited(v_00_u03b1_2106_, v_cmp_2107_);
    lean_dec_ref(v_cmp_2107_);
    return v_res_2108_;
}
pub unsafe fn l_Std_ExtTreeSet_insert___redArg(
    mut v_cmp_2109_: *mut LeanObject,
    mut v_l_2110_: *mut LeanObject,
    mut v_a_2111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2112_: u8 = 0;
    lean_inc(v_l_2110_);
    lean_inc(v_a_2111_);
    lean_inc_ref(v_cmp_2109_);
    v___x_2112_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2109_, v_a_2111_, v_l_2110_);
    if v___x_2112_ == 0 {
        let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
        v___x_2113_ = lean_box(0);
        v___x_2114_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2109_,
            v_a_2111_,
            v___x_2113_,
            v_l_2110_,
        );
        return v___x_2114_;
    } else {
        lean_dec(v_a_2111_);
        lean_dec_ref(v_cmp_2109_);
        return v_l_2110_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_insert(
    mut v_00_u03b1_2115_: *mut LeanObject,
    mut v_cmp_2116_: *mut LeanObject,
    mut v_inst_2117_: *mut LeanObject,
    mut v_l_2118_: *mut LeanObject,
    mut v_a_2119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2120_: u8 = 0;
    lean_inc(v_l_2118_);
    lean_inc(v_a_2119_);
    lean_inc_ref(v_cmp_2116_);
    v___x_2120_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2116_, v_a_2119_, v_l_2118_);
    if v___x_2120_ == 0 {
        let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
        v___x_2121_ = lean_box(0);
        v___x_2122_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2116_,
            v_a_2119_,
            v___x_2121_,
            v_l_2118_,
        );
        return v___x_2122_;
    } else {
        lean_dec(v_a_2119_);
        lean_dec_ref(v_cmp_2116_);
        return v_l_2118_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0(
    mut v_cmp_2123_: *mut LeanObject,
    mut v_e_2124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    v___x_2125_ = lean_box(1);
    lean_inc(v_e_2124_);
    lean_inc_ref(v_cmp_2123_);
    v___x_2126_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2123_, v_e_2124_, v___x_2125_);
    if v___x_2126_ == 0 {
        let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
        v___x_2127_ = lean_box(0);
        v___x_2128_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2123_,
            v_e_2124_,
            v___x_2127_,
            v___x_2125_,
        );
        return v___x_2128_;
    } else {
        lean_dec(v_e_2124_);
        lean_dec_ref(v_cmp_2123_);
        return v___x_2125_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg(
    mut v_cmp_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2130_: *mut LeanObject = core::ptr::null_mut();
    v___f_2130_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2130_, 0, v_cmp_2129_);
    return v___f_2130_;
}
pub unsafe fn l_Std_ExtTreeSet_instSingletonOfTransCmp(
    mut v_00_u03b1_2131_: *mut LeanObject,
    mut v_cmp_2132_: *mut LeanObject,
    mut v_inst_2133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2134_: *mut LeanObject = core::ptr::null_mut();
    v___f_2134_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2134_, 0, v_cmp_2132_);
    return v___f_2134_;
}
pub unsafe fn l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0(
    mut v_cmp_2135_: *mut LeanObject,
    mut v_e_2136_: *mut LeanObject,
    mut v_s_2137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2138_: u8 = 0;
    lean_inc(v_s_2137_);
    lean_inc(v_e_2136_);
    lean_inc_ref(v_cmp_2135_);
    v___x_2138_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2135_, v_e_2136_, v_s_2137_);
    if v___x_2138_ == 0 {
        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
        v___x_2139_ = lean_box(0);
        v___x_2140_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2135_,
            v_e_2136_,
            v___x_2139_,
            v_s_2137_,
        );
        return v___x_2140_;
    } else {
        lean_dec(v_e_2136_);
        lean_dec_ref(v_cmp_2135_);
        return v_s_2137_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_instInsertOfTransCmp___redArg(
    mut v_cmp_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2142_: *mut LeanObject = core::ptr::null_mut();
    v___f_2142_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2142_, 0, v_cmp_2141_);
    return v___f_2142_;
}
pub unsafe fn l_Std_ExtTreeSet_instInsertOfTransCmp(
    mut v_00_u03b1_2143_: *mut LeanObject,
    mut v_cmp_2144_: *mut LeanObject,
    mut v_inst_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2146_: *mut LeanObject = core::ptr::null_mut();
    v___f_2146_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2146_, 0, v_cmp_2144_);
    return v___f_2146_;
}
pub unsafe fn l_Std_ExtTreeSet_containsThenInsert___redArg(
    mut v_cmp_2147_: *mut LeanObject,
    mut v_t_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2150_: u8 = 0;
    lean_inc(v_t_2148_);
    lean_inc(v_a_2149_);
    lean_inc_ref(v_cmp_2147_);
    v___x_2150_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2147_, v_a_2149_, v_t_2148_);
    if v___x_2150_ == 0 {
        let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
        v___x_2151_ = lean_box(0);
        v___x_2152_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2147_,
            v_a_2149_,
            v___x_2151_,
            v_t_2148_,
        );
        v___x_2153_ = lean_box((v___x_2150_) as usize);
        v___x_2154_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2154_, 0, v___x_2153_);
        lean_ctor_set(v___x_2154_, 1, v___x_2152_);
        return v___x_2154_;
    } else {
        let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_2149_);
        lean_dec_ref(v_cmp_2147_);
        v___x_2155_ = lean_box((v___x_2150_) as usize);
        v___x_2156_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2156_, 0, v___x_2155_);
        lean_ctor_set(v___x_2156_, 1, v_t_2148_);
        return v___x_2156_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_containsThenInsert(
    mut v_00_u03b1_2157_: *mut LeanObject,
    mut v_cmp_2158_: *mut LeanObject,
    mut v_inst_2159_: *mut LeanObject,
    mut v_t_2160_: *mut LeanObject,
    mut v_a_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2162_: u8 = 0;
    lean_inc(v_t_2160_);
    lean_inc(v_a_2161_);
    lean_inc_ref(v_cmp_2158_);
    v___x_2162_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2158_, v_a_2161_, v_t_2160_);
    if v___x_2162_ == 0 {
        let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
        v___x_2163_ = lean_box(0);
        v___x_2164_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2158_,
            v_a_2161_,
            v___x_2163_,
            v_t_2160_,
        );
        v___x_2165_ = lean_box((v___x_2162_) as usize);
        v___x_2166_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2166_, 0, v___x_2165_);
        lean_ctor_set(v___x_2166_, 1, v___x_2164_);
        return v___x_2166_;
    } else {
        let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_2161_);
        lean_dec_ref(v_cmp_2158_);
        v___x_2167_ = lean_box((v___x_2162_) as usize);
        v___x_2168_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2168_, 0, v___x_2167_);
        lean_ctor_set(v___x_2168_, 1, v_t_2160_);
        return v___x_2168_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_contains___redArg(
    mut v_cmp_2169_: *mut LeanObject,
    mut v_l_2170_: *mut LeanObject,
    mut v_a_2171_: *mut LeanObject,
) -> u8 {
    let mut v___x_2172_: u8 = 0;
    v___x_2172_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2169_, v_a_2171_, v_l_2170_);
    return v___x_2172_;
}
pub unsafe fn l_Std_ExtTreeSet_contains___redArg___boxed(
    mut v_cmp_2173_: *mut LeanObject,
    mut v_l_2174_: *mut LeanObject,
    mut v_a_2175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2176_: u8 = 0;
    let mut v_r_2177_: *mut LeanObject = core::ptr::null_mut();
    v_res_2176_ = l_Std_ExtTreeSet_contains___redArg(v_cmp_2173_, v_l_2174_, v_a_2175_);
    v_r_2177_ = lean_box((v_res_2176_) as usize);
    return v_r_2177_;
}
pub unsafe fn l_Std_ExtTreeSet_contains(
    mut v_00_u03b1_2178_: *mut LeanObject,
    mut v_cmp_2179_: *mut LeanObject,
    mut v_inst_2180_: *mut LeanObject,
    mut v_l_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
) -> u8 {
    let mut v___x_2183_: u8 = 0;
    v___x_2183_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2179_, v_a_2182_, v_l_2181_);
    return v___x_2183_;
}
pub unsafe fn l_Std_ExtTreeSet_contains___boxed(
    mut v_00_u03b1_2184_: *mut LeanObject,
    mut v_cmp_2185_: *mut LeanObject,
    mut v_inst_2186_: *mut LeanObject,
    mut v_l_2187_: *mut LeanObject,
    mut v_a_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2189_: u8 = 0;
    let mut v_r_2190_: *mut LeanObject = core::ptr::null_mut();
    v_res_2189_ = l_Std_ExtTreeSet_contains(
        v_00_u03b1_2184_,
        v_cmp_2185_,
        v_inst_2186_,
        v_l_2187_,
        v_a_2188_,
    );
    v_r_2190_ = lean_box((v_res_2189_) as usize);
    return v_r_2190_;
}
pub unsafe fn l_Std_ExtTreeSet_instMembershipOfTransCmp(
    mut v_00_u03b1_2191_: *mut LeanObject,
    mut v_cmp_2192_: *mut LeanObject,
    mut v_inst_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    v___x_2194_ = lean_box(0);
    return v___x_2194_;
}
pub unsafe fn l_Std_ExtTreeSet_instMembershipOfTransCmp___boxed(
    mut v_00_u03b1_2195_: *mut LeanObject,
    mut v_cmp_2196_: *mut LeanObject,
    mut v_inst_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2198_: *mut LeanObject = core::ptr::null_mut();
    v_res_2198_ =
        l_Std_ExtTreeSet_instMembershipOfTransCmp(v_00_u03b1_2195_, v_cmp_2196_, v_inst_2197_);
    lean_dec_ref(v_cmp_2196_);
    return v_res_2198_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem___redArg(
    mut v_cmp_2199_: *mut LeanObject,
    mut v_m_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
) -> u8 {
    let mut v___x_2202_: u8 = 0;
    v___x_2202_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2199_, v_a_2201_, v_m_2200_);
    return v___x_2202_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem___redArg___boxed(
    mut v_cmp_2203_: *mut LeanObject,
    mut v_m_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2206_: u8 = 0;
    let mut v_r_2207_: *mut LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Std_ExtTreeSet_instDecidableMem___redArg(v_cmp_2203_, v_m_2204_, v_a_2205_);
    v_r_2207_ = lean_box((v_res_2206_) as usize);
    return v_r_2207_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem(
    mut v_00_u03b1_2208_: *mut LeanObject,
    mut v_cmp_2209_: *mut LeanObject,
    mut v_inst_2210_: *mut LeanObject,
    mut v_m_2211_: *mut LeanObject,
    mut v_a_2212_: *mut LeanObject,
) -> u8 {
    let mut v___x_2213_: u8 = 0;
    v___x_2213_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2209_, v_a_2212_, v_m_2211_);
    return v___x_2213_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem___boxed(
    mut v_00_u03b1_2214_: *mut LeanObject,
    mut v_cmp_2215_: *mut LeanObject,
    mut v_inst_2216_: *mut LeanObject,
    mut v_m_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2219_: u8 = 0;
    let mut v_r_2220_: *mut LeanObject = core::ptr::null_mut();
    v_res_2219_ = l_Std_ExtTreeSet_instDecidableMem(
        v_00_u03b1_2214_,
        v_cmp_2215_,
        v_inst_2216_,
        v_m_2217_,
        v_a_2218_,
    );
    v_r_2220_ = lean_box((v_res_2219_) as usize);
    return v_r_2220_;
}
pub unsafe fn l_Std_ExtTreeSet_size___redArg(mut v_t_2221_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_t_2221_) == 0 {
        let mut v_size_2222_: *mut LeanObject = core::ptr::null_mut();
        v_size_2222_ = lean_ctor_get(v_t_2221_, 0);
        lean_inc(v_size_2222_);
        return v_size_2222_;
    } else {
        let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
        v___x_2223_ = lean_unsigned_to_nat(0);
        return v___x_2223_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_size___redArg___boxed(
    mut v_t_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2225_: *mut LeanObject = core::ptr::null_mut();
    v_res_2225_ = l_Std_ExtTreeSet_size___redArg(v_t_2224_);
    lean_dec(v_t_2224_);
    return v_res_2225_;
}
pub unsafe fn l_Std_ExtTreeSet_size(
    mut v_00_u03b1_2226_: *mut LeanObject,
    mut v_cmp_2227_: *mut LeanObject,
    mut v_t_2228_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_2228_) == 0 {
        let mut v_size_2229_: *mut LeanObject = core::ptr::null_mut();
        v_size_2229_ = lean_ctor_get(v_t_2228_, 0);
        lean_inc(v_size_2229_);
        return v_size_2229_;
    } else {
        let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
        v___x_2230_ = lean_unsigned_to_nat(0);
        return v___x_2230_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_size___boxed(
    mut v_00_u03b1_2231_: *mut LeanObject,
    mut v_cmp_2232_: *mut LeanObject,
    mut v_t_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2234_: *mut LeanObject = core::ptr::null_mut();
    v_res_2234_ = l_Std_ExtTreeSet_size(v_00_u03b1_2231_, v_cmp_2232_, v_t_2233_);
    lean_dec(v_t_2233_);
    lean_dec_ref(v_cmp_2232_);
    return v_res_2234_;
}
pub unsafe fn l_Std_ExtTreeSet_isEmpty___redArg(mut v_t_2235_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_t_2235_) == 0 {
        let mut v___x_2236_: u8 = 0;
        v___x_2236_ = 0;
        return v___x_2236_;
    } else {
        let mut v___x_2237_: u8 = 0;
        v___x_2237_ = 1;
        return v___x_2237_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_isEmpty___redArg___boxed(
    mut v_t_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2239_: u8 = 0;
    let mut v_r_2240_: *mut LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Std_ExtTreeSet_isEmpty___redArg(v_t_2238_);
    lean_dec(v_t_2238_);
    v_r_2240_ = lean_box((v_res_2239_) as usize);
    return v_r_2240_;
}
pub unsafe fn l_Std_ExtTreeSet_isEmpty(
    mut v_00_u03b1_2241_: *mut LeanObject,
    mut v_cmp_2242_: *mut LeanObject,
    mut v_t_2243_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_t_2243_) == 0 {
        let mut v___x_2244_: u8 = 0;
        v___x_2244_ = 0;
        return v___x_2244_;
    } else {
        let mut v___x_2245_: u8 = 0;
        v___x_2245_ = 1;
        return v___x_2245_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_isEmpty___boxed(
    mut v_00_u03b1_2246_: *mut LeanObject,
    mut v_cmp_2247_: *mut LeanObject,
    mut v_t_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2249_: u8 = 0;
    let mut v_r_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2249_ = l_Std_ExtTreeSet_isEmpty(v_00_u03b1_2246_, v_cmp_2247_, v_t_2248_);
    lean_dec(v_t_2248_);
    lean_dec_ref(v_cmp_2247_);
    v_r_2250_ = lean_box((v_res_2249_) as usize);
    return v_r_2250_;
}
pub unsafe fn l_Std_ExtTreeSet_erase___redArg(
    mut v_cmp_2251_: *mut LeanObject,
    mut v_t_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2251_, v_a_2253_, v_t_2252_);
    return v___x_2254_;
}
pub unsafe fn l_Std_ExtTreeSet_erase(
    mut v_00_u03b1_2255_: *mut LeanObject,
    mut v_cmp_2256_: *mut LeanObject,
    mut v_inst_2257_: *mut LeanObject,
    mut v_t_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2256_, v_a_2259_, v_t_2258_);
    return v___x_2260_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x3f___redArg(
    mut v_cmp_2261_: *mut LeanObject,
    mut v_t_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    v___x_2264_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2261_, v_t_2262_, v_a_2263_);
    return v___x_2264_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x3f(
    mut v_00_u03b1_2265_: *mut LeanObject,
    mut v_cmp_2266_: *mut LeanObject,
    mut v_inst_2267_: *mut LeanObject,
    mut v_t_2268_: *mut LeanObject,
    mut v_a_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    v___x_2270_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2266_, v_t_2268_, v_a_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Std_ExtTreeSet_get___redArg(
    mut v_cmp_2271_: *mut LeanObject,
    mut v_t_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    v___x_2274_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2271_, v_t_2272_, v_a_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Std_ExtTreeSet_get(
    mut v_00_u03b1_2275_: *mut LeanObject,
    mut v_cmp_2276_: *mut LeanObject,
    mut v_inst_2277_: *mut LeanObject,
    mut v_t_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
    mut v_h_2280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2276_, v_t_2278_, v_a_2279_);
    return v___x_2281_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21___redArg(
    mut v_cmp_2282_: *mut LeanObject,
    mut v_inst_2283_: *mut LeanObject,
    mut v_t_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2282_,
        v_t_2284_,
        v_a_2285_,
        v_inst_2283_,
    );
    return v___x_2286_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21___redArg___boxed(
    mut v_cmp_2287_: *mut LeanObject,
    mut v_inst_2288_: *mut LeanObject,
    mut v_t_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2291_: *mut LeanObject = core::ptr::null_mut();
    v_res_2291_ =
        l_Std_ExtTreeSet_get_x21___redArg(v_cmp_2287_, v_inst_2288_, v_t_2289_, v_a_2290_);
    lean_dec(v_inst_2288_);
    return v_res_2291_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21(
    mut v_00_u03b1_2292_: *mut LeanObject,
    mut v_cmp_2293_: *mut LeanObject,
    mut v_inst_2294_: *mut LeanObject,
    mut v_inst_2295_: *mut LeanObject,
    mut v_t_2296_: *mut LeanObject,
    mut v_a_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v___x_2298_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2293_,
        v_t_2296_,
        v_a_2297_,
        v_inst_2295_,
    );
    return v___x_2298_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21___boxed(
    mut v_00_u03b1_2299_: *mut LeanObject,
    mut v_cmp_2300_: *mut LeanObject,
    mut v_inst_2301_: *mut LeanObject,
    mut v_inst_2302_: *mut LeanObject,
    mut v_t_2303_: *mut LeanObject,
    mut v_a_2304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2305_: *mut LeanObject = core::ptr::null_mut();
    v_res_2305_ = l_Std_ExtTreeSet_get_x21(
        v_00_u03b1_2299_,
        v_cmp_2300_,
        v_inst_2301_,
        v_inst_2302_,
        v_t_2303_,
        v_a_2304_,
    );
    lean_dec(v_inst_2302_);
    return v_res_2305_;
}
pub unsafe fn l_Std_ExtTreeSet_getD___redArg(
    mut v_cmp_2306_: *mut LeanObject,
    mut v_t_2307_: *mut LeanObject,
    mut v_a_2308_: *mut LeanObject,
    mut v_fallback_2309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2306_,
        v_t_2307_,
        v_a_2308_,
        v_fallback_2309_,
    );
    return v___x_2310_;
}
pub unsafe fn l_Std_ExtTreeSet_getD___redArg___boxed(
    mut v_cmp_2311_: *mut LeanObject,
    mut v_t_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
    mut v_fallback_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_res_2315_ =
        l_Std_ExtTreeSet_getD___redArg(v_cmp_2311_, v_t_2312_, v_a_2313_, v_fallback_2314_);
    lean_dec(v_fallback_2314_);
    return v_res_2315_;
}
pub unsafe fn l_Std_ExtTreeSet_getD(
    mut v_00_u03b1_2316_: *mut LeanObject,
    mut v_cmp_2317_: *mut LeanObject,
    mut v_inst_2318_: *mut LeanObject,
    mut v_t_2319_: *mut LeanObject,
    mut v_a_2320_: *mut LeanObject,
    mut v_fallback_2321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    v___x_2322_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2317_,
        v_t_2319_,
        v_a_2320_,
        v_fallback_2321_,
    );
    return v___x_2322_;
}
pub unsafe fn l_Std_ExtTreeSet_getD___boxed(
    mut v_00_u03b1_2323_: *mut LeanObject,
    mut v_cmp_2324_: *mut LeanObject,
    mut v_inst_2325_: *mut LeanObject,
    mut v_t_2326_: *mut LeanObject,
    mut v_a_2327_: *mut LeanObject,
    mut v_fallback_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2329_: *mut LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Std_ExtTreeSet_getD(
        v_00_u03b1_2323_,
        v_cmp_2324_,
        v_inst_2325_,
        v_t_2326_,
        v_a_2327_,
        v_fallback_2328_,
    );
    lean_dec(v_fallback_2328_);
    return v_res_2329_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f___redArg(mut v_t_2330_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    v___x_2331_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2330_);
    return v___x_2331_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f___redArg___boxed(
    mut v_t_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2333_: *mut LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Std_ExtTreeSet_min_x3f___redArg(v_t_2332_);
    lean_dec(v_t_2332_);
    return v_res_2333_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f(
    mut v_00_u03b1_2334_: *mut LeanObject,
    mut v_cmp_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
    mut v_t_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2337_);
    return v___x_2338_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f___boxed(
    mut v_00_u03b1_2339_: *mut LeanObject,
    mut v_cmp_2340_: *mut LeanObject,
    mut v_inst_2341_: *mut LeanObject,
    mut v_t_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2343_: *mut LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Std_ExtTreeSet_min_x3f(v_00_u03b1_2339_, v_cmp_2340_, v_inst_2341_, v_t_2342_);
    lean_dec(v_t_2342_);
    lean_dec_ref(v_cmp_2340_);
    return v_res_2343_;
}
pub unsafe fn l_Std_ExtTreeSet_min___redArg(mut v_t_2344_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2344_);
    return v___x_2345_;
}
pub unsafe fn l_Std_ExtTreeSet_min___redArg___boxed(
    mut v_t_2346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2347_: *mut LeanObject = core::ptr::null_mut();
    v_res_2347_ = l_Std_ExtTreeSet_min___redArg(v_t_2346_);
    lean_dec(v_t_2346_);
    return v_res_2347_;
}
pub unsafe fn l_Std_ExtTreeSet_min(
    mut v_00_u03b1_2348_: *mut LeanObject,
    mut v_cmp_2349_: *mut LeanObject,
    mut v_inst_2350_: *mut LeanObject,
    mut v_t_2351_: *mut LeanObject,
    mut v_h_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2351_);
    return v___x_2353_;
}
pub unsafe fn l_Std_ExtTreeSet_min___boxed(
    mut v_00_u03b1_2354_: *mut LeanObject,
    mut v_cmp_2355_: *mut LeanObject,
    mut v_inst_2356_: *mut LeanObject,
    mut v_t_2357_: *mut LeanObject,
    mut v_h_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2359_: *mut LeanObject = core::ptr::null_mut();
    v_res_2359_ = l_Std_ExtTreeSet_min(
        v_00_u03b1_2354_,
        v_cmp_2355_,
        v_inst_2356_,
        v_t_2357_,
        v_h_2358_,
    );
    lean_dec(v_t_2357_);
    lean_dec_ref(v_cmp_2355_);
    return v_res_2359_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21___redArg(
    mut v_inst_2360_: *mut LeanObject,
    mut v_t_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    v___x_2362_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2360_, v_t_2361_);
    return v___x_2362_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21___redArg___boxed(
    mut v_inst_2363_: *mut LeanObject,
    mut v_t_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2365_: *mut LeanObject = core::ptr::null_mut();
    v_res_2365_ = l_Std_ExtTreeSet_min_x21___redArg(v_inst_2363_, v_t_2364_);
    lean_dec(v_t_2364_);
    lean_dec(v_inst_2363_);
    return v_res_2365_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21(
    mut v_00_u03b1_2366_: *mut LeanObject,
    mut v_cmp_2367_: *mut LeanObject,
    mut v_inst_2368_: *mut LeanObject,
    mut v_inst_2369_: *mut LeanObject,
    mut v_t_2370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2369_, v_t_2370_);
    return v___x_2371_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21___boxed(
    mut v_00_u03b1_2372_: *mut LeanObject,
    mut v_cmp_2373_: *mut LeanObject,
    mut v_inst_2374_: *mut LeanObject,
    mut v_inst_2375_: *mut LeanObject,
    mut v_t_2376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2377_: *mut LeanObject = core::ptr::null_mut();
    v_res_2377_ = l_Std_ExtTreeSet_min_x21(
        v_00_u03b1_2372_,
        v_cmp_2373_,
        v_inst_2374_,
        v_inst_2375_,
        v_t_2376_,
    );
    lean_dec(v_t_2376_);
    lean_dec(v_inst_2375_);
    lean_dec_ref(v_cmp_2373_);
    return v_res_2377_;
}
pub unsafe fn l_Std_ExtTreeSet_minD___redArg(
    mut v_t_2378_: *mut LeanObject,
    mut v_fallback_2379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v___x_2380_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2378_, v_fallback_2379_);
    return v___x_2380_;
}
pub unsafe fn l_Std_ExtTreeSet_minD___redArg___boxed(
    mut v_t_2381_: *mut LeanObject,
    mut v_fallback_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2383_: *mut LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Std_ExtTreeSet_minD___redArg(v_t_2381_, v_fallback_2382_);
    lean_dec(v_fallback_2382_);
    lean_dec(v_t_2381_);
    return v_res_2383_;
}
pub unsafe fn l_Std_ExtTreeSet_minD(
    mut v_00_u03b1_2384_: *mut LeanObject,
    mut v_cmp_2385_: *mut LeanObject,
    mut v_inst_2386_: *mut LeanObject,
    mut v_t_2387_: *mut LeanObject,
    mut v_fallback_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    v___x_2389_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2387_, v_fallback_2388_);
    return v___x_2389_;
}
pub unsafe fn l_Std_ExtTreeSet_minD___boxed(
    mut v_00_u03b1_2390_: *mut LeanObject,
    mut v_cmp_2391_: *mut LeanObject,
    mut v_inst_2392_: *mut LeanObject,
    mut v_t_2393_: *mut LeanObject,
    mut v_fallback_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Std_ExtTreeSet_minD(
        v_00_u03b1_2390_,
        v_cmp_2391_,
        v_inst_2392_,
        v_t_2393_,
        v_fallback_2394_,
    );
    lean_dec(v_fallback_2394_);
    lean_dec(v_t_2393_);
    lean_dec_ref(v_cmp_2391_);
    return v_res_2395_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f___redArg(mut v_t_2396_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v___x_2397_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f___redArg___boxed(
    mut v_t_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2399_: *mut LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Std_ExtTreeSet_max_x3f___redArg(v_t_2398_);
    lean_dec(v_t_2398_);
    return v_res_2399_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f(
    mut v_00_u03b1_2400_: *mut LeanObject,
    mut v_cmp_2401_: *mut LeanObject,
    mut v_inst_2402_: *mut LeanObject,
    mut v_t_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    v___x_2404_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2403_);
    return v___x_2404_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f___boxed(
    mut v_00_u03b1_2405_: *mut LeanObject,
    mut v_cmp_2406_: *mut LeanObject,
    mut v_inst_2407_: *mut LeanObject,
    mut v_t_2408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2409_: *mut LeanObject = core::ptr::null_mut();
    v_res_2409_ = l_Std_ExtTreeSet_max_x3f(v_00_u03b1_2405_, v_cmp_2406_, v_inst_2407_, v_t_2408_);
    lean_dec(v_t_2408_);
    lean_dec_ref(v_cmp_2406_);
    return v_res_2409_;
}
pub unsafe fn l_Std_ExtTreeSet_max___redArg(mut v_t_2410_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2410_);
    return v___x_2411_;
}
pub unsafe fn l_Std_ExtTreeSet_max___redArg___boxed(
    mut v_t_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Std_ExtTreeSet_max___redArg(v_t_2412_);
    lean_dec(v_t_2412_);
    return v_res_2413_;
}
pub unsafe fn l_Std_ExtTreeSet_max(
    mut v_00_u03b1_2414_: *mut LeanObject,
    mut v_cmp_2415_: *mut LeanObject,
    mut v_inst_2416_: *mut LeanObject,
    mut v_t_2417_: *mut LeanObject,
    mut v_h_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    v___x_2419_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2417_);
    return v___x_2419_;
}
pub unsafe fn l_Std_ExtTreeSet_max___boxed(
    mut v_00_u03b1_2420_: *mut LeanObject,
    mut v_cmp_2421_: *mut LeanObject,
    mut v_inst_2422_: *mut LeanObject,
    mut v_t_2423_: *mut LeanObject,
    mut v_h_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2425_: *mut LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_Std_ExtTreeSet_max(
        v_00_u03b1_2420_,
        v_cmp_2421_,
        v_inst_2422_,
        v_t_2423_,
        v_h_2424_,
    );
    lean_dec(v_t_2423_);
    lean_dec_ref(v_cmp_2421_);
    return v_res_2425_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21___redArg(
    mut v_inst_2426_: *mut LeanObject,
    mut v_t_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    v___x_2428_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2426_, v_t_2427_);
    return v___x_2428_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21___redArg___boxed(
    mut v_inst_2429_: *mut LeanObject,
    mut v_t_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Std_ExtTreeSet_max_x21___redArg(v_inst_2429_, v_t_2430_);
    lean_dec(v_t_2430_);
    lean_dec(v_inst_2429_);
    return v_res_2431_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21(
    mut v_00_u03b1_2432_: *mut LeanObject,
    mut v_cmp_2433_: *mut LeanObject,
    mut v_inst_2434_: *mut LeanObject,
    mut v_inst_2435_: *mut LeanObject,
    mut v_t_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2435_, v_t_2436_);
    return v___x_2437_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21___boxed(
    mut v_00_u03b1_2438_: *mut LeanObject,
    mut v_cmp_2439_: *mut LeanObject,
    mut v_inst_2440_: *mut LeanObject,
    mut v_inst_2441_: *mut LeanObject,
    mut v_t_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2443_: *mut LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Std_ExtTreeSet_max_x21(
        v_00_u03b1_2438_,
        v_cmp_2439_,
        v_inst_2440_,
        v_inst_2441_,
        v_t_2442_,
    );
    lean_dec(v_t_2442_);
    lean_dec(v_inst_2441_);
    lean_dec_ref(v_cmp_2439_);
    return v_res_2443_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD___redArg(
    mut v_t_2444_: *mut LeanObject,
    mut v_fallback_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2444_, v_fallback_2445_);
    return v___x_2446_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD___redArg___boxed(
    mut v_t_2447_: *mut LeanObject,
    mut v_fallback_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Std_ExtTreeSet_maxD___redArg(v_t_2447_, v_fallback_2448_);
    lean_dec(v_fallback_2448_);
    lean_dec(v_t_2447_);
    return v_res_2449_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD(
    mut v_00_u03b1_2450_: *mut LeanObject,
    mut v_cmp_2451_: *mut LeanObject,
    mut v_inst_2452_: *mut LeanObject,
    mut v_t_2453_: *mut LeanObject,
    mut v_fallback_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2453_, v_fallback_2454_);
    return v___x_2455_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD___boxed(
    mut v_00_u03b1_2456_: *mut LeanObject,
    mut v_cmp_2457_: *mut LeanObject,
    mut v_inst_2458_: *mut LeanObject,
    mut v_t_2459_: *mut LeanObject,
    mut v_fallback_2460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2461_: *mut LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Std_ExtTreeSet_maxD(
        v_00_u03b1_2456_,
        v_cmp_2457_,
        v_inst_2458_,
        v_t_2459_,
        v_fallback_2460_,
    );
    lean_dec(v_fallback_2460_);
    lean_dec(v_t_2459_);
    lean_dec_ref(v_cmp_2457_);
    return v_res_2461_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f___redArg(
    mut v_t_2462_: *mut LeanObject,
    mut v_n_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    v___x_2464_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2462_, v_n_2463_);
    return v___x_2464_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(
    mut v_t_2465_: *mut LeanObject,
    mut v_n_2466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2467_: *mut LeanObject = core::ptr::null_mut();
    v_res_2467_ = l_Std_ExtTreeSet_atIdx_x3f___redArg(v_t_2465_, v_n_2466_);
    lean_dec(v_t_2465_);
    return v_res_2467_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f(
    mut v_00_u03b1_2468_: *mut LeanObject,
    mut v_cmp_2469_: *mut LeanObject,
    mut v_inst_2470_: *mut LeanObject,
    mut v_t_2471_: *mut LeanObject,
    mut v_n_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    v___x_2473_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2471_, v_n_2472_);
    return v___x_2473_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f___boxed(
    mut v_00_u03b1_2474_: *mut LeanObject,
    mut v_cmp_2475_: *mut LeanObject,
    mut v_inst_2476_: *mut LeanObject,
    mut v_t_2477_: *mut LeanObject,
    mut v_n_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2479_: *mut LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_Std_ExtTreeSet_atIdx_x3f(
        v_00_u03b1_2474_,
        v_cmp_2475_,
        v_inst_2476_,
        v_t_2477_,
        v_n_2478_,
    );
    lean_dec(v_t_2477_);
    lean_dec_ref(v_cmp_2475_);
    return v_res_2479_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx___redArg(
    mut v_t_2480_: *mut LeanObject,
    mut v_n_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2480_, v_n_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx___redArg___boxed(
    mut v_t_2483_: *mut LeanObject,
    mut v_n_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2485_: *mut LeanObject = core::ptr::null_mut();
    v_res_2485_ = l_Std_ExtTreeSet_atIdx___redArg(v_t_2483_, v_n_2484_);
    lean_dec(v_t_2483_);
    return v_res_2485_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx(
    mut v_00_u03b1_2486_: *mut LeanObject,
    mut v_cmp_2487_: *mut LeanObject,
    mut v_inst_2488_: *mut LeanObject,
    mut v_t_2489_: *mut LeanObject,
    mut v_n_2490_: *mut LeanObject,
    mut v_h_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2489_, v_n_2490_);
    return v___x_2492_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx___boxed(
    mut v_00_u03b1_2493_: *mut LeanObject,
    mut v_cmp_2494_: *mut LeanObject,
    mut v_inst_2495_: *mut LeanObject,
    mut v_t_2496_: *mut LeanObject,
    mut v_n_2497_: *mut LeanObject,
    mut v_h_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2499_: *mut LeanObject = core::ptr::null_mut();
    v_res_2499_ = l_Std_ExtTreeSet_atIdx(
        v_00_u03b1_2493_,
        v_cmp_2494_,
        v_inst_2495_,
        v_t_2496_,
        v_n_2497_,
        v_h_2498_,
    );
    lean_dec(v_t_2496_);
    lean_dec_ref(v_cmp_2494_);
    return v_res_2499_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21___redArg(
    mut v_inst_2500_: *mut LeanObject,
    mut v_t_2501_: *mut LeanObject,
    mut v_n_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    v___x_2503_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2500_, v_t_2501_, v_n_2502_);
    return v___x_2503_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(
    mut v_inst_2504_: *mut LeanObject,
    mut v_t_2505_: *mut LeanObject,
    mut v_n_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2507_: *mut LeanObject = core::ptr::null_mut();
    v_res_2507_ = l_Std_ExtTreeSet_atIdx_x21___redArg(v_inst_2504_, v_t_2505_, v_n_2506_);
    lean_dec(v_t_2505_);
    lean_dec(v_inst_2504_);
    return v_res_2507_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21(
    mut v_00_u03b1_2508_: *mut LeanObject,
    mut v_cmp_2509_: *mut LeanObject,
    mut v_inst_2510_: *mut LeanObject,
    mut v_inst_2511_: *mut LeanObject,
    mut v_t_2512_: *mut LeanObject,
    mut v_n_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    v___x_2514_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2511_, v_t_2512_, v_n_2513_);
    return v___x_2514_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21___boxed(
    mut v_00_u03b1_2515_: *mut LeanObject,
    mut v_cmp_2516_: *mut LeanObject,
    mut v_inst_2517_: *mut LeanObject,
    mut v_inst_2518_: *mut LeanObject,
    mut v_t_2519_: *mut LeanObject,
    mut v_n_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2521_: *mut LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Std_ExtTreeSet_atIdx_x21(
        v_00_u03b1_2515_,
        v_cmp_2516_,
        v_inst_2517_,
        v_inst_2518_,
        v_t_2519_,
        v_n_2520_,
    );
    lean_dec(v_t_2519_);
    lean_dec(v_inst_2518_);
    lean_dec_ref(v_cmp_2516_);
    return v_res_2521_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD___redArg(
    mut v_t_2522_: *mut LeanObject,
    mut v_n_2523_: *mut LeanObject,
    mut v_fallback_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    v___x_2525_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2522_, v_n_2523_, v_fallback_2524_);
    return v___x_2525_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD___redArg___boxed(
    mut v_t_2526_: *mut LeanObject,
    mut v_n_2527_: *mut LeanObject,
    mut v_fallback_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_ExtTreeSet_atIdxD___redArg(v_t_2526_, v_n_2527_, v_fallback_2528_);
    lean_dec(v_fallback_2528_);
    lean_dec(v_t_2526_);
    return v_res_2529_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD(
    mut v_00_u03b1_2530_: *mut LeanObject,
    mut v_cmp_2531_: *mut LeanObject,
    mut v_inst_2532_: *mut LeanObject,
    mut v_t_2533_: *mut LeanObject,
    mut v_n_2534_: *mut LeanObject,
    mut v_fallback_2535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    v___x_2536_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2533_, v_n_2534_, v_fallback_2535_);
    return v___x_2536_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD___boxed(
    mut v_00_u03b1_2537_: *mut LeanObject,
    mut v_cmp_2538_: *mut LeanObject,
    mut v_inst_2539_: *mut LeanObject,
    mut v_t_2540_: *mut LeanObject,
    mut v_n_2541_: *mut LeanObject,
    mut v_fallback_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2543_: *mut LeanObject = core::ptr::null_mut();
    v_res_2543_ = l_Std_ExtTreeSet_atIdxD(
        v_00_u03b1_2537_,
        v_cmp_2538_,
        v_inst_2539_,
        v_t_2540_,
        v_n_2541_,
        v_fallback_2542_,
    );
    lean_dec(v_fallback_2542_);
    lean_dec(v_t_2540_);
    lean_dec_ref(v_cmp_2538_);
    return v_res_2543_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x3f___redArg(
    mut v_cmp_2544_: *mut LeanObject,
    mut v_t_2545_: *mut LeanObject,
    mut v_k_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = lean_box(0);
    v___x_2548_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2544_,
        v_k_2546_,
        v___x_2547_,
        v_t_2545_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x3f(
    mut v_00_u03b1_2549_: *mut LeanObject,
    mut v_cmp_2550_: *mut LeanObject,
    mut v_inst_2551_: *mut LeanObject,
    mut v_t_2552_: *mut LeanObject,
    mut v_k_2553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    v___x_2554_ = lean_box(0);
    v___x_2555_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2550_,
        v_k_2553_,
        v___x_2554_,
        v_t_2552_,
    );
    return v___x_2555_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x3f___redArg(
    mut v_cmp_2556_: *mut LeanObject,
    mut v_t_2557_: *mut LeanObject,
    mut v_k_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    v___x_2559_ = lean_box(0);
    v___x_2560_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2556_,
        v_k_2558_,
        v___x_2559_,
        v_t_2557_,
    );
    return v___x_2560_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x3f(
    mut v_00_u03b1_2561_: *mut LeanObject,
    mut v_cmp_2562_: *mut LeanObject,
    mut v_inst_2563_: *mut LeanObject,
    mut v_t_2564_: *mut LeanObject,
    mut v_k_2565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2566_ = lean_box(0);
    v___x_2567_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2562_,
        v_k_2565_,
        v___x_2566_,
        v_t_2564_,
    );
    return v___x_2567_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x3f___redArg(
    mut v_cmp_2568_: *mut LeanObject,
    mut v_t_2569_: *mut LeanObject,
    mut v_k_2570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    v___x_2571_ = lean_box(0);
    v___x_2572_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2568_,
        v_k_2570_,
        v___x_2571_,
        v_t_2569_,
    );
    return v___x_2572_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x3f(
    mut v_00_u03b1_2573_: *mut LeanObject,
    mut v_cmp_2574_: *mut LeanObject,
    mut v_inst_2575_: *mut LeanObject,
    mut v_t_2576_: *mut LeanObject,
    mut v_k_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    v___x_2578_ = lean_box(0);
    v___x_2579_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2574_,
        v_k_2577_,
        v___x_2578_,
        v_t_2576_,
    );
    return v___x_2579_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x3f___redArg(
    mut v_cmp_2580_: *mut LeanObject,
    mut v_t_2581_: *mut LeanObject,
    mut v_k_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    v___x_2583_ = lean_box(0);
    v___x_2584_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2580_,
        v_k_2582_,
        v___x_2583_,
        v_t_2581_,
    );
    return v___x_2584_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x3f(
    mut v_00_u03b1_2585_: *mut LeanObject,
    mut v_cmp_2586_: *mut LeanObject,
    mut v_inst_2587_: *mut LeanObject,
    mut v_t_2588_: *mut LeanObject,
    mut v_k_2589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    v___x_2590_ = lean_box(0);
    v___x_2591_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2586_,
        v_k_2589_,
        v___x_2590_,
        v_t_2588_,
    );
    return v___x_2591_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE___redArg(
    mut v_cmp_2592_: *mut LeanObject,
    mut v_t_2593_: *mut LeanObject,
    mut v_k_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    v___x_2595_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_2592_, v_k_2594_, v_t_2593_);
    return v___x_2595_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE(
    mut v_00_u03b1_2596_: *mut LeanObject,
    mut v_cmp_2597_: *mut LeanObject,
    mut v_inst_2598_: *mut LeanObject,
    mut v_t_2599_: *mut LeanObject,
    mut v_k_2600_: *mut LeanObject,
    mut v_h_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    v___x_2602_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_2597_, v_k_2600_, v_t_2599_);
    return v___x_2602_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT___redArg(
    mut v_cmp_2603_: *mut LeanObject,
    mut v_t_2604_: *mut LeanObject,
    mut v_k_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    v___x_2606_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_2603_, v_k_2605_, v_t_2604_);
    return v___x_2606_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT(
    mut v_00_u03b1_2607_: *mut LeanObject,
    mut v_cmp_2608_: *mut LeanObject,
    mut v_inst_2609_: *mut LeanObject,
    mut v_t_2610_: *mut LeanObject,
    mut v_k_2611_: *mut LeanObject,
    mut v_h_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2613_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_2608_, v_k_2611_, v_t_2610_);
    return v___x_2613_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE___redArg(
    mut v_cmp_2614_: *mut LeanObject,
    mut v_t_2615_: *mut LeanObject,
    mut v_k_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    v___x_2617_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_2614_, v_k_2616_, v_t_2615_);
    return v___x_2617_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE(
    mut v_00_u03b1_2618_: *mut LeanObject,
    mut v_cmp_2619_: *mut LeanObject,
    mut v_inst_2620_: *mut LeanObject,
    mut v_t_2621_: *mut LeanObject,
    mut v_k_2622_: *mut LeanObject,
    mut v_h_2623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_2619_, v_k_2622_, v_t_2621_);
    return v___x_2624_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT___redArg(
    mut v_cmp_2625_: *mut LeanObject,
    mut v_t_2626_: *mut LeanObject,
    mut v_k_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    v___x_2628_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_2625_, v_k_2627_, v_t_2626_);
    return v___x_2628_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT(
    mut v_00_u03b1_2629_: *mut LeanObject,
    mut v_cmp_2630_: *mut LeanObject,
    mut v_inst_2631_: *mut LeanObject,
    mut v_t_2632_: *mut LeanObject,
    mut v_k_2633_: *mut LeanObject,
    mut v_h_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    v___x_2635_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_2630_, v_k_2633_, v_t_2632_);
    return v___x_2635_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Std_ExtTreeSet_getGE_x21___redArg___closed__2;
    v___x_2640_ = lean_unsigned_to_nat(14);
    v___x_2641_ = lean_unsigned_to_nat(22);
    v___x_2642_ = l_Std_ExtTreeSet_getGE_x21___redArg___closed__1;
    v___x_2643_ = l_Std_ExtTreeSet_getGE_x21___redArg___closed__0;
    v___x_2644_ = l_mkPanicMessageWithDecl(
        v___x_2643_,
        v___x_2642_,
        v___x_2641_,
        v___x_2640_,
        v___x_2639_,
    );
    return v___x_2644_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x21___redArg(
    mut v_cmp_2645_: *mut LeanObject,
    mut v_inst_2646_: *mut LeanObject,
    mut v_t_2647_: *mut LeanObject,
    mut v_k_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    v___x_2649_ = lean_box(0);
    v___x_2650_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2645_,
        v_k_2648_,
        v___x_2649_,
        v_t_2647_,
    );
    if lean_obj_tag(v___x_2650_) == 0 {
        let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
        v___x_2651_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2652_ = l_panic___redArg(v_inst_2646_, v___x_2651_);
        return v___x_2652_;
    } else {
        let mut v_val_2653_: *mut LeanObject = core::ptr::null_mut();
        v_val_2653_ = lean_ctor_get(v___x_2650_, 0);
        lean_inc(v_val_2653_);
        lean_dec_ref_known(v___x_2650_, 1);
        return v_val_2653_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x21___redArg___boxed(
    mut v_cmp_2654_: *mut LeanObject,
    mut v_inst_2655_: *mut LeanObject,
    mut v_t_2656_: *mut LeanObject,
    mut v_k_2657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2658_: *mut LeanObject = core::ptr::null_mut();
    v_res_2658_ =
        l_Std_ExtTreeSet_getGE_x21___redArg(v_cmp_2654_, v_inst_2655_, v_t_2656_, v_k_2657_);
    lean_dec(v_inst_2655_);
    return v_res_2658_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x21(
    mut v_00_u03b1_2659_: *mut LeanObject,
    mut v_cmp_2660_: *mut LeanObject,
    mut v_inst_2661_: *mut LeanObject,
    mut v_inst_2662_: *mut LeanObject,
    mut v_t_2663_: *mut LeanObject,
    mut v_k_2664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    v___x_2665_ = lean_box(0);
    v___x_2666_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2660_,
        v_k_2664_,
        v___x_2665_,
        v_t_2663_,
    );
    if lean_obj_tag(v___x_2666_) == 0 {
        let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
        v___x_2667_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2668_ = l_panic___redArg(v_inst_2662_, v___x_2667_);
        return v___x_2668_;
    } else {
        let mut v_val_2669_: *mut LeanObject = core::ptr::null_mut();
        v_val_2669_ = lean_ctor_get(v___x_2666_, 0);
        lean_inc(v_val_2669_);
        lean_dec_ref_known(v___x_2666_, 1);
        return v_val_2669_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x21___boxed(
    mut v_00_u03b1_2670_: *mut LeanObject,
    mut v_cmp_2671_: *mut LeanObject,
    mut v_inst_2672_: *mut LeanObject,
    mut v_inst_2673_: *mut LeanObject,
    mut v_t_2674_: *mut LeanObject,
    mut v_k_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2676_: *mut LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Std_ExtTreeSet_getGE_x21(
        v_00_u03b1_2670_,
        v_cmp_2671_,
        v_inst_2672_,
        v_inst_2673_,
        v_t_2674_,
        v_k_2675_,
    );
    lean_dec(v_inst_2673_);
    return v_res_2676_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21___redArg(
    mut v_cmp_2677_: *mut LeanObject,
    mut v_inst_2678_: *mut LeanObject,
    mut v_t_2679_: *mut LeanObject,
    mut v_k_2680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    v___x_2681_ = lean_box(0);
    v___x_2682_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2677_,
        v_k_2680_,
        v___x_2681_,
        v_t_2679_,
    );
    if lean_obj_tag(v___x_2682_) == 0 {
        let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
        v___x_2683_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2684_ = l_panic___redArg(v_inst_2678_, v___x_2683_);
        return v___x_2684_;
    } else {
        let mut v_val_2685_: *mut LeanObject = core::ptr::null_mut();
        v_val_2685_ = lean_ctor_get(v___x_2682_, 0);
        lean_inc(v_val_2685_);
        lean_dec_ref_known(v___x_2682_, 1);
        return v_val_2685_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21___redArg___boxed(
    mut v_cmp_2686_: *mut LeanObject,
    mut v_inst_2687_: *mut LeanObject,
    mut v_t_2688_: *mut LeanObject,
    mut v_k_2689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2690_: *mut LeanObject = core::ptr::null_mut();
    v_res_2690_ =
        l_Std_ExtTreeSet_getGT_x21___redArg(v_cmp_2686_, v_inst_2687_, v_t_2688_, v_k_2689_);
    lean_dec(v_inst_2687_);
    return v_res_2690_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21(
    mut v_00_u03b1_2691_: *mut LeanObject,
    mut v_cmp_2692_: *mut LeanObject,
    mut v_inst_2693_: *mut LeanObject,
    mut v_inst_2694_: *mut LeanObject,
    mut v_t_2695_: *mut LeanObject,
    mut v_k_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    v___x_2697_ = lean_box(0);
    v___x_2698_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2692_,
        v_k_2696_,
        v___x_2697_,
        v_t_2695_,
    );
    if lean_obj_tag(v___x_2698_) == 0 {
        let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
        v___x_2699_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2700_ = l_panic___redArg(v_inst_2694_, v___x_2699_);
        return v___x_2700_;
    } else {
        let mut v_val_2701_: *mut LeanObject = core::ptr::null_mut();
        v_val_2701_ = lean_ctor_get(v___x_2698_, 0);
        lean_inc(v_val_2701_);
        lean_dec_ref_known(v___x_2698_, 1);
        return v_val_2701_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21___boxed(
    mut v_00_u03b1_2702_: *mut LeanObject,
    mut v_cmp_2703_: *mut LeanObject,
    mut v_inst_2704_: *mut LeanObject,
    mut v_inst_2705_: *mut LeanObject,
    mut v_t_2706_: *mut LeanObject,
    mut v_k_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2708_: *mut LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_Std_ExtTreeSet_getGT_x21(
        v_00_u03b1_2702_,
        v_cmp_2703_,
        v_inst_2704_,
        v_inst_2705_,
        v_t_2706_,
        v_k_2707_,
    );
    lean_dec(v_inst_2705_);
    return v_res_2708_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21___redArg(
    mut v_cmp_2709_: *mut LeanObject,
    mut v_inst_2710_: *mut LeanObject,
    mut v_t_2711_: *mut LeanObject,
    mut v_k_2712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___x_2713_ = lean_box(0);
    v___x_2714_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2709_,
        v_k_2712_,
        v___x_2713_,
        v_t_2711_,
    );
    if lean_obj_tag(v___x_2714_) == 0 {
        let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
        v___x_2715_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2716_ = l_panic___redArg(v_inst_2710_, v___x_2715_);
        return v___x_2716_;
    } else {
        let mut v_val_2717_: *mut LeanObject = core::ptr::null_mut();
        v_val_2717_ = lean_ctor_get(v___x_2714_, 0);
        lean_inc(v_val_2717_);
        lean_dec_ref_known(v___x_2714_, 1);
        return v_val_2717_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21___redArg___boxed(
    mut v_cmp_2718_: *mut LeanObject,
    mut v_inst_2719_: *mut LeanObject,
    mut v_t_2720_: *mut LeanObject,
    mut v_k_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2722_: *mut LeanObject = core::ptr::null_mut();
    v_res_2722_ =
        l_Std_ExtTreeSet_getLE_x21___redArg(v_cmp_2718_, v_inst_2719_, v_t_2720_, v_k_2721_);
    lean_dec(v_inst_2719_);
    return v_res_2722_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21(
    mut v_00_u03b1_2723_: *mut LeanObject,
    mut v_cmp_2724_: *mut LeanObject,
    mut v_inst_2725_: *mut LeanObject,
    mut v_inst_2726_: *mut LeanObject,
    mut v_t_2727_: *mut LeanObject,
    mut v_k_2728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    v___x_2729_ = lean_box(0);
    v___x_2730_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2724_,
        v_k_2728_,
        v___x_2729_,
        v_t_2727_,
    );
    if lean_obj_tag(v___x_2730_) == 0 {
        let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
        v___x_2731_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2732_ = l_panic___redArg(v_inst_2726_, v___x_2731_);
        return v___x_2732_;
    } else {
        let mut v_val_2733_: *mut LeanObject = core::ptr::null_mut();
        v_val_2733_ = lean_ctor_get(v___x_2730_, 0);
        lean_inc(v_val_2733_);
        lean_dec_ref_known(v___x_2730_, 1);
        return v_val_2733_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21___boxed(
    mut v_00_u03b1_2734_: *mut LeanObject,
    mut v_cmp_2735_: *mut LeanObject,
    mut v_inst_2736_: *mut LeanObject,
    mut v_inst_2737_: *mut LeanObject,
    mut v_t_2738_: *mut LeanObject,
    mut v_k_2739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2740_: *mut LeanObject = core::ptr::null_mut();
    v_res_2740_ = l_Std_ExtTreeSet_getLE_x21(
        v_00_u03b1_2734_,
        v_cmp_2735_,
        v_inst_2736_,
        v_inst_2737_,
        v_t_2738_,
        v_k_2739_,
    );
    lean_dec(v_inst_2737_);
    return v_res_2740_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21___redArg(
    mut v_cmp_2741_: *mut LeanObject,
    mut v_inst_2742_: *mut LeanObject,
    mut v_t_2743_: *mut LeanObject,
    mut v_k_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v___x_2745_ = lean_box(0);
    v___x_2746_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2741_,
        v_k_2744_,
        v___x_2745_,
        v_t_2743_,
    );
    if lean_obj_tag(v___x_2746_) == 0 {
        let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
        v___x_2747_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2748_ = l_panic___redArg(v_inst_2742_, v___x_2747_);
        return v___x_2748_;
    } else {
        let mut v_val_2749_: *mut LeanObject = core::ptr::null_mut();
        v_val_2749_ = lean_ctor_get(v___x_2746_, 0);
        lean_inc(v_val_2749_);
        lean_dec_ref_known(v___x_2746_, 1);
        return v_val_2749_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21___redArg___boxed(
    mut v_cmp_2750_: *mut LeanObject,
    mut v_inst_2751_: *mut LeanObject,
    mut v_t_2752_: *mut LeanObject,
    mut v_k_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2754_: *mut LeanObject = core::ptr::null_mut();
    v_res_2754_ =
        l_Std_ExtTreeSet_getLT_x21___redArg(v_cmp_2750_, v_inst_2751_, v_t_2752_, v_k_2753_);
    lean_dec(v_inst_2751_);
    return v_res_2754_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21(
    mut v_00_u03b1_2755_: *mut LeanObject,
    mut v_cmp_2756_: *mut LeanObject,
    mut v_inst_2757_: *mut LeanObject,
    mut v_inst_2758_: *mut LeanObject,
    mut v_t_2759_: *mut LeanObject,
    mut v_k_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    v___x_2761_ = lean_box(0);
    v___x_2762_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2756_,
        v_k_2760_,
        v___x_2761_,
        v_t_2759_,
    );
    if lean_obj_tag(v___x_2762_) == 0 {
        let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
        v___x_2763_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2764_ = l_panic___redArg(v_inst_2758_, v___x_2763_);
        return v___x_2764_;
    } else {
        let mut v_val_2765_: *mut LeanObject = core::ptr::null_mut();
        v_val_2765_ = lean_ctor_get(v___x_2762_, 0);
        lean_inc(v_val_2765_);
        lean_dec_ref_known(v___x_2762_, 1);
        return v_val_2765_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21___boxed(
    mut v_00_u03b1_2766_: *mut LeanObject,
    mut v_cmp_2767_: *mut LeanObject,
    mut v_inst_2768_: *mut LeanObject,
    mut v_inst_2769_: *mut LeanObject,
    mut v_t_2770_: *mut LeanObject,
    mut v_k_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2772_: *mut LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Std_ExtTreeSet_getLT_x21(
        v_00_u03b1_2766_,
        v_cmp_2767_,
        v_inst_2768_,
        v_inst_2769_,
        v_t_2770_,
        v_k_2771_,
    );
    lean_dec(v_inst_2769_);
    return v_res_2772_;
}
pub unsafe fn l_Std_ExtTreeSet_getGED___redArg(
    mut v_cmp_2773_: *mut LeanObject,
    mut v_t_2774_: *mut LeanObject,
    mut v_k_2775_: *mut LeanObject,
    mut v_fallback_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2777_ = lean_box(0);
    v___x_2778_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2773_,
        v_k_2775_,
        v___x_2777_,
        v_t_2774_,
    );
    if lean_obj_tag(v___x_2778_) == 0 {
        lean_inc(v_fallback_2776_);
        return v_fallback_2776_;
    } else {
        let mut v_val_2779_: *mut LeanObject = core::ptr::null_mut();
        v_val_2779_ = lean_ctor_get(v___x_2778_, 0);
        lean_inc(v_val_2779_);
        lean_dec_ref_known(v___x_2778_, 1);
        return v_val_2779_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGED___redArg___boxed(
    mut v_cmp_2780_: *mut LeanObject,
    mut v_t_2781_: *mut LeanObject,
    mut v_k_2782_: *mut LeanObject,
    mut v_fallback_2783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2784_: *mut LeanObject = core::ptr::null_mut();
    v_res_2784_ =
        l_Std_ExtTreeSet_getGED___redArg(v_cmp_2780_, v_t_2781_, v_k_2782_, v_fallback_2783_);
    lean_dec(v_fallback_2783_);
    return v_res_2784_;
}
pub unsafe fn l_Std_ExtTreeSet_getGED(
    mut v_00_u03b1_2785_: *mut LeanObject,
    mut v_cmp_2786_: *mut LeanObject,
    mut v_inst_2787_: *mut LeanObject,
    mut v_t_2788_: *mut LeanObject,
    mut v_k_2789_: *mut LeanObject,
    mut v_fallback_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    v___x_2791_ = lean_box(0);
    v___x_2792_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2786_,
        v_k_2789_,
        v___x_2791_,
        v_t_2788_,
    );
    if lean_obj_tag(v___x_2792_) == 0 {
        lean_inc(v_fallback_2790_);
        return v_fallback_2790_;
    } else {
        let mut v_val_2793_: *mut LeanObject = core::ptr::null_mut();
        v_val_2793_ = lean_ctor_get(v___x_2792_, 0);
        lean_inc(v_val_2793_);
        lean_dec_ref_known(v___x_2792_, 1);
        return v_val_2793_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGED___boxed(
    mut v_00_u03b1_2794_: *mut LeanObject,
    mut v_cmp_2795_: *mut LeanObject,
    mut v_inst_2796_: *mut LeanObject,
    mut v_t_2797_: *mut LeanObject,
    mut v_k_2798_: *mut LeanObject,
    mut v_fallback_2799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2800_: *mut LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_Std_ExtTreeSet_getGED(
        v_00_u03b1_2794_,
        v_cmp_2795_,
        v_inst_2796_,
        v_t_2797_,
        v_k_2798_,
        v_fallback_2799_,
    );
    lean_dec(v_fallback_2799_);
    return v_res_2800_;
}
pub unsafe fn l_Std_ExtTreeSet_getGTD___redArg(
    mut v_cmp_2801_: *mut LeanObject,
    mut v_t_2802_: *mut LeanObject,
    mut v_k_2803_: *mut LeanObject,
    mut v_fallback_2804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    v___x_2805_ = lean_box(0);
    v___x_2806_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2801_,
        v_k_2803_,
        v___x_2805_,
        v_t_2802_,
    );
    if lean_obj_tag(v___x_2806_) == 0 {
        lean_inc(v_fallback_2804_);
        return v_fallback_2804_;
    } else {
        let mut v_val_2807_: *mut LeanObject = core::ptr::null_mut();
        v_val_2807_ = lean_ctor_get(v___x_2806_, 0);
        lean_inc(v_val_2807_);
        lean_dec_ref_known(v___x_2806_, 1);
        return v_val_2807_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGTD___redArg___boxed(
    mut v_cmp_2808_: *mut LeanObject,
    mut v_t_2809_: *mut LeanObject,
    mut v_k_2810_: *mut LeanObject,
    mut v_fallback_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2812_: *mut LeanObject = core::ptr::null_mut();
    v_res_2812_ =
        l_Std_ExtTreeSet_getGTD___redArg(v_cmp_2808_, v_t_2809_, v_k_2810_, v_fallback_2811_);
    lean_dec(v_fallback_2811_);
    return v_res_2812_;
}
pub unsafe fn l_Std_ExtTreeSet_getGTD(
    mut v_00_u03b1_2813_: *mut LeanObject,
    mut v_cmp_2814_: *mut LeanObject,
    mut v_inst_2815_: *mut LeanObject,
    mut v_t_2816_: *mut LeanObject,
    mut v_k_2817_: *mut LeanObject,
    mut v_fallback_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    v___x_2819_ = lean_box(0);
    v___x_2820_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2814_,
        v_k_2817_,
        v___x_2819_,
        v_t_2816_,
    );
    if lean_obj_tag(v___x_2820_) == 0 {
        lean_inc(v_fallback_2818_);
        return v_fallback_2818_;
    } else {
        let mut v_val_2821_: *mut LeanObject = core::ptr::null_mut();
        v_val_2821_ = lean_ctor_get(v___x_2820_, 0);
        lean_inc(v_val_2821_);
        lean_dec_ref_known(v___x_2820_, 1);
        return v_val_2821_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGTD___boxed(
    mut v_00_u03b1_2822_: *mut LeanObject,
    mut v_cmp_2823_: *mut LeanObject,
    mut v_inst_2824_: *mut LeanObject,
    mut v_t_2825_: *mut LeanObject,
    mut v_k_2826_: *mut LeanObject,
    mut v_fallback_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2828_: *mut LeanObject = core::ptr::null_mut();
    v_res_2828_ = l_Std_ExtTreeSet_getGTD(
        v_00_u03b1_2822_,
        v_cmp_2823_,
        v_inst_2824_,
        v_t_2825_,
        v_k_2826_,
        v_fallback_2827_,
    );
    lean_dec(v_fallback_2827_);
    return v_res_2828_;
}
pub unsafe fn l_Std_ExtTreeSet_getLED___redArg(
    mut v_cmp_2829_: *mut LeanObject,
    mut v_t_2830_: *mut LeanObject,
    mut v_k_2831_: *mut LeanObject,
    mut v_fallback_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    v___x_2833_ = lean_box(0);
    v___x_2834_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2829_,
        v_k_2831_,
        v___x_2833_,
        v_t_2830_,
    );
    if lean_obj_tag(v___x_2834_) == 0 {
        lean_inc(v_fallback_2832_);
        return v_fallback_2832_;
    } else {
        let mut v_val_2835_: *mut LeanObject = core::ptr::null_mut();
        v_val_2835_ = lean_ctor_get(v___x_2834_, 0);
        lean_inc(v_val_2835_);
        lean_dec_ref_known(v___x_2834_, 1);
        return v_val_2835_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLED___redArg___boxed(
    mut v_cmp_2836_: *mut LeanObject,
    mut v_t_2837_: *mut LeanObject,
    mut v_k_2838_: *mut LeanObject,
    mut v_fallback_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2840_: *mut LeanObject = core::ptr::null_mut();
    v_res_2840_ =
        l_Std_ExtTreeSet_getLED___redArg(v_cmp_2836_, v_t_2837_, v_k_2838_, v_fallback_2839_);
    lean_dec(v_fallback_2839_);
    return v_res_2840_;
}
pub unsafe fn l_Std_ExtTreeSet_getLED(
    mut v_00_u03b1_2841_: *mut LeanObject,
    mut v_cmp_2842_: *mut LeanObject,
    mut v_inst_2843_: *mut LeanObject,
    mut v_t_2844_: *mut LeanObject,
    mut v_k_2845_: *mut LeanObject,
    mut v_fallback_2846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    v___x_2847_ = lean_box(0);
    v___x_2848_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2842_,
        v_k_2845_,
        v___x_2847_,
        v_t_2844_,
    );
    if lean_obj_tag(v___x_2848_) == 0 {
        lean_inc(v_fallback_2846_);
        return v_fallback_2846_;
    } else {
        let mut v_val_2849_: *mut LeanObject = core::ptr::null_mut();
        v_val_2849_ = lean_ctor_get(v___x_2848_, 0);
        lean_inc(v_val_2849_);
        lean_dec_ref_known(v___x_2848_, 1);
        return v_val_2849_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLED___boxed(
    mut v_00_u03b1_2850_: *mut LeanObject,
    mut v_cmp_2851_: *mut LeanObject,
    mut v_inst_2852_: *mut LeanObject,
    mut v_t_2853_: *mut LeanObject,
    mut v_k_2854_: *mut LeanObject,
    mut v_fallback_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2856_: *mut LeanObject = core::ptr::null_mut();
    v_res_2856_ = l_Std_ExtTreeSet_getLED(
        v_00_u03b1_2850_,
        v_cmp_2851_,
        v_inst_2852_,
        v_t_2853_,
        v_k_2854_,
        v_fallback_2855_,
    );
    lean_dec(v_fallback_2855_);
    return v_res_2856_;
}
pub unsafe fn l_Std_ExtTreeSet_getLTD___redArg(
    mut v_cmp_2857_: *mut LeanObject,
    mut v_t_2858_: *mut LeanObject,
    mut v_k_2859_: *mut LeanObject,
    mut v_fallback_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    v___x_2861_ = lean_box(0);
    v___x_2862_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2857_,
        v_k_2859_,
        v___x_2861_,
        v_t_2858_,
    );
    if lean_obj_tag(v___x_2862_) == 0 {
        lean_inc(v_fallback_2860_);
        return v_fallback_2860_;
    } else {
        let mut v_val_2863_: *mut LeanObject = core::ptr::null_mut();
        v_val_2863_ = lean_ctor_get(v___x_2862_, 0);
        lean_inc(v_val_2863_);
        lean_dec_ref_known(v___x_2862_, 1);
        return v_val_2863_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLTD___redArg___boxed(
    mut v_cmp_2864_: *mut LeanObject,
    mut v_t_2865_: *mut LeanObject,
    mut v_k_2866_: *mut LeanObject,
    mut v_fallback_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2868_: *mut LeanObject = core::ptr::null_mut();
    v_res_2868_ =
        l_Std_ExtTreeSet_getLTD___redArg(v_cmp_2864_, v_t_2865_, v_k_2866_, v_fallback_2867_);
    lean_dec(v_fallback_2867_);
    return v_res_2868_;
}
pub unsafe fn l_Std_ExtTreeSet_getLTD(
    mut v_00_u03b1_2869_: *mut LeanObject,
    mut v_cmp_2870_: *mut LeanObject,
    mut v_inst_2871_: *mut LeanObject,
    mut v_t_2872_: *mut LeanObject,
    mut v_k_2873_: *mut LeanObject,
    mut v_fallback_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    v___x_2875_ = lean_box(0);
    v___x_2876_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2870_,
        v_k_2873_,
        v___x_2875_,
        v_t_2872_,
    );
    if lean_obj_tag(v___x_2876_) == 0 {
        lean_inc(v_fallback_2874_);
        return v_fallback_2874_;
    } else {
        let mut v_val_2877_: *mut LeanObject = core::ptr::null_mut();
        v_val_2877_ = lean_ctor_get(v___x_2876_, 0);
        lean_inc(v_val_2877_);
        lean_dec_ref_known(v___x_2876_, 1);
        return v_val_2877_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLTD___boxed(
    mut v_00_u03b1_2878_: *mut LeanObject,
    mut v_cmp_2879_: *mut LeanObject,
    mut v_inst_2880_: *mut LeanObject,
    mut v_t_2881_: *mut LeanObject,
    mut v_k_2882_: *mut LeanObject,
    mut v_fallback_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2884_: *mut LeanObject = core::ptr::null_mut();
    v_res_2884_ = l_Std_ExtTreeSet_getLTD(
        v_00_u03b1_2878_,
        v_cmp_2879_,
        v_inst_2880_,
        v_t_2881_,
        v_k_2882_,
        v_fallback_2883_,
    );
    lean_dec(v_fallback_2883_);
    return v_res_2884_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___redArg___lam__0(
    mut v_f_2885_: *mut LeanObject,
    mut v_a_2886_: *mut LeanObject,
    mut v_x_2887_: *mut LeanObject,
) -> u8 {
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    v___x_2888_ = lean_apply_1(v_f_2885_, v_a_2886_);
    v___x_2889_ = (lean_unbox(v___x_2888_) as u8);
    return v___x_2889_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(
    mut v_f_2890_: *mut LeanObject,
    mut v_a_2891_: *mut LeanObject,
    mut v_x_2892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2893_: u8 = 0;
    let mut v_r_2894_: *mut LeanObject = core::ptr::null_mut();
    v_res_2893_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_2890_, v_a_2891_, v_x_2892_);
    v_r_2894_ = lean_box((v_res_2893_) as usize);
    return v_r_2894_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___redArg(
    mut v_f_2895_: *mut LeanObject,
    mut v_m_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    v___f_2897_ = lean_alloc_closure(
        l_Std_ExtTreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2897_, 0, v_f_2895_);
    v___x_2898_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_2897_, v_m_2896_);
    return v___x_2898_;
}
pub unsafe fn l_Std_ExtTreeSet_filter(
    mut v_00_u03b1_2899_: *mut LeanObject,
    mut v_cmp_2900_: *mut LeanObject,
    mut v_f_2901_: *mut LeanObject,
    mut v_m_2902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    v___f_2903_ = lean_alloc_closure(
        l_Std_ExtTreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2903_, 0, v_f_2901_);
    v___x_2904_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_2903_, v_m_2902_);
    return v___x_2904_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___boxed(
    mut v_00_u03b1_2905_: *mut LeanObject,
    mut v_cmp_2906_: *mut LeanObject,
    mut v_f_2907_: *mut LeanObject,
    mut v_m_2908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2909_: *mut LeanObject = core::ptr::null_mut();
    v_res_2909_ = l_Std_ExtTreeSet_filter(v_00_u03b1_2905_, v_cmp_2906_, v_f_2907_, v_m_2908_);
    lean_dec_ref(v_cmp_2906_);
    return v_res_2909_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM___redArg___lam__0(
    mut v_f_2910_: *mut LeanObject,
    mut v_c_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
    mut v_x_2913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ = lean_apply_2(v_f_2910_, v_c_2911_, v_a_2912_);
    return v___x_2914_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM___redArg(
    mut v_inst_2915_: *mut LeanObject,
    mut v_f_2916_: *mut LeanObject,
    mut v_init_2917_: *mut LeanObject,
    mut v_t_2918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    v___f_2919_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2919_, 0, v_f_2916_);
    v___x_2920_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2915_,
        v___f_2919_,
        v_init_2917_,
        v_t_2918_,
    );
    return v___x_2920_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM(
    mut v_00_u03b1_2921_: *mut LeanObject,
    mut v_cmp_2922_: *mut LeanObject,
    mut v_00_u03b4_2923_: *mut LeanObject,
    mut v_m_2924_: *mut LeanObject,
    mut v_inst_2925_: *mut LeanObject,
    mut v_inst_2926_: *mut LeanObject,
    mut v_inst_2927_: *mut LeanObject,
    mut v_f_2928_: *mut LeanObject,
    mut v_init_2929_: *mut LeanObject,
    mut v_t_2930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    v___f_2931_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2931_, 0, v_f_2928_);
    v___x_2932_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2925_,
        v___f_2931_,
        v_init_2929_,
        v_t_2930_,
    );
    return v___x_2932_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM___boxed(
    mut v_00_u03b1_2933_: *mut LeanObject,
    mut v_cmp_2934_: *mut LeanObject,
    mut v_00_u03b4_2935_: *mut LeanObject,
    mut v_m_2936_: *mut LeanObject,
    mut v_inst_2937_: *mut LeanObject,
    mut v_inst_2938_: *mut LeanObject,
    mut v_inst_2939_: *mut LeanObject,
    mut v_f_2940_: *mut LeanObject,
    mut v_init_2941_: *mut LeanObject,
    mut v_t_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2943_: *mut LeanObject = core::ptr::null_mut();
    v_res_2943_ = l_Std_ExtTreeSet_foldlM(
        v_00_u03b1_2933_,
        v_cmp_2934_,
        v_00_u03b4_2935_,
        v_m_2936_,
        v_inst_2937_,
        v_inst_2938_,
        v_inst_2939_,
        v_f_2940_,
        v_init_2941_,
        v_t_2942_,
    );
    lean_dec_ref(v_cmp_2934_);
    return v_res_2943_;
}
pub unsafe fn l_Std_ExtTreeSet_foldl___redArg(
    mut v_f_2944_: *mut LeanObject,
    mut v_init_2945_: *mut LeanObject,
    mut v_t_2946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___f_2947_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2947_, 0, v_f_2944_);
    v___x_2948_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2947_, v_init_2945_, v_t_2946_);
    return v___x_2948_;
}
pub unsafe fn l_Std_ExtTreeSet_foldl(
    mut v_00_u03b1_2949_: *mut LeanObject,
    mut v_cmp_2950_: *mut LeanObject,
    mut v_00_u03b4_2951_: *mut LeanObject,
    mut v_inst_2952_: *mut LeanObject,
    mut v_f_2953_: *mut LeanObject,
    mut v_init_2954_: *mut LeanObject,
    mut v_t_2955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    v___f_2956_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2956_, 0, v_f_2953_);
    v___x_2957_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2956_, v_init_2954_, v_t_2955_);
    return v___x_2957_;
}
pub unsafe fn l_Std_ExtTreeSet_foldl___boxed(
    mut v_00_u03b1_2958_: *mut LeanObject,
    mut v_cmp_2959_: *mut LeanObject,
    mut v_00_u03b4_2960_: *mut LeanObject,
    mut v_inst_2961_: *mut LeanObject,
    mut v_f_2962_: *mut LeanObject,
    mut v_init_2963_: *mut LeanObject,
    mut v_t_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Std_ExtTreeSet_foldl(
        v_00_u03b1_2958_,
        v_cmp_2959_,
        v_00_u03b4_2960_,
        v_inst_2961_,
        v_f_2962_,
        v_init_2963_,
        v_t_2964_,
    );
    lean_dec_ref(v_cmp_2959_);
    return v_res_2965_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM___redArg___lam__0(
    mut v_f_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
    mut v_x_2968_: *mut LeanObject,
    mut v_acc_2969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    v___x_2970_ = lean_apply_2(v_f_2966_, v_a_2967_, v_acc_2969_);
    return v___x_2970_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM___redArg(
    mut v_inst_2971_: *mut LeanObject,
    mut v_f_2972_: *mut LeanObject,
    mut v_init_2973_: *mut LeanObject,
    mut v_t_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___f_2975_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2975_, 0, v_f_2972_);
    v___x_2976_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2971_,
        v___f_2975_,
        v_init_2973_,
        v_t_2974_,
    );
    return v___x_2976_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM(
    mut v_00_u03b1_2977_: *mut LeanObject,
    mut v_cmp_2978_: *mut LeanObject,
    mut v_00_u03b4_2979_: *mut LeanObject,
    mut v_m_2980_: *mut LeanObject,
    mut v_inst_2981_: *mut LeanObject,
    mut v_inst_2982_: *mut LeanObject,
    mut v_inst_2983_: *mut LeanObject,
    mut v_f_2984_: *mut LeanObject,
    mut v_init_2985_: *mut LeanObject,
    mut v_t_2986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    v___f_2987_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2987_, 0, v_f_2984_);
    v___x_2988_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2981_,
        v___f_2987_,
        v_init_2985_,
        v_t_2986_,
    );
    return v___x_2988_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM___boxed(
    mut v_00_u03b1_2989_: *mut LeanObject,
    mut v_cmp_2990_: *mut LeanObject,
    mut v_00_u03b4_2991_: *mut LeanObject,
    mut v_m_2992_: *mut LeanObject,
    mut v_inst_2993_: *mut LeanObject,
    mut v_inst_2994_: *mut LeanObject,
    mut v_inst_2995_: *mut LeanObject,
    mut v_f_2996_: *mut LeanObject,
    mut v_init_2997_: *mut LeanObject,
    mut v_t_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Std_ExtTreeSet_foldrM(
        v_00_u03b1_2989_,
        v_cmp_2990_,
        v_00_u03b4_2991_,
        v_m_2992_,
        v_inst_2993_,
        v_inst_2994_,
        v_inst_2995_,
        v_f_2996_,
        v_init_2997_,
        v_t_2998_,
    );
    lean_dec_ref(v_cmp_2990_);
    return v_res_2999_;
}
pub unsafe fn l_Std_ExtTreeSet_foldr___redArg___lam__0(
    mut v_f_3000_: *mut LeanObject,
    mut v_x1_3001_: *mut LeanObject,
    mut v_x2_3002_: *mut LeanObject,
    mut v_x3_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    v___x_3004_ = lean_apply_2(v_f_3000_, v_x1_3001_, v_x3_3003_);
    return v___x_3004_;
}
pub unsafe fn l_Std_ExtTreeSet_foldr___redArg(
    mut v_f_3024_: *mut LeanObject,
    mut v_init_3025_: *mut LeanObject,
    mut v_t_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    v___f_3027_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3027_, 0, v_f_3024_);
    v___x_3028_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
    v___x_3029_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3028_,
        v___f_3027_,
        v_init_3025_,
        v_t_3026_,
    );
    return v___x_3029_;
}
pub unsafe fn l_Std_ExtTreeSet_foldr(
    mut v_00_u03b1_3030_: *mut LeanObject,
    mut v_cmp_3031_: *mut LeanObject,
    mut v_00_u03b4_3032_: *mut LeanObject,
    mut v_inst_3033_: *mut LeanObject,
    mut v_f_3034_: *mut LeanObject,
    mut v_init_3035_: *mut LeanObject,
    mut v_t_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    v___f_3037_ = lean_alloc_closure(
        l_Std_ExtTreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3037_, 0, v_f_3034_);
    v___x_3038_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
    v___x_3039_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3038_,
        v___f_3037_,
        v_init_3035_,
        v_t_3036_,
    );
    return v___x_3039_;
}
pub unsafe fn l_Std_ExtTreeSet_foldr___boxed(
    mut v_00_u03b1_3040_: *mut LeanObject,
    mut v_cmp_3041_: *mut LeanObject,
    mut v_00_u03b4_3042_: *mut LeanObject,
    mut v_inst_3043_: *mut LeanObject,
    mut v_f_3044_: *mut LeanObject,
    mut v_init_3045_: *mut LeanObject,
    mut v_t_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3047_: *mut LeanObject = core::ptr::null_mut();
    v_res_3047_ = l_Std_ExtTreeSet_foldr(
        v_00_u03b1_3040_,
        v_cmp_3041_,
        v_00_u03b4_3042_,
        v_inst_3043_,
        v_f_3044_,
        v_init_3045_,
        v_t_3046_,
    );
    lean_dec_ref(v_cmp_3041_);
    return v_res_3047_;
}
pub unsafe fn l_Std_ExtTreeSet_partition___redArg___lam__0(
    mut v_f_3048_: *mut LeanObject,
    mut v_cmp_3049_: *mut LeanObject,
    mut v_x_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
    mut v_b_3052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3057_: u8 = 0;
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3053_ = lean_ctor_get(v_x_3050_, 0);
                v_snd_3054_ = lean_ctor_get(v_x_3050_, 1);
                v_isSharedCheck_3068_ = (!lean_is_exclusive(v_x_3050_)) as u8;
                if v_isSharedCheck_3068_ == 0 {
                    v___x_3056_ = v_x_3050_;
                    v_isShared_3057_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3054_);
                    lean_inc(v_fst_3053_);
                    lean_dec(v_x_3050_);
                    v___x_3056_ = lean_box(0);
                    v_isShared_3057_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_3051_);
                v___x_3058_ = lean_apply_1(v_f_3048_, v_a_3051_);
                v___x_3059_ = (lean_unbox(v___x_3058_) as u8);
                if v___x_3059_ == 0 {
                    v___x_3060_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_3049_,
                        v_a_3051_,
                        v_b_3052_,
                        v_snd_3054_,
                    );
                    if v_isShared_3057_ == 0 {
                        lean_ctor_set(v___x_3056_, 1, v___x_3060_);
                        v___x_3062_ = v___x_3056_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_fst_3053_);
                        lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3060_);
                        v___x_3062_ = v_reuseFailAlloc_3063_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3064_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_3049_,
                        v_a_3051_,
                        v_b_3052_,
                        v_fst_3053_,
                    );
                    if v_isShared_3057_ == 0 {
                        lean_ctor_set(v___x_3056_, 0, v___x_3064_);
                        v___x_3066_ = v___x_3056_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
                        lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_snd_3054_);
                        v___x_3066_ = v_reuseFailAlloc_3067_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3062_;
            }
            3 => {
                return v___x_3066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_partition___redArg(
    mut v_cmp_3071_: *mut LeanObject,
    mut v_f_3072_: *mut LeanObject,
    mut v_t_3073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3081_: u8 = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3074_ = lean_alloc_closure(
                    l_Std_ExtTreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_3074_, 0, v_f_3072_);
                lean_closure_set(v___f_3074_, 1, v_cmp_3071_);
                v___x_3075_ = l_Std_ExtTreeSet_partition___redArg___closed__0;
                v_p_3076_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3074_,
                    v___x_3075_,
                    v_t_3073_,
                );
                v_fst_3077_ = lean_ctor_get(v_p_3076_, 0);
                v_snd_3078_ = lean_ctor_get(v_p_3076_, 1);
                v_isSharedCheck_3085_ = (!lean_is_exclusive(v_p_3076_)) as u8;
                if v_isSharedCheck_3085_ == 0 {
                    v___x_3080_ = v_p_3076_;
                    v_isShared_3081_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3078_);
                    lean_inc(v_fst_3077_);
                    lean_dec(v_p_3076_);
                    v___x_3080_ = lean_box(0);
                    v_isShared_3081_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3081_ == 0 {
                    v___x_3083_ = v___x_3080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_fst_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_snd_3078_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_partition(
    mut v_00_u03b1_3086_: *mut LeanObject,
    mut v_cmp_3087_: *mut LeanObject,
    mut v_inst_3088_: *mut LeanObject,
    mut v_f_3089_: *mut LeanObject,
    mut v_t_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3091_ = lean_alloc_closure(
                    l_Std_ExtTreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_3091_, 0, v_f_3089_);
                lean_closure_set(v___f_3091_, 1, v_cmp_3087_);
                v___x_3092_ = l_Std_ExtTreeSet_partition___redArg___closed__0;
                v_p_3093_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3091_,
                    v___x_3092_,
                    v_t_3090_,
                );
                v_fst_3094_ = lean_ctor_get(v_p_3093_, 0);
                v_snd_3095_ = lean_ctor_get(v_p_3093_, 1);
                v_isSharedCheck_3102_ = (!lean_is_exclusive(v_p_3093_)) as u8;
                if v_isSharedCheck_3102_ == 0 {
                    v___x_3097_ = v_p_3093_;
                    v_isShared_3098_ = v_isSharedCheck_3102_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3095_);
                    lean_inc(v_fst_3094_);
                    lean_dec(v_p_3093_);
                    v___x_3097_ = lean_box(0);
                    v_isShared_3098_ = v_isSharedCheck_3102_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3098_ == 0 {
                    v___x_3100_ = v___x_3097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_fst_3094_);
                    lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_snd_3095_);
                    v___x_3100_ = v_reuseFailAlloc_3101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_forM___redArg___lam__0(
    mut v_f_3103_: *mut LeanObject,
    mut v_x_3104_: *mut LeanObject,
    mut v_k_3105_: *mut LeanObject,
    mut v_v_3106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    v___x_3107_ = lean_apply_1(v_f_3103_, v_k_3105_);
    return v___x_3107_;
}
pub unsafe fn l_Std_ExtTreeSet_forM___redArg(
    mut v_inst_3108_: *mut LeanObject,
    mut v_f_3109_: *mut LeanObject,
    mut v_t_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    v___f_3111_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3111_, 0, v_f_3109_);
    v___x_3112_ = lean_box(0);
    v___x_3113_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3108_,
        v___f_3111_,
        v___x_3112_,
        v_t_3110_,
    );
    return v___x_3113_;
}
pub unsafe fn l_Std_ExtTreeSet_forM(
    mut v_00_u03b1_3114_: *mut LeanObject,
    mut v_cmp_3115_: *mut LeanObject,
    mut v_m_3116_: *mut LeanObject,
    mut v_inst_3117_: *mut LeanObject,
    mut v_inst_3118_: *mut LeanObject,
    mut v_inst_3119_: *mut LeanObject,
    mut v_f_3120_: *mut LeanObject,
    mut v_t_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    v___f_3122_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3122_, 0, v_f_3120_);
    v___x_3123_ = lean_box(0);
    v___x_3124_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3117_,
        v___f_3122_,
        v___x_3123_,
        v_t_3121_,
    );
    return v___x_3124_;
}
pub unsafe fn l_Std_ExtTreeSet_forM___boxed(
    mut v_00_u03b1_3125_: *mut LeanObject,
    mut v_cmp_3126_: *mut LeanObject,
    mut v_m_3127_: *mut LeanObject,
    mut v_inst_3128_: *mut LeanObject,
    mut v_inst_3129_: *mut LeanObject,
    mut v_inst_3130_: *mut LeanObject,
    mut v_f_3131_: *mut LeanObject,
    mut v_t_3132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3133_: *mut LeanObject = core::ptr::null_mut();
    v_res_3133_ = l_Std_ExtTreeSet_forM(
        v_00_u03b1_3125_,
        v_cmp_3126_,
        v_m_3127_,
        v_inst_3128_,
        v_inst_3129_,
        v_inst_3130_,
        v_f_3131_,
        v_t_3132_,
    );
    lean_dec_ref(v_cmp_3126_);
    return v_res_3133_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___redArg___lam__0(
    mut v_f_3134_: *mut LeanObject,
    mut v_a_3135_: *mut LeanObject,
    mut v_b_3136_: *mut LeanObject,
    mut v_c_3137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    v___x_3138_ = lean_apply_2(v_f_3134_, v_a_3135_, v_c_3137_);
    return v___x_3138_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___redArg___lam__1(
    mut v_toPure_3139_: *mut LeanObject,
    mut v_____do__lift_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    v_a_3141_ = lean_ctor_get(v_____do__lift_3140_, 0);
    lean_inc(v_a_3141_);
    lean_dec_ref(v_____do__lift_3140_);
    v___x_3142_ = lean_apply_2(v_toPure_3139_, lean_box(0), v_a_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___redArg(
    mut v_inst_3143_: *mut LeanObject,
    mut v_f_3144_: *mut LeanObject,
    mut v_init_3145_: *mut LeanObject,
    mut v_t_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3147_ = lean_ctor_get(v_inst_3143_, 0);
    v_toBind_3148_ = lean_ctor_get(v_inst_3143_, 1);
    lean_inc(v_toBind_3148_);
    v_toPure_3149_ = lean_ctor_get(v_toApplicative_3147_, 1);
    lean_inc(v_toPure_3149_);
    v___f_3150_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3150_, 0, v_f_3144_);
    v___x_3151_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3143_,
        v___f_3150_,
        v_init_3145_,
        v_t_3146_,
    );
    v___f_3152_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3152_, 0, v_toPure_3149_);
    v___x_3153_ = lean_apply_4(
        v_toBind_3148_,
        lean_box(0),
        lean_box(0),
        v___x_3151_,
        v___f_3152_,
    );
    return v___x_3153_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn(
    mut v_00_u03b1_3154_: *mut LeanObject,
    mut v_cmp_3155_: *mut LeanObject,
    mut v_00_u03b4_3156_: *mut LeanObject,
    mut v_m_3157_: *mut LeanObject,
    mut v_inst_3158_: *mut LeanObject,
    mut v_inst_3159_: *mut LeanObject,
    mut v_inst_3160_: *mut LeanObject,
    mut v_f_3161_: *mut LeanObject,
    mut v_init_3162_: *mut LeanObject,
    mut v_t_3163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3164_ = lean_ctor_get(v_inst_3158_, 0);
    v_toBind_3165_ = lean_ctor_get(v_inst_3158_, 1);
    lean_inc(v_toBind_3165_);
    v_toPure_3166_ = lean_ctor_get(v_toApplicative_3164_, 1);
    lean_inc(v_toPure_3166_);
    v___f_3167_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3167_, 0, v_f_3161_);
    v___x_3168_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3158_,
        v___f_3167_,
        v_init_3162_,
        v_t_3163_,
    );
    v___f_3169_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3169_, 0, v_toPure_3166_);
    v___x_3170_ = lean_apply_4(
        v_toBind_3165_,
        lean_box(0),
        lean_box(0),
        v___x_3168_,
        v___f_3169_,
    );
    return v___x_3170_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___boxed(
    mut v_00_u03b1_3171_: *mut LeanObject,
    mut v_cmp_3172_: *mut LeanObject,
    mut v_00_u03b4_3173_: *mut LeanObject,
    mut v_m_3174_: *mut LeanObject,
    mut v_inst_3175_: *mut LeanObject,
    mut v_inst_3176_: *mut LeanObject,
    mut v_inst_3177_: *mut LeanObject,
    mut v_f_3178_: *mut LeanObject,
    mut v_init_3179_: *mut LeanObject,
    mut v_t_3180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3181_: *mut LeanObject = core::ptr::null_mut();
    v_res_3181_ = l_Std_ExtTreeSet_forIn(
        v_00_u03b1_3171_,
        v_cmp_3172_,
        v_00_u03b4_3173_,
        v_m_3174_,
        v_inst_3175_,
        v_inst_3176_,
        v_inst_3177_,
        v_f_3178_,
        v_init_3179_,
        v_t_3180_,
    );
    lean_dec_ref(v_cmp_3172_);
    return v_res_3181_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(
    mut v_inst_3182_: *mut LeanObject,
    mut v_t_3183_: *mut LeanObject,
    mut v_f_3184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    v___f_3185_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3185_, 0, v_f_3184_);
    v___x_3186_ = lean_box(0);
    v___x_3187_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3182_,
        v___f_3185_,
        v___x_3186_,
        v_t_3183_,
    );
    return v___x_3187_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3189_: *mut LeanObject = core::ptr::null_mut();
    v___f_3189_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3189_, 0, v_inst_3188_);
    return v___f_3189_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_3190_: *mut LeanObject,
    mut v_cmp_3191_: *mut LeanObject,
    mut v_m_3192_: *mut LeanObject,
    mut v_inst_3193_: *mut LeanObject,
    mut v_inst_3194_: *mut LeanObject,
    mut v_inst_3195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3196_: *mut LeanObject = core::ptr::null_mut();
    v___f_3196_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3196_, 0, v_inst_3194_);
    return v___f_3196_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_3197_: *mut LeanObject,
    mut v_cmp_3198_: *mut LeanObject,
    mut v_m_3199_: *mut LeanObject,
    mut v_inst_3200_: *mut LeanObject,
    mut v_inst_3201_: *mut LeanObject,
    mut v_inst_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3203_: *mut LeanObject = core::ptr::null_mut();
    v_res_3203_ = l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(
        v_00_u03b1_3197_,
        v_cmp_3198_,
        v_m_3199_,
        v_inst_3200_,
        v_inst_3201_,
        v_inst_3202_,
    );
    lean_dec_ref(v_cmp_3198_);
    return v_res_3203_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(
    mut v_inst_3204_: *mut LeanObject,
    mut v_00_u03b2_3205_: *mut LeanObject,
    mut v_m_3206_: *mut LeanObject,
    mut v_init_3207_: *mut LeanObject,
    mut v_f_3208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3209_ = lean_ctor_get(v_inst_3204_, 0);
    v_toBind_3210_ = lean_ctor_get(v_inst_3204_, 1);
    lean_inc(v_toBind_3210_);
    v_toPure_3211_ = lean_ctor_get(v_toApplicative_3209_, 1);
    lean_inc(v_toPure_3211_);
    v___f_3212_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3212_, 0, v_f_3208_);
    v___x_3213_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3204_,
        v___f_3212_,
        v_init_3207_,
        v_m_3206_,
    );
    v___f_3214_ = lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3214_, 0, v_toPure_3211_);
    v___x_3215_ = lean_apply_4(
        v_toBind_3210_,
        lean_box(0),
        lean_box(0),
        v___x_3213_,
        v___f_3214_,
    );
    return v___x_3215_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_3216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3217_: *mut LeanObject = core::ptr::null_mut();
    v___f_3217_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3217_, 0, v_inst_3216_);
    return v___f_3217_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_3218_: *mut LeanObject,
    mut v_cmp_3219_: *mut LeanObject,
    mut v_m_3220_: *mut LeanObject,
    mut v_inst_3221_: *mut LeanObject,
    mut v_inst_3222_: *mut LeanObject,
    mut v_inst_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3224_: *mut LeanObject = core::ptr::null_mut();
    v___f_3224_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3224_, 0, v_inst_3222_);
    return v___f_3224_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_3225_: *mut LeanObject,
    mut v_cmp_3226_: *mut LeanObject,
    mut v_m_3227_: *mut LeanObject,
    mut v_inst_3228_: *mut LeanObject,
    mut v_inst_3229_: *mut LeanObject,
    mut v_inst_3230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3231_: *mut LeanObject = core::ptr::null_mut();
    v_res_3231_ = l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(
        v_00_u03b1_3225_,
        v_cmp_3226_,
        v_m_3227_,
        v_inst_3228_,
        v_inst_3229_,
        v_inst_3230_,
    );
    lean_dec_ref(v_cmp_3226_);
    return v_res_3231_;
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg___lam__0(
    mut v_p_3232_: *mut LeanObject,
    mut v___x_3233_: *mut LeanObject,
    mut v___x_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_b_3236_: *mut LeanObject,
    mut v_acc_3237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    v___x_3238_ = lean_apply_1(v_p_3232_, v_a_3235_);
    v___x_3239_ = (lean_unbox(v___x_3238_) as u8);
    if v___x_3239_ == 0 {
        let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
        v___x_3240_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3240_, 0, v___x_3233_);
        return v___x_3240_;
    } else {
        let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_3233_);
        v___x_3241_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3241_, 0, v___x_3238_);
        v___x_3242_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3242_, 0, v___x_3241_);
        lean_ctor_set(v___x_3242_, 1, v___x_3234_);
        v___x_3243_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3243_, 0, v___x_3242_);
        return v___x_3243_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg___lam__0___boxed(
    mut v_p_3244_: *mut LeanObject,
    mut v___x_3245_: *mut LeanObject,
    mut v___x_3246_: *mut LeanObject,
    mut v_a_3247_: *mut LeanObject,
    mut v_b_3248_: *mut LeanObject,
    mut v_acc_3249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3250_: *mut LeanObject = core::ptr::null_mut();
    v_res_3250_ = l_Std_ExtTreeSet_any___redArg___lam__0(
        v_p_3244_,
        v___x_3245_,
        v___x_3246_,
        v_a_3247_,
        v_b_3248_,
        v_acc_3249_,
    );
    lean_dec_ref(v_acc_3249_);
    return v_res_3250_;
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg(
    mut v_t_3254_: *mut LeanObject,
    mut v_p_3255_: *mut LeanObject,
) -> u8 {
    let mut v___y_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: u8 = 0;
    let mut v_val_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3262_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3263_ = lean_box(0);
                v___x_3264_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3265_ = lean_alloc_closure(
                    l_Std_ExtTreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3265_, 0, v_p_3255_);
                lean_closure_set(v___f_3265_, 1, v___x_3264_);
                lean_closure_set(v___f_3265_, 2, v___x_3263_);
                v___x_3266_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3262_,
                    v___f_3265_,
                    v___x_3264_,
                    v_t_3254_,
                );
                v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                lean_inc(v_a_3267_);
                lean_dec(v___x_3266_);
                v___y_3257_ = v_a_3267_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3258_ = lean_ctor_get(v___y_3257_, 0);
                lean_inc(v_fst_3258_);
                lean_dec_ref(v___y_3257_);
                if lean_obj_tag(v_fst_3258_) == 0 {
                    v___x_3259_ = 0;
                    return v___x_3259_;
                } else {
                    v_val_3260_ = lean_ctor_get(v_fst_3258_, 0);
                    lean_inc(v_val_3260_);
                    lean_dec_ref_known(v_fst_3258_, 1);
                    v___x_3261_ = (lean_unbox(v_val_3260_) as u8);
                    lean_dec(v_val_3260_);
                    return v___x_3261_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg___boxed(
    mut v_t_3268_: *mut LeanObject,
    mut v_p_3269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3270_: u8 = 0;
    let mut v_r_3271_: *mut LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Std_ExtTreeSet_any___redArg(v_t_3268_, v_p_3269_);
    v_r_3271_ = lean_box((v_res_3270_) as usize);
    return v_r_3271_;
}
pub unsafe fn l_Std_ExtTreeSet_any(
    mut v_00_u03b1_3272_: *mut LeanObject,
    mut v_cmp_3273_: *mut LeanObject,
    mut v_inst_3274_: *mut LeanObject,
    mut v_t_3275_: *mut LeanObject,
    mut v_p_3276_: *mut LeanObject,
) -> u8 {
    let mut v___y_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v_val_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3283_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3284_ = lean_box(0);
                v___x_3285_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3286_ = lean_alloc_closure(
                    l_Std_ExtTreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3286_, 0, v_p_3276_);
                lean_closure_set(v___f_3286_, 1, v___x_3285_);
                lean_closure_set(v___f_3286_, 2, v___x_3284_);
                v___x_3287_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3283_,
                    v___f_3286_,
                    v___x_3285_,
                    v_t_3275_,
                );
                v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
                lean_inc(v_a_3288_);
                lean_dec(v___x_3287_);
                v___y_3278_ = v_a_3288_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3279_ = lean_ctor_get(v___y_3278_, 0);
                lean_inc(v_fst_3279_);
                lean_dec_ref(v___y_3278_);
                if lean_obj_tag(v_fst_3279_) == 0 {
                    v___x_3280_ = 0;
                    return v___x_3280_;
                } else {
                    v_val_3281_ = lean_ctor_get(v_fst_3279_, 0);
                    lean_inc(v_val_3281_);
                    lean_dec_ref_known(v_fst_3279_, 1);
                    v___x_3282_ = (lean_unbox(v_val_3281_) as u8);
                    lean_dec(v_val_3281_);
                    return v___x_3282_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_any___boxed(
    mut v_00_u03b1_3289_: *mut LeanObject,
    mut v_cmp_3290_: *mut LeanObject,
    mut v_inst_3291_: *mut LeanObject,
    mut v_t_3292_: *mut LeanObject,
    mut v_p_3293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3294_: u8 = 0;
    let mut v_r_3295_: *mut LeanObject = core::ptr::null_mut();
    v_res_3294_ = l_Std_ExtTreeSet_any(
        v_00_u03b1_3289_,
        v_cmp_3290_,
        v_inst_3291_,
        v_t_3292_,
        v_p_3293_,
    );
    lean_dec_ref(v_cmp_3290_);
    v_r_3295_ = lean_box((v_res_3294_) as usize);
    return v_r_3295_;
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg___lam__0(
    mut v_p_3296_: *mut LeanObject,
    mut v___x_3297_: *mut LeanObject,
    mut v___x_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
    mut v_b_3300_: *mut LeanObject,
    mut v_acc_3301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: u8 = 0;
    v___x_3302_ = lean_apply_1(v_p_3296_, v_a_3299_);
    v___x_3303_ = (lean_unbox(v___x_3302_) as u8);
    if v___x_3303_ == 0 {
        let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_3298_);
        v___x_3304_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3304_, 0, v___x_3302_);
        v___x_3305_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3305_, 0, v___x_3304_);
        lean_ctor_set(v___x_3305_, 1, v___x_3297_);
        v___x_3306_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3306_, 0, v___x_3305_);
        return v___x_3306_;
    } else {
        let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
        v___x_3307_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3307_, 0, v___x_3298_);
        return v___x_3307_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg___lam__0___boxed(
    mut v_p_3308_: *mut LeanObject,
    mut v___x_3309_: *mut LeanObject,
    mut v___x_3310_: *mut LeanObject,
    mut v_a_3311_: *mut LeanObject,
    mut v_b_3312_: *mut LeanObject,
    mut v_acc_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3314_: *mut LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_Std_ExtTreeSet_all___redArg___lam__0(
        v_p_3308_,
        v___x_3309_,
        v___x_3310_,
        v_a_3311_,
        v_b_3312_,
        v_acc_3313_,
    );
    lean_dec_ref(v_acc_3313_);
    return v_res_3314_;
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg(
    mut v_t_3315_: *mut LeanObject,
    mut v_p_3316_: *mut LeanObject,
) -> u8 {
    let mut v___y_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v_val_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3323_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3324_ = lean_box(0);
                v___x_3325_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3326_ = lean_alloc_closure(
                    l_Std_ExtTreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3326_, 0, v_p_3316_);
                lean_closure_set(v___f_3326_, 1, v___x_3324_);
                lean_closure_set(v___f_3326_, 2, v___x_3325_);
                v___x_3327_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3323_,
                    v___f_3326_,
                    v___x_3325_,
                    v_t_3315_,
                );
                v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
                lean_inc(v_a_3328_);
                lean_dec(v___x_3327_);
                v___y_3318_ = v_a_3328_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3319_ = lean_ctor_get(v___y_3318_, 0);
                lean_inc(v_fst_3319_);
                lean_dec_ref(v___y_3318_);
                if lean_obj_tag(v_fst_3319_) == 0 {
                    v___x_3320_ = 1;
                    return v___x_3320_;
                } else {
                    v_val_3321_ = lean_ctor_get(v_fst_3319_, 0);
                    lean_inc(v_val_3321_);
                    lean_dec_ref_known(v_fst_3319_, 1);
                    v___x_3322_ = (lean_unbox(v_val_3321_) as u8);
                    lean_dec(v_val_3321_);
                    return v___x_3322_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg___boxed(
    mut v_t_3329_: *mut LeanObject,
    mut v_p_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3331_: u8 = 0;
    let mut v_r_3332_: *mut LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Std_ExtTreeSet_all___redArg(v_t_3329_, v_p_3330_);
    v_r_3332_ = lean_box((v_res_3331_) as usize);
    return v_r_3332_;
}
pub unsafe fn l_Std_ExtTreeSet_all(
    mut v_00_u03b1_3333_: *mut LeanObject,
    mut v_cmp_3334_: *mut LeanObject,
    mut v_inst_3335_: *mut LeanObject,
    mut v_t_3336_: *mut LeanObject,
    mut v_p_3337_: *mut LeanObject,
) -> u8 {
    let mut v___y_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v_val_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3344_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3345_ = lean_box(0);
                v___x_3346_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3347_ = lean_alloc_closure(
                    l_Std_ExtTreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                lean_closure_set(v___f_3347_, 0, v_p_3337_);
                lean_closure_set(v___f_3347_, 1, v___x_3345_);
                lean_closure_set(v___f_3347_, 2, v___x_3346_);
                v___x_3348_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3344_,
                    v___f_3347_,
                    v___x_3346_,
                    v_t_3336_,
                );
                v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
                lean_inc(v_a_3349_);
                lean_dec(v___x_3348_);
                v___y_3339_ = v_a_3349_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3340_ = lean_ctor_get(v___y_3339_, 0);
                lean_inc(v_fst_3340_);
                lean_dec_ref(v___y_3339_);
                if lean_obj_tag(v_fst_3340_) == 0 {
                    v___x_3341_ = 1;
                    return v___x_3341_;
                } else {
                    v_val_3342_ = lean_ctor_get(v_fst_3340_, 0);
                    lean_inc(v_val_3342_);
                    lean_dec_ref_known(v_fst_3340_, 1);
                    v___x_3343_ = (lean_unbox(v_val_3342_) as u8);
                    lean_dec(v_val_3342_);
                    return v___x_3343_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_all___boxed(
    mut v_00_u03b1_3350_: *mut LeanObject,
    mut v_cmp_3351_: *mut LeanObject,
    mut v_inst_3352_: *mut LeanObject,
    mut v_t_3353_: *mut LeanObject,
    mut v_p_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3355_: u8 = 0;
    let mut v_r_3356_: *mut LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Std_ExtTreeSet_all(
        v_00_u03b1_3350_,
        v_cmp_3351_,
        v_inst_3352_,
        v_t_3353_,
        v_p_3354_,
    );
    lean_dec_ref(v_cmp_3351_);
    v_r_3356_ = lean_box((v_res_3355_) as usize);
    return v_r_3356_;
}
pub unsafe fn l_Std_ExtTreeSet_toList___redArg___lam__0(
    mut v_x1_3357_: *mut LeanObject,
    mut v_x2_3358_: *mut LeanObject,
    mut v_x3_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    v___x_3360_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3360_, 0, v_x1_3357_);
    lean_ctor_set(v___x_3360_, 1, v_x3_3359_);
    return v___x_3360_;
}
pub unsafe fn l_Std_ExtTreeSet_toList___redArg(mut v_t_3362_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    v___f_3363_ = l_Std_ExtTreeSet_toList___redArg___closed__0;
    v___x_3364_ = lean_box(0);
    v___x_3365_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
    v___x_3366_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3365_,
        v___f_3363_,
        v___x_3364_,
        v_t_3362_,
    );
    return v___x_3366_;
}
pub unsafe fn l_Std_ExtTreeSet_toList(
    mut v_00_u03b1_3367_: *mut LeanObject,
    mut v_cmp_3368_: *mut LeanObject,
    mut v_inst_3369_: *mut LeanObject,
    mut v_t_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    v___f_3371_ = l_Std_ExtTreeSet_toList___redArg___closed__0;
    v___x_3372_ = lean_box(0);
    v___x_3373_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
    v___x_3374_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3373_,
        v___f_3371_,
        v___x_3372_,
        v_t_3370_,
    );
    return v___x_3374_;
}
pub unsafe fn l_Std_ExtTreeSet_toList___boxed(
    mut v_00_u03b1_3375_: *mut LeanObject,
    mut v_cmp_3376_: *mut LeanObject,
    mut v_inst_3377_: *mut LeanObject,
    mut v_t_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3379_: *mut LeanObject = core::ptr::null_mut();
    v_res_3379_ = l_Std_ExtTreeSet_toList(v_00_u03b1_3375_, v_cmp_3376_, v_inst_3377_, v_t_3378_);
    lean_dec_ref(v_cmp_3376_);
    return v_res_3379_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_ofList___auto__1() -> *mut LeanObject {
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    v___x_3380_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__26,
    );
    return v___x_3380_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(
    mut v_cmp_3381_: *mut LeanObject,
    mut v_k_3382_: *mut LeanObject,
    mut v_v_3383_: *mut LeanObject,
    mut v_t_3384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3392_: u8 = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v_impl_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: u8 = 0;
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v_size_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: u8 = 0;
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut v_unused_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_unused_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_unused_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut v_unused_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v_k_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut v_unused_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v_size_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut v_unused_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3603_: u8 = 0;
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3607_: u8 = 0;
    let mut v_unused_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut v_unused_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v_k_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3631_: u8 = 0;
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v_unused_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_unused_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_unused_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3384_) == 0 {
                    v_size_3385_ = lean_ctor_get(v_t_3384_, 0);
                    v_k_3386_ = lean_ctor_get(v_t_3384_, 1);
                    v_v_3387_ = lean_ctor_get(v_t_3384_, 2);
                    v_l_3388_ = lean_ctor_get(v_t_3384_, 3);
                    v_r_3389_ = lean_ctor_get(v_t_3384_, 4);
                    v_isSharedCheck_3670_ = (!lean_is_exclusive(v_t_3384_)) as u8;
                    if v_isSharedCheck_3670_ == 0 {
                        v___x_3391_ = v_t_3384_;
                        v_isShared_3392_ = v_isSharedCheck_3670_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3389_);
                        lean_inc(v_l_3388_);
                        lean_inc(v_v_3387_);
                        lean_inc(v_k_3386_);
                        lean_inc(v_size_3385_);
                        lean_dec(v_t_3384_);
                        v___x_3391_ = lean_box(0);
                        v_isShared_3392_ = v_isSharedCheck_3670_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_cmp_3381_);
                    v___x_3671_ = lean_unsigned_to_nat(1);
                    v___x_3672_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3672_, 0, v___x_3671_);
                    lean_ctor_set(v___x_3672_, 1, v_k_3382_);
                    lean_ctor_set(v___x_3672_, 2, v_v_3383_);
                    lean_ctor_set(v___x_3672_, 3, v_t_3384_);
                    lean_ctor_set(v___x_3672_, 4, v_t_3384_);
                    return v___x_3672_;
                }
            }
            1 => {
                lean_inc_ref(v_cmp_3381_);
                lean_inc(v_k_3386_);
                lean_inc(v_k_3382_);
                v___x_3393_ = lean_apply_2(v_cmp_3381_, v_k_3382_, v_k_3386_);
                v___x_3394_ = (lean_unbox(v___x_3393_) as u8);
                match v___x_3394_ {
                    0 => {
                        lean_dec(v_size_3385_);
                        v_impl_3395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_3381_, v_k_3382_, v_v_3383_, v_l_3388_);
                        v___x_3396_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_3389_) == 0 {
                            v_size_3397_ = lean_ctor_get(v_r_3389_, 0);
                            v_size_3398_ = lean_ctor_get(v_impl_3395_, 0);
                            lean_inc(v_size_3398_);
                            v_k_3399_ = lean_ctor_get(v_impl_3395_, 1);
                            lean_inc(v_k_3399_);
                            v_v_3400_ = lean_ctor_get(v_impl_3395_, 2);
                            lean_inc(v_v_3400_);
                            v_l_3401_ = lean_ctor_get(v_impl_3395_, 3);
                            lean_inc(v_l_3401_);
                            v_r_3402_ = lean_ctor_get(v_impl_3395_, 4);
                            lean_inc(v_r_3402_);
                            v___x_3403_ = lean_unsigned_to_nat(3);
                            v___x_3404_ = lean_nat_mul(v___x_3403_, v_size_3397_);
                            v___x_3405_ = lean_nat_dec_lt(v___x_3404_, v_size_3398_);
                            lean_dec(v___x_3404_);
                            if v___x_3405_ == 0 {
                                lean_dec(v_r_3402_);
                                lean_dec(v_l_3401_);
                                lean_dec(v_v_3400_);
                                lean_dec(v_k_3399_);
                                v___x_3406_ = lean_nat_add(v___x_3396_, v_size_3398_);
                                lean_dec(v_size_3398_);
                                v___x_3407_ = lean_nat_add(v___x_3406_, v_size_3397_);
                                lean_dec(v___x_3406_);
                                if v_isShared_3392_ == 0 {
                                    lean_ctor_set(v___x_3391_, 3, v_impl_3395_);
                                    lean_ctor_set(v___x_3391_, 0, v___x_3407_);
                                    v___x_3409_ = v___x_3391_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
                                    lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_k_3386_);
                                    lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_v_3387_);
                                    lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_impl_3395_);
                                    lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_r_3389_);
                                    v___x_3409_ = v_reuseFailAlloc_3410_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3476_ = (!lean_is_exclusive(v_impl_3395_)) as u8;
                                if v_isSharedCheck_3476_ == 0 {
                                    v_unused_3477_ = lean_ctor_get(v_impl_3395_, 4);
                                    lean_dec(v_unused_3477_);
                                    v_unused_3478_ = lean_ctor_get(v_impl_3395_, 3);
                                    lean_dec(v_unused_3478_);
                                    v_unused_3479_ = lean_ctor_get(v_impl_3395_, 2);
                                    lean_dec(v_unused_3479_);
                                    v_unused_3480_ = lean_ctor_get(v_impl_3395_, 1);
                                    lean_dec(v_unused_3480_);
                                    v_unused_3481_ = lean_ctor_get(v_impl_3395_, 0);
                                    lean_dec(v_unused_3481_);
                                    v___x_3412_ = v_impl_3395_;
                                    v_isShared_3413_ = v_isSharedCheck_3476_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_3395_);
                                    v___x_3412_ = lean_box(0);
                                    v_isShared_3413_ = v_isSharedCheck_3476_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3482_ = lean_ctor_get(v_impl_3395_, 3);
                            lean_inc(v_l_3482_);
                            if lean_obj_tag(v_l_3482_) == 0 {
                                v_r_3483_ = lean_ctor_get(v_impl_3395_, 4);
                                v_k_3484_ = lean_ctor_get(v_impl_3395_, 1);
                                v_v_3485_ = lean_ctor_get(v_impl_3395_, 2);
                                v_isSharedCheck_3496_ = (!lean_is_exclusive(v_impl_3395_)) as u8;
                                if v_isSharedCheck_3496_ == 0 {
                                    v_unused_3497_ = lean_ctor_get(v_impl_3395_, 3);
                                    lean_dec(v_unused_3497_);
                                    v_unused_3498_ = lean_ctor_get(v_impl_3395_, 0);
                                    lean_dec(v_unused_3498_);
                                    v___x_3487_ = v_impl_3395_;
                                    v_isShared_3488_ = v_isSharedCheck_3496_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_3483_);
                                    lean_inc(v_v_3485_);
                                    lean_inc(v_k_3484_);
                                    lean_dec(v_impl_3395_);
                                    v___x_3487_ = lean_box(0);
                                    v_isShared_3488_ = v_isSharedCheck_3496_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3499_ = lean_ctor_get(v_impl_3395_, 4);
                                lean_inc(v_r_3499_);
                                if lean_obj_tag(v_r_3499_) == 0 {
                                    v_k_3500_ = lean_ctor_get(v_impl_3395_, 1);
                                    v_v_3501_ = lean_ctor_get(v_impl_3395_, 2);
                                    v_isSharedCheck_3524_ =
                                        (!lean_is_exclusive(v_impl_3395_)) as u8;
                                    if v_isSharedCheck_3524_ == 0 {
                                        v_unused_3525_ = lean_ctor_get(v_impl_3395_, 4);
                                        lean_dec(v_unused_3525_);
                                        v_unused_3526_ = lean_ctor_get(v_impl_3395_, 3);
                                        lean_dec(v_unused_3526_);
                                        v_unused_3527_ = lean_ctor_get(v_impl_3395_, 0);
                                        lean_dec(v_unused_3527_);
                                        v___x_3503_ = v_impl_3395_;
                                        v_isShared_3504_ = v_isSharedCheck_3524_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3501_);
                                        lean_inc(v_k_3500_);
                                        lean_dec(v_impl_3395_);
                                        v___x_3503_ = lean_box(0);
                                        v_isShared_3504_ = v_isSharedCheck_3524_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_3528_ = lean_unsigned_to_nat(2);
                                    if v_isShared_3392_ == 0 {
                                        lean_ctor_set(v___x_3391_, 4, v_r_3499_);
                                        lean_ctor_set(v___x_3391_, 3, v_impl_3395_);
                                        lean_ctor_set(v___x_3391_, 0, v___x_3528_);
                                        v___x_3530_ = v___x_3391_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_k_3386_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_v_3387_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_impl_3395_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 4, v_r_3499_);
                                        v___x_3530_ = v_reuseFailAlloc_3531_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_3387_);
                        lean_dec(v_k_3386_);
                        lean_dec_ref(v_cmp_3381_);
                        if v_isShared_3392_ == 0 {
                            lean_ctor_set(v___x_3391_, 2, v_v_3383_);
                            lean_ctor_set(v___x_3391_, 1, v_k_3382_);
                            v___x_3533_ = v___x_3391_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_size_3385_);
                            lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_k_3382_);
                            lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_v_3383_);
                            lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_l_3388_);
                            lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_r_3389_);
                            v___x_3533_ = v_reuseFailAlloc_3534_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_3385_);
                        v_impl_3535_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_3381_, v_k_3382_, v_v_3383_, v_r_3389_);
                        v___x_3536_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_3388_) == 0 {
                            v_size_3537_ = lean_ctor_get(v_l_3388_, 0);
                            v_size_3538_ = lean_ctor_get(v_impl_3535_, 0);
                            lean_inc(v_size_3538_);
                            v_k_3539_ = lean_ctor_get(v_impl_3535_, 1);
                            lean_inc(v_k_3539_);
                            v_v_3540_ = lean_ctor_get(v_impl_3535_, 2);
                            lean_inc(v_v_3540_);
                            v_l_3541_ = lean_ctor_get(v_impl_3535_, 3);
                            lean_inc(v_l_3541_);
                            v_r_3542_ = lean_ctor_get(v_impl_3535_, 4);
                            lean_inc(v_r_3542_);
                            v___x_3543_ = lean_unsigned_to_nat(3);
                            v___x_3544_ = lean_nat_mul(v___x_3543_, v_size_3537_);
                            v___x_3545_ = lean_nat_dec_lt(v___x_3544_, v_size_3538_);
                            lean_dec(v___x_3544_);
                            if v___x_3545_ == 0 {
                                lean_dec(v_r_3542_);
                                lean_dec(v_l_3541_);
                                lean_dec(v_v_3540_);
                                lean_dec(v_k_3539_);
                                v___x_3546_ = lean_nat_add(v___x_3536_, v_size_3537_);
                                v___x_3547_ = lean_nat_add(v___x_3546_, v_size_3538_);
                                lean_dec(v_size_3538_);
                                lean_dec(v___x_3546_);
                                if v_isShared_3392_ == 0 {
                                    lean_ctor_set(v___x_3391_, 4, v_impl_3535_);
                                    lean_ctor_set(v___x_3391_, 0, v___x_3547_);
                                    v___x_3549_ = v___x_3391_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
                                    lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_k_3386_);
                                    lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_v_3387_);
                                    lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_l_3388_);
                                    lean_ctor_set(v_reuseFailAlloc_3550_, 4, v_impl_3535_);
                                    v___x_3549_ = v_reuseFailAlloc_3550_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3614_ = (!lean_is_exclusive(v_impl_3535_)) as u8;
                                if v_isSharedCheck_3614_ == 0 {
                                    v_unused_3615_ = lean_ctor_get(v_impl_3535_, 4);
                                    lean_dec(v_unused_3615_);
                                    v_unused_3616_ = lean_ctor_get(v_impl_3535_, 3);
                                    lean_dec(v_unused_3616_);
                                    v_unused_3617_ = lean_ctor_get(v_impl_3535_, 2);
                                    lean_dec(v_unused_3617_);
                                    v_unused_3618_ = lean_ctor_get(v_impl_3535_, 1);
                                    lean_dec(v_unused_3618_);
                                    v_unused_3619_ = lean_ctor_get(v_impl_3535_, 0);
                                    lean_dec(v_unused_3619_);
                                    v___x_3552_ = v_impl_3535_;
                                    v_isShared_3553_ = v_isSharedCheck_3614_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_3535_);
                                    v___x_3552_ = lean_box(0);
                                    v_isShared_3553_ = v_isSharedCheck_3614_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3620_ = lean_ctor_get(v_impl_3535_, 3);
                            lean_inc(v_l_3620_);
                            if lean_obj_tag(v_l_3620_) == 0 {
                                v_r_3621_ = lean_ctor_get(v_impl_3535_, 4);
                                v_k_3622_ = lean_ctor_get(v_impl_3535_, 1);
                                v_v_3623_ = lean_ctor_get(v_impl_3535_, 2);
                                v_isSharedCheck_3646_ = (!lean_is_exclusive(v_impl_3535_)) as u8;
                                if v_isSharedCheck_3646_ == 0 {
                                    v_unused_3647_ = lean_ctor_get(v_impl_3535_, 3);
                                    lean_dec(v_unused_3647_);
                                    v_unused_3648_ = lean_ctor_get(v_impl_3535_, 0);
                                    lean_dec(v_unused_3648_);
                                    v___x_3625_ = v_impl_3535_;
                                    v_isShared_3626_ = v_isSharedCheck_3646_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_3621_);
                                    lean_inc(v_v_3623_);
                                    lean_inc(v_k_3622_);
                                    lean_dec(v_impl_3535_);
                                    v___x_3625_ = lean_box(0);
                                    v_isShared_3626_ = v_isSharedCheck_3646_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3649_ = lean_ctor_get(v_impl_3535_, 4);
                                lean_inc(v_r_3649_);
                                if lean_obj_tag(v_r_3649_) == 0 {
                                    v_k_3650_ = lean_ctor_get(v_impl_3535_, 1);
                                    v_v_3651_ = lean_ctor_get(v_impl_3535_, 2);
                                    v_isSharedCheck_3662_ =
                                        (!lean_is_exclusive(v_impl_3535_)) as u8;
                                    if v_isSharedCheck_3662_ == 0 {
                                        v_unused_3663_ = lean_ctor_get(v_impl_3535_, 4);
                                        lean_dec(v_unused_3663_);
                                        v_unused_3664_ = lean_ctor_get(v_impl_3535_, 3);
                                        lean_dec(v_unused_3664_);
                                        v_unused_3665_ = lean_ctor_get(v_impl_3535_, 0);
                                        lean_dec(v_unused_3665_);
                                        v___x_3653_ = v_impl_3535_;
                                        v_isShared_3654_ = v_isSharedCheck_3662_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3651_);
                                        lean_inc(v_k_3650_);
                                        lean_dec(v_impl_3535_);
                                        v___x_3653_ = lean_box(0);
                                        v_isShared_3654_ = v_isSharedCheck_3662_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3666_ = lean_unsigned_to_nat(2);
                                    if v_isShared_3392_ == 0 {
                                        lean_ctor_set(v___x_3391_, 4, v_impl_3535_);
                                        lean_ctor_set(v___x_3391_, 3, v_r_3649_);
                                        lean_ctor_set(v___x_3391_, 0, v___x_3666_);
                                        v___x_3668_ = v___x_3391_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
                                        lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_k_3386_);
                                        lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_v_3387_);
                                        lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_r_3649_);
                                        lean_ctor_set(v_reuseFailAlloc_3669_, 4, v_impl_3535_);
                                        v___x_3668_ = v_reuseFailAlloc_3669_;
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
                return v___x_3409_;
            }
            3 => {
                v_size_3414_ = lean_ctor_get(v_l_3401_, 0);
                v_size_3415_ = lean_ctor_get(v_r_3402_, 0);
                v_k_3416_ = lean_ctor_get(v_r_3402_, 1);
                v_v_3417_ = lean_ctor_get(v_r_3402_, 2);
                v_l_3418_ = lean_ctor_get(v_r_3402_, 3);
                v_r_3419_ = lean_ctor_get(v_r_3402_, 4);
                v___x_3420_ = lean_unsigned_to_nat(2);
                v___x_3421_ = lean_nat_mul(v___x_3420_, v_size_3414_);
                v___x_3422_ = lean_nat_dec_lt(v_size_3415_, v___x_3421_);
                lean_dec(v___x_3421_);
                if v___x_3422_ == 0 {
                    lean_inc(v_r_3419_);
                    lean_inc(v_l_3418_);
                    lean_inc(v_v_3417_);
                    lean_inc(v_k_3416_);
                    v_isSharedCheck_3451_ = (!lean_is_exclusive(v_r_3402_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v_unused_3452_ = lean_ctor_get(v_r_3402_, 4);
                        lean_dec(v_unused_3452_);
                        v_unused_3453_ = lean_ctor_get(v_r_3402_, 3);
                        lean_dec(v_unused_3453_);
                        v_unused_3454_ = lean_ctor_get(v_r_3402_, 2);
                        lean_dec(v_unused_3454_);
                        v_unused_3455_ = lean_ctor_get(v_r_3402_, 1);
                        lean_dec(v_unused_3455_);
                        v_unused_3456_ = lean_ctor_get(v_r_3402_, 0);
                        lean_dec(v_unused_3456_);
                        v___x_3424_ = v_r_3402_;
                        v_isShared_3425_ = v_isSharedCheck_3451_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_3402_);
                        v___x_3424_ = lean_box(0);
                        v_isShared_3425_ = v_isSharedCheck_3451_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3391_);
                    v___x_3457_ = lean_nat_add(v___x_3396_, v_size_3398_);
                    lean_dec(v_size_3398_);
                    v___x_3458_ = lean_nat_add(v___x_3457_, v_size_3397_);
                    lean_dec(v___x_3457_);
                    v___x_3459_ = lean_nat_add(v___x_3396_, v_size_3397_);
                    v___x_3460_ = lean_nat_add(v___x_3459_, v_size_3415_);
                    lean_dec(v___x_3459_);
                    lean_inc_ref(v_r_3389_);
                    if v_isShared_3413_ == 0 {
                        lean_ctor_set(v___x_3412_, 4, v_r_3389_);
                        lean_ctor_set(v___x_3412_, 3, v_r_3402_);
                        lean_ctor_set(v___x_3412_, 2, v_v_3387_);
                        lean_ctor_set(v___x_3412_, 1, v_k_3386_);
                        lean_ctor_set(v___x_3412_, 0, v___x_3460_);
                        v___x_3462_ = v___x_3412_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3460_);
                        lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_k_3386_);
                        lean_ctor_set(v_reuseFailAlloc_3475_, 2, v_v_3387_);
                        lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_r_3402_);
                        lean_ctor_set(v_reuseFailAlloc_3475_, 4, v_r_3389_);
                        v___x_3462_ = v_reuseFailAlloc_3475_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3426_ = lean_nat_add(v___x_3396_, v_size_3398_);
                lean_dec(v_size_3398_);
                v___x_3427_ = lean_nat_add(v___x_3426_, v_size_3397_);
                lean_dec(v___x_3426_);
                v___x_3439_ = lean_nat_add(v___x_3396_, v_size_3414_);
                if lean_obj_tag(v_l_3418_) == 0 {
                    v_size_3449_ = lean_ctor_get(v_l_3418_, 0);
                    lean_inc(v_size_3449_);
                    v___y_3441_ = v_size_3449_;
                    state = 8;
                    continue;
                } else {
                    v___x_3450_ = lean_unsigned_to_nat(0);
                    v___y_3441_ = v___x_3450_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3432_ = lean_nat_add(v___y_3429_, v___y_3431_);
                lean_dec(v___y_3431_);
                lean_dec(v___y_3429_);
                if v_isShared_3425_ == 0 {
                    lean_ctor_set(v___x_3424_, 4, v_r_3389_);
                    lean_ctor_set(v___x_3424_, 3, v_r_3419_);
                    lean_ctor_set(v___x_3424_, 2, v_v_3387_);
                    lean_ctor_set(v___x_3424_, 1, v_k_3386_);
                    lean_ctor_set(v___x_3424_, 0, v___x_3432_);
                    v___x_3434_ = v___x_3424_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3432_);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_k_3386_);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 2, v_v_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 3, v_r_3419_);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 4, v_r_3389_);
                    v___x_3434_ = v_reuseFailAlloc_3438_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3413_ == 0 {
                    lean_ctor_set(v___x_3412_, 4, v___x_3434_);
                    lean_ctor_set(v___x_3412_, 3, v___y_3430_);
                    lean_ctor_set(v___x_3412_, 2, v_v_3417_);
                    lean_ctor_set(v___x_3412_, 1, v_k_3416_);
                    lean_ctor_set(v___x_3412_, 0, v___x_3427_);
                    v___x_3436_ = v___x_3412_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3427_);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_k_3416_);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_v_3417_);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 3, v___y_3430_);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 4, v___x_3434_);
                    v___x_3436_ = v_reuseFailAlloc_3437_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3436_;
            }
            8 => {
                v___x_3442_ = lean_nat_add(v___x_3439_, v___y_3441_);
                lean_dec(v___y_3441_);
                lean_dec(v___x_3439_);
                if v_isShared_3392_ == 0 {
                    lean_ctor_set(v___x_3391_, 4, v_l_3418_);
                    lean_ctor_set(v___x_3391_, 3, v_l_3401_);
                    lean_ctor_set(v___x_3391_, 2, v_v_3400_);
                    lean_ctor_set(v___x_3391_, 1, v_k_3399_);
                    lean_ctor_set(v___x_3391_, 0, v___x_3442_);
                    v___x_3444_ = v___x_3391_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
                    lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3399_);
                    lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3400_);
                    lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_l_3401_);
                    lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_l_3418_);
                    v___x_3444_ = v_reuseFailAlloc_3448_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3445_ = lean_nat_add(v___x_3396_, v_size_3397_);
                if lean_obj_tag(v_r_3419_) == 0 {
                    v_size_3446_ = lean_ctor_get(v_r_3419_, 0);
                    lean_inc(v_size_3446_);
                    v___y_3429_ = v___x_3445_;
                    v___y_3430_ = v___x_3444_;
                    v___y_3431_ = v_size_3446_;
                    state = 5;
                    continue;
                } else {
                    v___x_3447_ = lean_unsigned_to_nat(0);
                    v___y_3429_ = v___x_3445_;
                    v___y_3430_ = v___x_3444_;
                    v___y_3431_ = v___x_3447_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3469_ = (!lean_is_exclusive(v_r_3389_)) as u8;
                if v_isSharedCheck_3469_ == 0 {
                    v_unused_3470_ = lean_ctor_get(v_r_3389_, 4);
                    lean_dec(v_unused_3470_);
                    v_unused_3471_ = lean_ctor_get(v_r_3389_, 3);
                    lean_dec(v_unused_3471_);
                    v_unused_3472_ = lean_ctor_get(v_r_3389_, 2);
                    lean_dec(v_unused_3472_);
                    v_unused_3473_ = lean_ctor_get(v_r_3389_, 1);
                    lean_dec(v_unused_3473_);
                    v_unused_3474_ = lean_ctor_get(v_r_3389_, 0);
                    lean_dec(v_unused_3474_);
                    v___x_3464_ = v_r_3389_;
                    v_isShared_3465_ = v_isSharedCheck_3469_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_3389_);
                    v___x_3464_ = lean_box(0);
                    v_isShared_3465_ = v_isSharedCheck_3469_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 4, v___x_3462_);
                    lean_ctor_set(v___x_3464_, 3, v_l_3401_);
                    lean_ctor_set(v___x_3464_, 2, v_v_3400_);
                    lean_ctor_set(v___x_3464_, 1, v_k_3399_);
                    lean_ctor_set(v___x_3464_, 0, v___x_3458_);
                    v___x_3467_ = v___x_3464_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3458_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_k_3399_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_v_3400_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_l_3401_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 4, v___x_3462_);
                    v___x_3467_ = v_reuseFailAlloc_3468_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3467_;
            }
            13 => {
                v___x_3489_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_3483_);
                if v_isShared_3488_ == 0 {
                    lean_ctor_set(v___x_3487_, 3, v_r_3483_);
                    lean_ctor_set(v___x_3487_, 2, v_v_3387_);
                    lean_ctor_set(v___x_3487_, 1, v_k_3386_);
                    lean_ctor_set(v___x_3487_, 0, v___x_3396_);
                    v___x_3491_ = v___x_3487_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3396_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3386_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_r_3483_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_r_3483_);
                    v___x_3491_ = v_reuseFailAlloc_3495_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_3392_ == 0 {
                    lean_ctor_set(v___x_3391_, 4, v___x_3491_);
                    lean_ctor_set(v___x_3391_, 3, v_l_3482_);
                    lean_ctor_set(v___x_3391_, 2, v_v_3485_);
                    lean_ctor_set(v___x_3391_, 1, v_k_3484_);
                    lean_ctor_set(v___x_3391_, 0, v___x_3489_);
                    v___x_3493_ = v___x_3391_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3489_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3484_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3485_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_l_3482_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 4, v___x_3491_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3493_;
            }
            16 => {
                v_k_3505_ = lean_ctor_get(v_r_3499_, 1);
                v_v_3506_ = lean_ctor_get(v_r_3499_, 2);
                v_isSharedCheck_3520_ = (!lean_is_exclusive(v_r_3499_)) as u8;
                if v_isSharedCheck_3520_ == 0 {
                    v_unused_3521_ = lean_ctor_get(v_r_3499_, 4);
                    lean_dec(v_unused_3521_);
                    v_unused_3522_ = lean_ctor_get(v_r_3499_, 3);
                    lean_dec(v_unused_3522_);
                    v_unused_3523_ = lean_ctor_get(v_r_3499_, 0);
                    lean_dec(v_unused_3523_);
                    v___x_3508_ = v_r_3499_;
                    v_isShared_3509_ = v_isSharedCheck_3520_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_3506_);
                    lean_inc(v_k_3505_);
                    lean_dec(v_r_3499_);
                    v___x_3508_ = lean_box(0);
                    v_isShared_3509_ = v_isSharedCheck_3520_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3510_ = lean_unsigned_to_nat(3);
                if v_isShared_3509_ == 0 {
                    lean_ctor_set(v___x_3508_, 4, v_l_3482_);
                    lean_ctor_set(v___x_3508_, 3, v_l_3482_);
                    lean_ctor_set(v___x_3508_, 2, v_v_3501_);
                    lean_ctor_set(v___x_3508_, 1, v_k_3500_);
                    lean_ctor_set(v___x_3508_, 0, v___x_3396_);
                    v___x_3512_ = v___x_3508_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3396_);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_k_3500_);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 2, v_v_3501_);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 3, v_l_3482_);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 4, v_l_3482_);
                    v___x_3512_ = v_reuseFailAlloc_3519_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3504_ == 0 {
                    lean_ctor_set(v___x_3503_, 4, v_l_3482_);
                    lean_ctor_set(v___x_3503_, 2, v_v_3387_);
                    lean_ctor_set(v___x_3503_, 1, v_k_3386_);
                    lean_ctor_set(v___x_3503_, 0, v___x_3396_);
                    v___x_3514_ = v___x_3503_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3396_);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_k_3386_);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 2, v_v_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 3, v_l_3482_);
                    lean_ctor_set(v_reuseFailAlloc_3518_, 4, v_l_3482_);
                    v___x_3514_ = v_reuseFailAlloc_3518_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3392_ == 0 {
                    lean_ctor_set(v___x_3391_, 4, v___x_3514_);
                    lean_ctor_set(v___x_3391_, 3, v___x_3512_);
                    lean_ctor_set(v___x_3391_, 2, v_v_3506_);
                    lean_ctor_set(v___x_3391_, 1, v_k_3505_);
                    lean_ctor_set(v___x_3391_, 0, v___x_3510_);
                    v___x_3516_ = v___x_3391_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3510_);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_k_3505_);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_v_3506_);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 3, v___x_3512_);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 4, v___x_3514_);
                    v___x_3516_ = v_reuseFailAlloc_3517_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3516_;
            }
            21 => {
                return v___x_3530_;
            }
            22 => {
                return v___x_3533_;
            }
            23 => {
                return v___x_3549_;
            }
            24 => {
                v_size_3554_ = lean_ctor_get(v_l_3541_, 0);
                v_k_3555_ = lean_ctor_get(v_l_3541_, 1);
                v_v_3556_ = lean_ctor_get(v_l_3541_, 2);
                v_l_3557_ = lean_ctor_get(v_l_3541_, 3);
                v_r_3558_ = lean_ctor_get(v_l_3541_, 4);
                v_size_3559_ = lean_ctor_get(v_r_3542_, 0);
                v___x_3560_ = lean_unsigned_to_nat(2);
                v___x_3561_ = lean_nat_mul(v___x_3560_, v_size_3559_);
                v___x_3562_ = lean_nat_dec_lt(v_size_3554_, v___x_3561_);
                lean_dec(v___x_3561_);
                if v___x_3562_ == 0 {
                    lean_inc(v_r_3558_);
                    lean_inc(v_l_3557_);
                    lean_inc(v_v_3556_);
                    lean_inc(v_k_3555_);
                    v_isSharedCheck_3590_ = (!lean_is_exclusive(v_l_3541_)) as u8;
                    if v_isSharedCheck_3590_ == 0 {
                        v_unused_3591_ = lean_ctor_get(v_l_3541_, 4);
                        lean_dec(v_unused_3591_);
                        v_unused_3592_ = lean_ctor_get(v_l_3541_, 3);
                        lean_dec(v_unused_3592_);
                        v_unused_3593_ = lean_ctor_get(v_l_3541_, 2);
                        lean_dec(v_unused_3593_);
                        v_unused_3594_ = lean_ctor_get(v_l_3541_, 1);
                        lean_dec(v_unused_3594_);
                        v_unused_3595_ = lean_ctor_get(v_l_3541_, 0);
                        lean_dec(v_unused_3595_);
                        v___x_3564_ = v_l_3541_;
                        v_isShared_3565_ = v_isSharedCheck_3590_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_3541_);
                        v___x_3564_ = lean_box(0);
                        v_isShared_3565_ = v_isSharedCheck_3590_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3391_);
                    v___x_3596_ = lean_nat_add(v___x_3536_, v_size_3537_);
                    v___x_3597_ = lean_nat_add(v___x_3596_, v_size_3538_);
                    lean_dec(v_size_3538_);
                    v___x_3598_ = lean_nat_add(v___x_3596_, v_size_3554_);
                    lean_dec(v___x_3596_);
                    lean_inc_ref(v_l_3388_);
                    if v_isShared_3553_ == 0 {
                        lean_ctor_set(v___x_3552_, 4, v_l_3541_);
                        lean_ctor_set(v___x_3552_, 3, v_l_3388_);
                        lean_ctor_set(v___x_3552_, 2, v_v_3387_);
                        lean_ctor_set(v___x_3552_, 1, v_k_3386_);
                        lean_ctor_set(v___x_3552_, 0, v___x_3598_);
                        v___x_3600_ = v___x_3552_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3598_);
                        lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_k_3386_);
                        lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_v_3387_);
                        lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_l_3388_);
                        lean_ctor_set(v_reuseFailAlloc_3613_, 4, v_l_3541_);
                        v___x_3600_ = v_reuseFailAlloc_3613_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3566_ = lean_nat_add(v___x_3536_, v_size_3537_);
                v___x_3567_ = lean_nat_add(v___x_3566_, v_size_3538_);
                lean_dec(v_size_3538_);
                if lean_obj_tag(v_l_3557_) == 0 {
                    v_size_3588_ = lean_ctor_get(v_l_3557_, 0);
                    lean_inc(v_size_3588_);
                    v___y_3580_ = v_size_3588_;
                    state = 29;
                    continue;
                } else {
                    v___x_3589_ = lean_unsigned_to_nat(0);
                    v___y_3580_ = v___x_3589_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3572_ = lean_nat_add(v___y_3569_, v___y_3571_);
                lean_dec(v___y_3571_);
                lean_dec(v___y_3569_);
                if v_isShared_3565_ == 0 {
                    lean_ctor_set(v___x_3564_, 4, v_r_3542_);
                    lean_ctor_set(v___x_3564_, 3, v_r_3558_);
                    lean_ctor_set(v___x_3564_, 2, v_v_3540_);
                    lean_ctor_set(v___x_3564_, 1, v_k_3539_);
                    lean_ctor_set(v___x_3564_, 0, v___x_3572_);
                    v___x_3574_ = v___x_3564_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3572_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_k_3539_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_v_3540_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_r_3558_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 4, v_r_3542_);
                    v___x_3574_ = v_reuseFailAlloc_3578_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3553_ == 0 {
                    lean_ctor_set(v___x_3552_, 4, v___x_3574_);
                    lean_ctor_set(v___x_3552_, 3, v___y_3570_);
                    lean_ctor_set(v___x_3552_, 2, v_v_3556_);
                    lean_ctor_set(v___x_3552_, 1, v_k_3555_);
                    lean_ctor_set(v___x_3552_, 0, v___x_3567_);
                    v___x_3576_ = v___x_3552_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3567_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_k_3555_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_v_3556_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 3, v___y_3570_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 4, v___x_3574_);
                    v___x_3576_ = v_reuseFailAlloc_3577_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3576_;
            }
            29 => {
                v___x_3581_ = lean_nat_add(v___x_3566_, v___y_3580_);
                lean_dec(v___y_3580_);
                lean_dec(v___x_3566_);
                if v_isShared_3392_ == 0 {
                    lean_ctor_set(v___x_3391_, 4, v_l_3557_);
                    lean_ctor_set(v___x_3391_, 0, v___x_3581_);
                    v___x_3583_ = v___x_3391_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3581_);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3386_);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_l_3388_);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_l_3557_);
                    v___x_3583_ = v_reuseFailAlloc_3587_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3584_ = lean_nat_add(v___x_3536_, v_size_3559_);
                if lean_obj_tag(v_r_3558_) == 0 {
                    v_size_3585_ = lean_ctor_get(v_r_3558_, 0);
                    lean_inc(v_size_3585_);
                    v___y_3569_ = v___x_3584_;
                    v___y_3570_ = v___x_3583_;
                    v___y_3571_ = v_size_3585_;
                    state = 26;
                    continue;
                } else {
                    v___x_3586_ = lean_unsigned_to_nat(0);
                    v___y_3569_ = v___x_3584_;
                    v___y_3570_ = v___x_3583_;
                    v___y_3571_ = v___x_3586_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3607_ = (!lean_is_exclusive(v_l_3388_)) as u8;
                if v_isSharedCheck_3607_ == 0 {
                    v_unused_3608_ = lean_ctor_get(v_l_3388_, 4);
                    lean_dec(v_unused_3608_);
                    v_unused_3609_ = lean_ctor_get(v_l_3388_, 3);
                    lean_dec(v_unused_3609_);
                    v_unused_3610_ = lean_ctor_get(v_l_3388_, 2);
                    lean_dec(v_unused_3610_);
                    v_unused_3611_ = lean_ctor_get(v_l_3388_, 1);
                    lean_dec(v_unused_3611_);
                    v_unused_3612_ = lean_ctor_get(v_l_3388_, 0);
                    lean_dec(v_unused_3612_);
                    v___x_3602_ = v_l_3388_;
                    v_isShared_3603_ = v_isSharedCheck_3607_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_3388_);
                    v___x_3602_ = lean_box(0);
                    v_isShared_3603_ = v_isSharedCheck_3607_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3603_ == 0 {
                    lean_ctor_set(v___x_3602_, 4, v_r_3542_);
                    lean_ctor_set(v___x_3602_, 3, v___x_3600_);
                    lean_ctor_set(v___x_3602_, 2, v_v_3540_);
                    lean_ctor_set(v___x_3602_, 1, v_k_3539_);
                    lean_ctor_set(v___x_3602_, 0, v___x_3597_);
                    v___x_3605_ = v___x_3602_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3597_);
                    lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_k_3539_);
                    lean_ctor_set(v_reuseFailAlloc_3606_, 2, v_v_3540_);
                    lean_ctor_set(v_reuseFailAlloc_3606_, 3, v___x_3600_);
                    lean_ctor_set(v_reuseFailAlloc_3606_, 4, v_r_3542_);
                    v___x_3605_ = v_reuseFailAlloc_3606_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3605_;
            }
            34 => {
                v_k_3627_ = lean_ctor_get(v_l_3620_, 1);
                v_v_3628_ = lean_ctor_get(v_l_3620_, 2);
                v_isSharedCheck_3642_ = (!lean_is_exclusive(v_l_3620_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v_unused_3643_ = lean_ctor_get(v_l_3620_, 4);
                    lean_dec(v_unused_3643_);
                    v_unused_3644_ = lean_ctor_get(v_l_3620_, 3);
                    lean_dec(v_unused_3644_);
                    v_unused_3645_ = lean_ctor_get(v_l_3620_, 0);
                    lean_dec(v_unused_3645_);
                    v___x_3630_ = v_l_3620_;
                    v_isShared_3631_ = v_isSharedCheck_3642_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_3628_);
                    lean_inc(v_k_3627_);
                    lean_dec(v_l_3620_);
                    v___x_3630_ = lean_box(0);
                    v_isShared_3631_ = v_isSharedCheck_3642_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3632_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_3621_, 2);
                if v_isShared_3631_ == 0 {
                    lean_ctor_set(v___x_3630_, 4, v_r_3621_);
                    lean_ctor_set(v___x_3630_, 3, v_r_3621_);
                    lean_ctor_set(v___x_3630_, 2, v_v_3387_);
                    lean_ctor_set(v___x_3630_, 1, v_k_3386_);
                    lean_ctor_set(v___x_3630_, 0, v___x_3536_);
                    v___x_3634_ = v___x_3630_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3536_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_k_3386_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_v_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_r_3621_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_r_3621_);
                    v___x_3634_ = v_reuseFailAlloc_3641_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_3621_);
                if v_isShared_3626_ == 0 {
                    lean_ctor_set(v___x_3625_, 3, v_r_3621_);
                    lean_ctor_set(v___x_3625_, 0, v___x_3536_);
                    v___x_3636_ = v___x_3625_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3536_);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_k_3622_);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 2, v_v_3623_);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 3, v_r_3621_);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 4, v_r_3621_);
                    v___x_3636_ = v_reuseFailAlloc_3640_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3392_ == 0 {
                    lean_ctor_set(v___x_3391_, 4, v___x_3636_);
                    lean_ctor_set(v___x_3391_, 3, v___x_3634_);
                    lean_ctor_set(v___x_3391_, 2, v_v_3628_);
                    lean_ctor_set(v___x_3391_, 1, v_k_3627_);
                    lean_ctor_set(v___x_3391_, 0, v___x_3632_);
                    v___x_3638_ = v___x_3391_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3632_);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_k_3627_);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_v_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 3, v___x_3634_);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 4, v___x_3636_);
                    v___x_3638_ = v_reuseFailAlloc_3639_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3638_;
            }
            39 => {
                v___x_3655_ = lean_unsigned_to_nat(3);
                if v_isShared_3654_ == 0 {
                    lean_ctor_set(v___x_3653_, 4, v_l_3620_);
                    lean_ctor_set(v___x_3653_, 2, v_v_3387_);
                    lean_ctor_set(v___x_3653_, 1, v_k_3386_);
                    lean_ctor_set(v___x_3653_, 0, v___x_3536_);
                    v___x_3657_ = v___x_3653_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3536_);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_k_3386_);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_v_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 3, v_l_3620_);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 4, v_l_3620_);
                    v___x_3657_ = v_reuseFailAlloc_3661_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3392_ == 0 {
                    lean_ctor_set(v___x_3391_, 4, v_r_3649_);
                    lean_ctor_set(v___x_3391_, 3, v___x_3657_);
                    lean_ctor_set(v___x_3391_, 2, v_v_3651_);
                    lean_ctor_set(v___x_3391_, 1, v_k_3650_);
                    lean_ctor_set(v___x_3391_, 0, v___x_3655_);
                    v___x_3659_ = v___x_3391_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3655_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3651_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 3, v___x_3657_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_r_3649_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3659_;
            }
            42 => {
                return v___x_3668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(
    mut v_cmp_3673_: *mut LeanObject,
    mut v_k_3674_: *mut LeanObject,
    mut v_t_3675_: *mut LeanObject,
) -> u8 {
    let mut v_k_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: u8 = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3675_) == 0 {
                    v_k_3676_ = lean_ctor_get(v_t_3675_, 1);
                    lean_inc(v_k_3676_);
                    v_l_3677_ = lean_ctor_get(v_t_3675_, 3);
                    lean_inc(v_l_3677_);
                    v_r_3678_ = lean_ctor_get(v_t_3675_, 4);
                    lean_inc(v_r_3678_);
                    lean_dec_ref_known(v_t_3675_, 5);
                    lean_inc_ref(v_cmp_3673_);
                    lean_inc(v_k_3674_);
                    v___x_3679_ = lean_apply_2(v_cmp_3673_, v_k_3674_, v_k_3676_);
                    v___x_3680_ = (lean_unbox(v___x_3679_) as u8);
                    match v___x_3680_ {
                        0 => {
                            lean_dec(v_r_3678_);
                            v_t_3675_ = v_l_3677_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_dec(v_r_3678_);
                            lean_dec(v_l_3677_);
                            lean_dec(v_k_3674_);
                            lean_dec_ref(v_cmp_3673_);
                            v___x_3682_ = 1;
                            return v___x_3682_;
                        }
                        _ => {
                            lean_dec(v_l_3677_);
                            v_t_3675_ = v_r_3678_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_3674_);
                    lean_dec_ref(v_cmp_3673_);
                    v___x_3684_ = 0;
                    return v___x_3684_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(
    mut v_cmp_3685_: *mut LeanObject,
    mut v_k_3686_: *mut LeanObject,
    mut v_t_3687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3688_: u8 = 0;
    let mut v_r_3689_: *mut LeanObject = core::ptr::null_mut();
    v_res_3688_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(
            v_cmp_3685_,
            v_k_3686_,
            v_t_3687_,
        );
    v_r_3689_ = lean_box((v_res_3688_) as usize);
    return v_r_3689_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
    mut v_cmp_3690_: *mut LeanObject,
    mut v_as_x27_3691_: *mut LeanObject,
    mut v_b_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3691_) == 0 {
                    lean_dec_ref(v_cmp_3690_);
                    return v_b_3692_;
                } else {
                    v_head_3693_ = lean_ctor_get(v_as_x27_3691_, 0);
                    v_tail_3694_ = lean_ctor_get(v_as_x27_3691_, 1);
                    lean_inc(v_b_3692_);
                    lean_inc(v_head_3693_);
                    lean_inc_ref(v_cmp_3690_);
                    v___x_3695_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_3690_, v_head_3693_, v_b_3692_);
                    if v___x_3695_ == 0 {
                        v___x_3696_ = lean_box(0);
                        lean_inc(v_head_3693_);
                        lean_inc_ref(v_cmp_3690_);
                        v___x_3697_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_3690_, v_head_3693_, v___x_3696_, v_b_3692_);
                        v_as_x27_3691_ = v_tail_3694_;
                        v_b_3692_ = v___x_3697_;
                        state = 0;
                        continue;
                    } else {
                        v_as_x27_3691_ = v_tail_3694_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg___boxed(
    mut v_cmp_3700_: *mut LeanObject,
    mut v_as_x27_3701_: *mut LeanObject,
    mut v_b_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3703_: *mut LeanObject = core::ptr::null_mut();
    v_res_3703_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
        v_cmp_3700_,
        v_as_x27_3701_,
        v_b_3702_,
    );
    lean_dec(v_as_x27_3701_);
    return v_res_3703_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList___redArg(
    mut v_l_3704_: *mut LeanObject,
    mut v_cmp_3705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    v_r_3706_ = lean_box(1);
    v___x_3707_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
        v_cmp_3705_,
        v_l_3704_,
        v_r_3706_,
    );
    return v___x_3707_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList___redArg___boxed(
    mut v_l_3708_: *mut LeanObject,
    mut v_cmp_3709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3710_: *mut LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Std_ExtTreeSet_ofList___redArg(v_l_3708_, v_cmp_3709_);
    lean_dec(v_l_3708_);
    return v_res_3710_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList(
    mut v_00_u03b1_3711_: *mut LeanObject,
    mut v_l_3712_: *mut LeanObject,
    mut v_cmp_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    v___x_3714_ = l_Std_ExtTreeSet_ofList___redArg(v_l_3712_, v_cmp_3713_);
    return v___x_3714_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList___boxed(
    mut v_00_u03b1_3715_: *mut LeanObject,
    mut v_l_3716_: *mut LeanObject,
    mut v_cmp_3717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3718_: *mut LeanObject = core::ptr::null_mut();
    v_res_3718_ = l_Std_ExtTreeSet_ofList(v_00_u03b1_3715_, v_l_3716_, v_cmp_3717_);
    lean_dec(v_l_3716_);
    return v_res_3718_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(
    mut v_00_u03b1_3719_: *mut LeanObject,
    mut v_cmp_3720_: *mut LeanObject,
    mut v_00_u03b2_3721_: *mut LeanObject,
    mut v_k_3722_: *mut LeanObject,
    mut v_t_3723_: *mut LeanObject,
) -> u8 {
    let mut v___x_3724_: u8 = 0;
    v___x_3724_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(
            v_cmp_3720_,
            v_k_3722_,
            v_t_3723_,
        );
    return v___x_3724_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___boxed(
    mut v_00_u03b1_3725_: *mut LeanObject,
    mut v_cmp_3726_: *mut LeanObject,
    mut v_00_u03b2_3727_: *mut LeanObject,
    mut v_k_3728_: *mut LeanObject,
    mut v_t_3729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3730_: u8 = 0;
    let mut v_r_3731_: *mut LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(
        v_00_u03b1_3725_,
        v_cmp_3726_,
        v_00_u03b2_3727_,
        v_k_3728_,
        v_t_3729_,
    );
    v_r_3731_ = lean_box((v_res_3730_) as usize);
    return v_r_3731_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(
    mut v_00_u03b1_3732_: *mut LeanObject,
    mut v_cmp_3733_: *mut LeanObject,
    mut v_00_u03b2_3734_: *mut LeanObject,
    mut v_k_3735_: *mut LeanObject,
    mut v_v_3736_: *mut LeanObject,
    mut v_t_3737_: *mut LeanObject,
    mut v_hl_3738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    v___x_3739_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(
            v_cmp_3733_,
            v_k_3735_,
            v_v_3736_,
            v_t_3737_,
        );
    return v___x_3739_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(
    mut v_00_u03b1_3740_: *mut LeanObject,
    mut v_cmp_3741_: *mut LeanObject,
    mut v_as_3742_: *mut LeanObject,
    mut v_as_x27_3743_: *mut LeanObject,
    mut v_b_3744_: *mut LeanObject,
    mut v_a_3745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
        v_cmp_3741_,
        v_as_x27_3743_,
        v_b_3744_,
    );
    return v___x_3746_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(
    mut v_00_u03b1_3747_: *mut LeanObject,
    mut v_cmp_3748_: *mut LeanObject,
    mut v_as_3749_: *mut LeanObject,
    mut v_as_x27_3750_: *mut LeanObject,
    mut v_b_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3753_: *mut LeanObject = core::ptr::null_mut();
    v_res_3753_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(
        v_00_u03b1_3747_,
        v_cmp_3748_,
        v_as_3749_,
        v_as_x27_3750_,
        v_b_3751_,
        v_a_3752_,
    );
    lean_dec(v_as_x27_3750_);
    lean_dec(v_as_3749_);
    return v_res_3753_;
}
pub unsafe fn l_Std_ExtTreeSet_toArray___redArg___lam__0(
    mut v_l_3754_: *mut LeanObject,
    mut v_k_3755_: *mut LeanObject,
    mut v_x_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    v___x_3757_ = lean_array_push(v_l_3754_, v_k_3755_);
    return v___x_3757_;
}
pub unsafe fn l_Std_ExtTreeSet_toArray___redArg(mut v_t_3759_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3760_ = l_Std_ExtTreeSet_toArray___redArg___closed__0;
                if lean_obj_tag(v_t_3759_) == 0 {
                    v_size_3765_ = lean_ctor_get(v_t_3759_, 0);
                    lean_inc(v_size_3765_);
                    v___y_3762_ = v_size_3765_;
                    state = 1;
                    continue;
                } else {
                    v___x_3766_ = lean_unsigned_to_nat(0);
                    v___y_3762_ = v___x_3766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3763_ = lean_mk_empty_array_with_capacity(v___y_3762_);
                lean_dec(v___y_3762_);
                v___x_3764_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3760_,
                    v___x_3763_,
                    v_t_3759_,
                );
                return v___x_3764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_toArray(
    mut v_00_u03b1_3767_: *mut LeanObject,
    mut v_cmp_3768_: *mut LeanObject,
    mut v_inst_3769_: *mut LeanObject,
    mut v_t_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3771_ = l_Std_ExtTreeSet_toArray___redArg___closed__0;
                if lean_obj_tag(v_t_3770_) == 0 {
                    v_size_3776_ = lean_ctor_get(v_t_3770_, 0);
                    lean_inc(v_size_3776_);
                    v___y_3773_ = v_size_3776_;
                    state = 1;
                    continue;
                } else {
                    v___x_3777_ = lean_unsigned_to_nat(0);
                    v___y_3773_ = v___x_3777_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3774_ = lean_mk_empty_array_with_capacity(v___y_3773_);
                lean_dec(v___y_3773_);
                v___x_3775_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3771_,
                    v___x_3774_,
                    v_t_3770_,
                );
                return v___x_3775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_toArray___boxed(
    mut v_00_u03b1_3778_: *mut LeanObject,
    mut v_cmp_3779_: *mut LeanObject,
    mut v_inst_3780_: *mut LeanObject,
    mut v_t_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3782_: *mut LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_Std_ExtTreeSet_toArray(v_00_u03b1_3778_, v_cmp_3779_, v_inst_3780_, v_t_3781_);
    lean_dec_ref(v_cmp_3779_);
    return v_res_3782_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_ofArray___auto__1() -> *mut LeanObject {
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3783_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__26,
    );
    return v___x_3783_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(
    mut v_cmp_3784_: *mut LeanObject,
    mut v_as_3785_: *mut LeanObject,
    mut v_sz_3786_: usize,
    mut v_i_3787_: usize,
    mut v_b_3788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: usize = 0;
    let mut v___x_3792_: usize = 0;
    let mut v___x_3794_: u8 = 0;
    let mut v_a_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3794_ = lean_usize_dec_lt(v_i_3787_, v_sz_3786_);
                if v___x_3794_ == 0 {
                    lean_dec_ref(v_cmp_3784_);
                    return v_b_3788_;
                } else {
                    v_a_3795_ = lean_array_uget_borrowed(v_as_3785_, v_i_3787_);
                    lean_inc(v_b_3788_);
                    lean_inc(v_a_3795_);
                    lean_inc_ref(v_cmp_3784_);
                    v___x_3796_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_3784_, v_a_3795_, v_b_3788_);
                    if v___x_3796_ == 0 {
                        v___x_3797_ = lean_box(0);
                        lean_inc(v_a_3795_);
                        lean_inc_ref(v_cmp_3784_);
                        v___x_3798_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_3784_, v_a_3795_, v___x_3797_, v_b_3788_);
                        v___y_3790_ = v___x_3798_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3790_ = v_b_3788_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3791_ = 1usize;
                v___x_3792_ = lean_usize_add(v_i_3787_, v___x_3791_);
                v_i_3787_ = v___x_3792_;
                v_b_3788_ = v___y_3790_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg___boxed(
    mut v_cmp_3799_: *mut LeanObject,
    mut v_as_3800_: *mut LeanObject,
    mut v_sz_3801_: *mut LeanObject,
    mut v_i_3802_: *mut LeanObject,
    mut v_b_3803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3804_: usize = 0;
    let mut v_i_boxed_3805_: usize = 0;
    let mut v_res_3806_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3804_ = lean_unbox_usize(v_sz_3801_);
    lean_dec(v_sz_3801_);
    v_i_boxed_3805_ = lean_unbox_usize(v_i_3802_);
    lean_dec(v_i_3802_);
    v_res_3806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_3799_, v_as_3800_, v_sz_boxed_3804_, v_i_boxed_3805_, v_b_3803_);
    lean_dec_ref(v_as_3800_);
    return v_res_3806_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray___redArg(
    mut v_a_3807_: *mut LeanObject,
    mut v_cmp_3808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3810_: usize = 0;
    let mut v___x_3811_: usize = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    v_r_3809_ = lean_box(1);
    v_sz_3810_ = lean_array_size(v_a_3807_);
    v___x_3811_ = 0usize;
    v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_3808_, v_a_3807_, v_sz_3810_, v___x_3811_, v_r_3809_);
    return v___x_3812_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray___redArg___boxed(
    mut v_a_3813_: *mut LeanObject,
    mut v_cmp_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3815_: *mut LeanObject = core::ptr::null_mut();
    v_res_3815_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_3813_, v_cmp_3814_);
    lean_dec_ref(v_a_3813_);
    return v_res_3815_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray(
    mut v_00_u03b1_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_cmp_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v___x_3819_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_3817_, v_cmp_3818_);
    return v___x_3819_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray___boxed(
    mut v_00_u03b1_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_cmp_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3823_: *mut LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Std_ExtTreeSet_ofArray(v_00_u03b1_3820_, v_a_3821_, v_cmp_3822_);
    lean_dec_ref(v_a_3821_);
    return v_res_3823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(
    mut v_00_u03b1_3824_: *mut LeanObject,
    mut v_cmp_3825_: *mut LeanObject,
    mut v_as_3826_: *mut LeanObject,
    mut v_sz_3827_: usize,
    mut v_i_3828_: usize,
    mut v_b_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_3825_, v_as_3826_, v_sz_3827_, v_i_3828_, v_b_3829_);
    return v___x_3830_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(
    mut v_00_u03b1_3831_: *mut LeanObject,
    mut v_cmp_3832_: *mut LeanObject,
    mut v_as_3833_: *mut LeanObject,
    mut v_sz_3834_: *mut LeanObject,
    mut v_i_3835_: *mut LeanObject,
    mut v_b_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3837_: usize = 0;
    let mut v_i_boxed_3838_: usize = 0;
    let mut v_res_3839_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3837_ = lean_unbox_usize(v_sz_3834_);
    lean_dec(v_sz_3834_);
    v_i_boxed_3838_ = lean_unbox_usize(v_i_3835_);
    lean_dec(v_i_3835_);
    v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(v_00_u03b1_3831_, v_cmp_3832_, v_as_3833_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3836_);
    lean_dec_ref(v_as_3833_);
    return v_res_3839_;
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg___lam__0(
    mut v_b_u2082_3842_: *mut LeanObject,
    mut v_x_3843_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3843_) == 0 {
        let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
        v___x_3844_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3844_, 0, v_b_u2082_3842_);
        return v___x_3844_;
    } else {
        let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
        v___x_3845_ = l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0;
        return v___x_3845_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(
    mut v_b_u2082_3846_: *mut LeanObject,
    mut v_x_3847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3848_: *mut LeanObject = core::ptr::null_mut();
    v_res_3848_ = l_Std_ExtTreeSet_merge___redArg___lam__0(v_b_u2082_3846_, v_x_3847_);
    lean_dec(v_x_3847_);
    return v_res_3848_;
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg___lam__1(
    mut v_cmp_3849_: *mut LeanObject,
    mut v_t_3850_: *mut LeanObject,
    mut v_a_3851_: *mut LeanObject,
    mut v_b_u2082_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___f_3853_ = lean_alloc_closure(
        l_Std_ExtTreeSet_merge___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3853_, 0, v_b_u2082_3852_);
    v___x_3854_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_3849_,
        v_a_3851_,
        v___f_3853_,
        v_t_3850_,
    );
    return v___x_3854_;
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg(
    mut v_cmp_3855_: *mut LeanObject,
    mut v_t_u2081_3856_: *mut LeanObject,
    mut v_t_u2082_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___f_3858_ = lean_alloc_closure(
        l_Std_ExtTreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3858_, 0, v_cmp_3855_);
    v___x_3859_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3858_, v_t_u2081_3856_, v_t_u2082_3857_);
    return v___x_3859_;
}
pub unsafe fn l_Std_ExtTreeSet_merge(
    mut v_00_u03b1_3860_: *mut LeanObject,
    mut v_cmp_3861_: *mut LeanObject,
    mut v_inst_3862_: *mut LeanObject,
    mut v_t_u2081_3863_: *mut LeanObject,
    mut v_t_u2082_3864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    v___f_3865_ = lean_alloc_closure(
        l_Std_ExtTreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3865_, 0, v_cmp_3861_);
    v___x_3866_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3865_, v_t_u2081_3863_, v_t_u2082_3864_);
    return v___x_3866_;
}
pub unsafe fn l_Std_ExtTreeSet_insertMany___redArg___lam__0(
    mut v_cmp_3867_: *mut LeanObject,
    mut v_a_3868_: *mut LeanObject,
    mut v_____s_3869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3870_: u8 = 0;
    lean_inc(v_____s_3869_);
    lean_inc(v_a_3868_);
    lean_inc_ref(v_cmp_3867_);
    v___x_3870_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3867_, v_a_3868_, v_____s_3869_);
    if v___x_3870_ == 0 {
        let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
        v___x_3871_ = lean_box(0);
        v___x_3872_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_3867_,
            v_a_3868_,
            v___x_3871_,
            v_____s_3869_,
        );
        v___x_3873_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3873_, 0, v___x_3872_);
        return v___x_3873_;
    } else {
        let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_3868_);
        lean_dec_ref(v_cmp_3867_);
        v___x_3874_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3874_, 0, v_____s_3869_);
        return v___x_3874_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_insertMany___redArg(
    mut v_cmp_3875_: *mut LeanObject,
    mut v_inst_3876_: *mut LeanObject,
    mut v_t_3877_: *mut LeanObject,
    mut v_l_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    v___f_3879_ = lean_alloc_closure(
        l_Std_ExtTreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3879_, 0, v_cmp_3875_);
    v___x_3880_ = lean_apply_4(v_inst_3876_, lean_box(0), v_l_3878_, v_t_3877_, v___f_3879_);
    return v___x_3880_;
}
pub unsafe fn l_Std_ExtTreeSet_insertMany(
    mut v_00_u03b1_3881_: *mut LeanObject,
    mut v_cmp_3882_: *mut LeanObject,
    mut v_inst_3883_: *mut LeanObject,
    mut v_00_u03c1_3884_: *mut LeanObject,
    mut v_inst_3885_: *mut LeanObject,
    mut v_t_3886_: *mut LeanObject,
    mut v_l_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    v___f_3888_ = lean_alloc_closure(
        l_Std_ExtTreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3888_, 0, v_cmp_3882_);
    v___x_3889_ = lean_apply_4(v_inst_3885_, lean_box(0), v_l_3887_, v_t_3886_, v___f_3888_);
    return v___x_3889_;
}
pub unsafe fn l_Std_ExtTreeSet_union___redArg(
    mut v_cmp_3890_: *mut LeanObject,
    mut v_t_u2081_3891_: *mut LeanObject,
    mut v_t_u2082_3892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    v___x_3893_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3890_,
        v_t_u2081_3891_,
        v_t_u2082_3892_,
    );
    return v___x_3893_;
}
pub unsafe fn l_Std_ExtTreeSet_union(
    mut v_00_u03b1_3894_: *mut LeanObject,
    mut v_cmp_3895_: *mut LeanObject,
    mut v_inst_3896_: *mut LeanObject,
    mut v_t_u2081_3897_: *mut LeanObject,
    mut v_t_u2082_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3895_,
        v_t_u2081_3897_,
        v_t_u2082_3898_,
    );
    return v___x_3899_;
}
pub unsafe fn l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(
    mut v_cmp_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    v___x_3901_ = lean_alloc_closure(l_Std_ExtTreeSet_union as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_3901_, 0, lean_box(0));
    lean_closure_set(v___x_3901_, 1, v_cmp_3900_);
    lean_closure_set(v___x_3901_, 2, lean_box(0));
    return v___x_3901_;
}
pub unsafe fn l_Std_ExtTreeSet_instUnionOfTransCmp(
    mut v_00_u03b1_3902_: *mut LeanObject,
    mut v_cmp_3903_: *mut LeanObject,
    mut v_inst_3904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    v___x_3905_ = lean_alloc_closure(l_Std_ExtTreeSet_union as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_3905_, 0, lean_box(0));
    lean_closure_set(v___x_3905_, 1, v_cmp_3903_);
    lean_closure_set(v___x_3905_, 2, lean_box(0));
    return v___x_3905_;
}
pub unsafe fn l_Std_ExtTreeSet_inter___redArg(
    mut v_cmp_3906_: *mut LeanObject,
    mut v_t_u2081_3907_: *mut LeanObject,
    mut v_t_u2082_3908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    v___x_3909_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3906_,
        v_t_u2081_3907_,
        v_t_u2082_3908_,
    );
    return v___x_3909_;
}
pub unsafe fn l_Std_ExtTreeSet_inter(
    mut v_00_u03b1_3910_: *mut LeanObject,
    mut v_cmp_3911_: *mut LeanObject,
    mut v_inst_3912_: *mut LeanObject,
    mut v_t_u2081_3913_: *mut LeanObject,
    mut v_t_u2082_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    v___x_3915_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3911_,
        v_t_u2081_3913_,
        v_t_u2082_3914_,
    );
    return v___x_3915_;
}
pub unsafe fn l_Std_ExtTreeSet_instInterOfTransCmp___redArg(
    mut v_cmp_3916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    v___x_3917_ = lean_alloc_closure(l_Std_ExtTreeSet_inter as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_3917_, 0, lean_box(0));
    lean_closure_set(v___x_3917_, 1, v_cmp_3916_);
    lean_closure_set(v___x_3917_, 2, lean_box(0));
    return v___x_3917_;
}
pub unsafe fn l_Std_ExtTreeSet_instInterOfTransCmp(
    mut v_00_u03b1_3918_: *mut LeanObject,
    mut v_cmp_3919_: *mut LeanObject,
    mut v_inst_3920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    v___x_3921_ = lean_alloc_closure(l_Std_ExtTreeSet_inter as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_3921_, 0, lean_box(0));
    lean_closure_set(v___x_3921_, 1, v_cmp_3919_);
    lean_closure_set(v___x_3921_, 2, lean_box(0));
    return v___x_3921_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3923_: *mut LeanObject = core::ptr::null_mut();
    v___x_3922_ = lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3923_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3923_, 0, v___x_3922_);
    return v___f_3923_;
}
pub unsafe fn l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(
    mut v_cmp_3924_: *mut LeanObject,
    mut v_m_u2081_3925_: *mut LeanObject,
    mut v_m_u2082_3926_: *mut LeanObject,
) -> u8 {
    let mut v___f_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    v___f_3927_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0,
    );
    v___x_3928_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_3924_,
        v___f_3927_,
        v_m_u2081_3925_,
        v_m_u2082_3926_,
    );
    return v___x_3928_;
}
pub unsafe fn l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed(
    mut v_cmp_3929_: *mut LeanObject,
    mut v_m_u2081_3930_: *mut LeanObject,
    mut v_m_u2082_3931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3932_: u8 = 0;
    let mut v_r_3933_: *mut LeanObject = core::ptr::null_mut();
    v_res_3932_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(
        v_cmp_3929_,
        v_m_u2081_3930_,
        v_m_u2082_3931_,
    );
    v_r_3933_ = lean_box((v_res_3932_) as usize);
    return v_r_3933_;
}
pub unsafe fn l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(
    mut v_cmp_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3935_: *mut LeanObject = core::ptr::null_mut();
    v___f_3935_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3935_, 0, v_cmp_3934_);
    return v___f_3935_;
}
pub unsafe fn l_Std_ExtTreeSet_instBEqOfTransCmp(
    mut v_00_u03b1_3936_: *mut LeanObject,
    mut v_cmp_3937_: *mut LeanObject,
    mut v_inst_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3939_: *mut LeanObject = core::ptr::null_mut();
    v___f_3939_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3939_, 0, v_cmp_3937_);
    return v___f_3939_;
}
pub unsafe fn l_Std_ExtTreeSet_diff___redArg(
    mut v_cmp_3940_: *mut LeanObject,
    mut v_t_u2081_3941_: *mut LeanObject,
    mut v_t_u2082_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_3940_,
        v_t_u2081_3941_,
        v_t_u2082_3942_,
    );
    return v___x_3943_;
}
pub unsafe fn l_Std_ExtTreeSet_diff(
    mut v_00_u03b1_3944_: *mut LeanObject,
    mut v_cmp_3945_: *mut LeanObject,
    mut v_inst_3946_: *mut LeanObject,
    mut v_t_u2081_3947_: *mut LeanObject,
    mut v_t_u2082_3948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    v___x_3949_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_3945_,
        v_t_u2081_3947_,
        v_t_u2082_3948_,
    );
    return v___x_3949_;
}
pub unsafe fn l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(
    mut v_cmp_3950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    v___x_3951_ = lean_alloc_closure(l_Std_ExtTreeSet_diff as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_3951_, 0, lean_box(0));
    lean_closure_set(v___x_3951_, 1, v_cmp_3950_);
    lean_closure_set(v___x_3951_, 2, lean_box(0));
    return v___x_3951_;
}
pub unsafe fn l_Std_ExtTreeSet_instSDiffOfTransCmp(
    mut v_00_u03b1_3952_: *mut LeanObject,
    mut v_cmp_3953_: *mut LeanObject,
    mut v_inst_3954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    v___x_3955_ = lean_alloc_closure(l_Std_ExtTreeSet_diff as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_3955_, 0, lean_box(0));
    lean_closure_set(v___x_3955_, 1, v_cmp_3953_);
    lean_closure_set(v___x_3955_, 2, lean_box(0));
    return v___x_3955_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(
    mut v_cmp_3956_: *mut LeanObject,
    mut v_x_3957_: *mut LeanObject,
    mut v_x_3958_: *mut LeanObject,
) -> u8 {
    let mut v___f_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: u8 = 0;
    v___f_3959_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0,
    );
    v___x_3960_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_3956_,
        v___f_3959_,
        v_x_3957_,
        v_x_3958_,
    );
    return v___x_3960_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg___boxed(
    mut v_cmp_3961_: *mut LeanObject,
    mut v_x_3962_: *mut LeanObject,
    mut v_x_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3964_: u8 = 0;
    let mut v_r_3965_: *mut LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(
        v_cmp_3961_,
        v_x_3962_,
        v_x_3963_,
    );
    v_r_3965_ = lean_box((v_res_3964_) as usize);
    return v_r_3965_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(
    mut v_00_u03b1_3966_: *mut LeanObject,
    mut v_cmp_3967_: *mut LeanObject,
    mut v_inst_3968_: *mut LeanObject,
    mut v_inst_3969_: *mut LeanObject,
    mut v_x_3970_: *mut LeanObject,
    mut v_x_3971_: *mut LeanObject,
) -> u8 {
    let mut v___x_3972_: u8 = 0;
    v___x_3972_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(
        v_cmp_3967_,
        v_x_3970_,
        v_x_3971_,
    );
    return v___x_3972_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___boxed(
    mut v_00_u03b1_3973_: *mut LeanObject,
    mut v_cmp_3974_: *mut LeanObject,
    mut v_inst_3975_: *mut LeanObject,
    mut v_inst_3976_: *mut LeanObject,
    mut v_x_3977_: *mut LeanObject,
    mut v_x_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3979_: u8 = 0;
    let mut v_r_3980_: *mut LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(
        v_00_u03b1_3973_,
        v_cmp_3974_,
        v_inst_3975_,
        v_inst_3976_,
        v_x_3977_,
        v_x_3978_,
    );
    v_r_3980_ = lean_box((v_res_3979_) as usize);
    return v_r_3980_;
}
pub unsafe fn l_Std_ExtTreeSet_eraseMany___redArg___lam__0(
    mut v_cmp_3981_: *mut LeanObject,
    mut v_a_3982_: *mut LeanObject,
    mut v_____s_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_acc_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    v_acc_3984_ =
        l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3981_, v_a_3982_, v_____s_3983_);
    v___x_3985_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3985_, 0, v_acc_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Std_ExtTreeSet_eraseMany___redArg(
    mut v_cmp_3986_: *mut LeanObject,
    mut v_inst_3987_: *mut LeanObject,
    mut v_t_3988_: *mut LeanObject,
    mut v_l_3989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    v___f_3990_ = lean_alloc_closure(
        l_Std_ExtTreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3990_, 0, v_cmp_3986_);
    v___x_3991_ = lean_apply_4(v_inst_3987_, lean_box(0), v_l_3989_, v_t_3988_, v___f_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Std_ExtTreeSet_eraseMany(
    mut v_00_u03b1_3992_: *mut LeanObject,
    mut v_cmp_3993_: *mut LeanObject,
    mut v_inst_3994_: *mut LeanObject,
    mut v_00_u03c1_3995_: *mut LeanObject,
    mut v_inst_3996_: *mut LeanObject,
    mut v_t_3997_: *mut LeanObject,
    mut v_l_3998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    v___f_3999_ = lean_alloc_closure(
        l_Std_ExtTreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3999_, 0, v_cmp_3993_);
    v___x_4000_ = lean_apply_4(v_inst_3996_, lean_box(0), v_l_3998_, v_t_3997_, v___f_3999_);
    return v___x_4000_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(
    mut v___f_4004_: *mut LeanObject,
    mut v_inst_4005_: *mut LeanObject,
    mut v_m_4006_: *mut LeanObject,
    mut v_prec_4007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    v___x_4008_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1;
    v___x_4009_ = lean_box(0);
    v___x_4010_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
    v___x_4011_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4010_,
        v___f_4004_,
        v___x_4009_,
        v_m_4006_,
    );
    v___x_4012_ = l_List_repr___redArg(v_inst_4005_, v___x_4011_);
    v___x_4013_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4013_, 0, v___x_4008_);
    lean_ctor_set(v___x_4013_, 1, v___x_4012_);
    v___x_4014_ = l_Repr_addAppParen(v___x_4013_, v_prec_4007_);
    return v___x_4014_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(
    mut v___f_4015_: *mut LeanObject,
    mut v_inst_4016_: *mut LeanObject,
    mut v_m_4017_: *mut LeanObject,
    mut v_prec_4018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4019_: *mut LeanObject = core::ptr::null_mut();
    v_res_4019_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(
        v___f_4015_,
        v_inst_4016_,
        v_m_4017_,
        v_prec_4018_,
    );
    lean_dec(v_prec_4018_);
    return v_res_4019_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___redArg(
    mut v_inst_4020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4022_: *mut LeanObject = core::ptr::null_mut();
    v___f_4021_ = l_Std_ExtTreeSet_toList___redArg___closed__0;
    v___f_4022_ = lean_alloc_closure(
        l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_4022_, 0, v___f_4021_);
    lean_closure_set(v___f_4022_, 1, v_inst_4020_);
    return v___f_4022_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp(
    mut v_00_u03b1_4023_: *mut LeanObject,
    mut v_cmp_4024_: *mut LeanObject,
    mut v_inst_4025_: *mut LeanObject,
    mut v_inst_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg(v_inst_4026_);
    return v___x_4027_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___boxed(
    mut v_00_u03b1_4028_: *mut LeanObject,
    mut v_cmp_4029_: *mut LeanObject,
    mut v_inst_4030_: *mut LeanObject,
    mut v_inst_4031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4032_: *mut LeanObject = core::ptr::null_mut();
    v_res_4032_ = l_Std_ExtTreeSet_instReprOfTransCmp(
        v_00_u03b1_4028_,
        v_cmp_4029_,
        v_inst_4030_,
        v_inst_4031_,
    );
    lean_dec_ref(v_cmp_4029_);
    return v_res_4032_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtTreeSet_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtTreeSet_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_ExtTreeSet___auto__1 = _init_l_Std_ExtTreeSet___auto__1();
    lean_mark_persistent(l_Std_ExtTreeSet___auto__1);
    l_Std_ExtTreeSet_ofList___auto__1 = _init_l_Std_ExtTreeSet_ofList___auto__1();
    lean_mark_persistent(l_Std_ExtTreeSet_ofList___auto__1);
    l_Std_ExtTreeSet_ofArray___auto__1 = _init_l_Std_ExtTreeSet_ofArray___auto__1();
    lean_mark_persistent(l_Std_ExtTreeSet_ofArray___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ExtTreeSet_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtTreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtTreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_ExtTreeSet_Basic(builtin);
}
