// Lean compiler output
// Module: Std.Data.ExtTreeSet.Basic
// Imports: Std.Data.ExtTreeMap.Basic
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_lt, lean_nat_mul, lean_string_utf8_byte_size, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_mkAtom, l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_panic___redArg,
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
pub static l_Std_ExtTreeSet___auto__1___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Std_ExtTreeSet___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_ExtTreeSet___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeSet___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeSet___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtTreeSet___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
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
static mut l_Std_ExtTreeSet___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__6_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Std_ExtTreeSet___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeSet___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeSet___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtTreeSet___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__8_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet___auto__1___closed__10_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_ExtTreeSet___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Std_ExtTreeSet___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeSet___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeSet___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtTreeSet___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeSet___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeSet___auto__1___closed__14_value: leanh::LeanStringObject<8> =
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
        m_data: [99, 111, 109, 112, 97, 114, 101, 0],
    };
static mut l_Std_ExtTreeSet___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeSet___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeSet___auto__1___closed__17_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16710690322389477741 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeSet___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeSet___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_ExtTreeSet___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet_getGE_x21___redArg___closed__0_value: leanh::LeanStringObject<
    26,
> = leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_getGE_x21___redArg___closed__1_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_getGE_x21___redArg___closed__2_value: leanh::LeanStringObject<
    14,
> = leanh::LeanStringObject {
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
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeSet_getGE_x21___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeSet_foldr___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_foldr___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet_foldr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_foldr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_partition___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet_partition___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_partition___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_any___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeSet_any___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_any___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeSet_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtTreeSet_ofList___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeSet_toArray___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeSet_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeSet_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtTreeSet_ofArray___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Std_ExtTreeSet___auto__1___closed__10;
    v___x_2044_ = l_Lean_mkAtom(v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2045_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__12_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__12,
    );
    v___x_2046_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2047_ = lean_array_push(v___x_2046_, v___x_2045_);
    return v___x_2047_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Std_ExtTreeSet___auto__1___closed__14;
    v___x_2050_ = lean_string_utf8_byte_size(v___x_2049_);
    return v___x_2050_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__15_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__15,
    );
    v___x_2052_ = leanh::lean_unsigned_to_nat(0);
    v___x_2053_ = l_Std_ExtTreeSet___auto__1___closed__14;
    v___x_2054_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2054_, 0, v___x_2053_);
    leanh::lean_ctor_set(v___x_2054_, 1, v___x_2052_);
    leanh::lean_ctor_set(v___x_2054_, 2, v___x_2051_);
    return v___x_2054_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = leanh::lean_box(0);
    v___x_2058_ = l_Std_ExtTreeSet___auto__1___closed__17;
    v___x_2059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__16_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__16,
    );
    v___x_2060_ = leanh::lean_box(2);
    v___x_2061_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2061_, 0, v___x_2060_);
    leanh::lean_ctor_set(v___x_2061_, 1, v___x_2059_);
    leanh::lean_ctor_set(v___x_2061_, 2, v___x_2058_);
    leanh::lean_ctor_set(v___x_2061_, 3, v___x_2057_);
    return v___x_2061_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__18_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__18,
    );
    v___x_2063_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__13_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__13,
    );
    v___x_2064_ = lean_array_push(v___x_2063_, v___x_2062_);
    return v___x_2064_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__19_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__19,
    );
    v___x_2066_ = l_Std_ExtTreeSet___auto__1___closed__11;
    v___x_2067_ = leanh::lean_box(2);
    v___x_2068_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2068_, 0, v___x_2067_);
    leanh::lean_ctor_set(v___x_2068_, 1, v___x_2066_);
    leanh::lean_ctor_set(v___x_2068_, 2, v___x_2065_);
    return v___x_2068_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__20_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__20,
    );
    v___x_2070_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2071_ = lean_array_push(v___x_2070_, v___x_2069_);
    return v___x_2071_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__21_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__21,
    );
    v___x_2073_ = l_Std_ExtTreeSet___auto__1___closed__9;
    v___x_2074_ = leanh::lean_box(2);
    v___x_2075_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2075_, 0, v___x_2074_);
    leanh::lean_ctor_set(v___x_2075_, 1, v___x_2073_);
    leanh::lean_ctor_set(v___x_2075_, 2, v___x_2072_);
    return v___x_2075_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2076_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__22_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__22,
    );
    v___x_2077_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2078_ = lean_array_push(v___x_2077_, v___x_2076_);
    return v___x_2078_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2079_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__23_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__23,
    );
    v___x_2080_ = l_Std_ExtTreeSet___auto__1___closed__7;
    v___x_2081_ = leanh::lean_box(2);
    v___x_2082_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2082_, 0, v___x_2081_);
    leanh::lean_ctor_set(v___x_2082_, 1, v___x_2080_);
    leanh::lean_ctor_set(v___x_2082_, 2, v___x_2079_);
    return v___x_2082_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__24_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__24,
    );
    v___x_2084_ = l_Std_ExtTreeSet___auto__1___closed__5;
    v___x_2085_ = lean_array_push(v___x_2084_, v___x_2083_);
    return v___x_2085_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2086_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__25_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__25,
    );
    v___x_2087_ = l_Std_ExtTreeSet___auto__1___closed__4;
    v___x_2088_ = leanh::lean_box(2);
    v___x_2089_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2089_, 0, v___x_2088_);
    leanh::lean_ctor_set(v___x_2089_, 1, v___x_2087_);
    leanh::lean_ctor_set(v___x_2089_, 2, v___x_2086_);
    return v___x_2089_;
}
pub unsafe fn _init_l_Std_ExtTreeSet___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2090_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__26,
    );
    return v___x_2090_;
}
pub unsafe fn l_Std_ExtTreeSet_empty(
    mut v_00_u03b1_2091_: *mut leanh::LeanObject,
    mut v_cmp_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ = leanh::lean_box(1);
    return v___x_2093_;
}
pub unsafe fn l_Std_ExtTreeSet_empty___boxed(
    mut v_00_u03b1_2094_: *mut leanh::LeanObject,
    mut v_cmp_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Std_ExtTreeSet_empty(v_00_u03b1_2094_, v_cmp_2095_);
    leanh::lean_dec_ref(v_cmp_2095_);
    return v_res_2096_;
}
pub unsafe fn l_Std_ExtTreeSet_instEmptyCollection(
    mut v_00_u03b1_2097_: *mut leanh::LeanObject,
    mut v_cmp_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2099_ = leanh::lean_box(1);
    return v___x_2099_;
}
pub unsafe fn l_Std_ExtTreeSet_instEmptyCollection___boxed(
    mut v_00_u03b1_2100_: *mut leanh::LeanObject,
    mut v_cmp_2101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2102_ = l_Std_ExtTreeSet_instEmptyCollection(v_00_u03b1_2100_, v_cmp_2101_);
    leanh::lean_dec_ref(v_cmp_2101_);
    return v_res_2102_;
}
pub unsafe fn l_Std_ExtTreeSet_instInhabited(
    mut v_00_u03b1_2103_: *mut leanh::LeanObject,
    mut v_cmp_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = leanh::lean_box(1);
    return v___x_2105_;
}
pub unsafe fn l_Std_ExtTreeSet_instInhabited___boxed(
    mut v_00_u03b1_2106_: *mut leanh::LeanObject,
    mut v_cmp_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_ExtTreeSet_instInhabited(v_00_u03b1_2106_, v_cmp_2107_);
    leanh::lean_dec_ref(v_cmp_2107_);
    return v_res_2108_;
}
pub unsafe fn l_Std_ExtTreeSet_insert___redArg(
    mut v_cmp_2109_: *mut leanh::LeanObject,
    mut v_l_2110_: *mut leanh::LeanObject,
    mut v_a_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2112_: u8 = 0;
    leanh::lean_inc(v_l_2110_);
    leanh::lean_inc(v_a_2111_);
    leanh::lean_inc_ref(v_cmp_2109_);
    v___x_2112_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2109_, v_a_2111_, v_l_2110_);
    if v___x_2112_ == 0 {
        let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2113_ = leanh::lean_box(0);
        v___x_2114_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2109_,
            v_a_2111_,
            v___x_2113_,
            v_l_2110_,
        );
        return v___x_2114_;
    } else {
        leanh::lean_dec(v_a_2111_);
        leanh::lean_dec_ref(v_cmp_2109_);
        return v_l_2110_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_insert(
    mut v_00_u03b1_2115_: *mut leanh::LeanObject,
    mut v_cmp_2116_: *mut leanh::LeanObject,
    mut v_inst_2117_: *mut leanh::LeanObject,
    mut v_l_2118_: *mut leanh::LeanObject,
    mut v_a_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2120_: u8 = 0;
    leanh::lean_inc(v_l_2118_);
    leanh::lean_inc(v_a_2119_);
    leanh::lean_inc_ref(v_cmp_2116_);
    v___x_2120_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2116_, v_a_2119_, v_l_2118_);
    if v___x_2120_ == 0 {
        let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2121_ = leanh::lean_box(0);
        v___x_2122_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2116_,
            v_a_2119_,
            v___x_2121_,
            v_l_2118_,
        );
        return v___x_2122_;
    } else {
        leanh::lean_dec(v_a_2119_);
        leanh::lean_dec_ref(v_cmp_2116_);
        return v_l_2118_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0(
    mut v_cmp_2123_: *mut leanh::LeanObject,
    mut v_e_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    v___x_2125_ = leanh::lean_box(1);
    leanh::lean_inc(v_e_2124_);
    leanh::lean_inc_ref(v_cmp_2123_);
    v___x_2126_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2123_, v_e_2124_, v___x_2125_);
    if v___x_2126_ == 0 {
        let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2127_ = leanh::lean_box(0);
        v___x_2128_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2123_,
            v_e_2124_,
            v___x_2127_,
            v___x_2125_,
        );
        return v___x_2128_;
    } else {
        leanh::lean_dec(v_e_2124_);
        leanh::lean_dec_ref(v_cmp_2123_);
        return v___x_2125_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg(
    mut v_cmp_2129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2130_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2130_, 0, v_cmp_2129_);
    return v___f_2130_;
}
pub unsafe fn l_Std_ExtTreeSet_instSingletonOfTransCmp(
    mut v_00_u03b1_2131_: *mut leanh::LeanObject,
    mut v_cmp_2132_: *mut leanh::LeanObject,
    mut v_inst_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2134_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instSingletonOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2134_, 0, v_cmp_2132_);
    return v___f_2134_;
}
pub unsafe fn l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0(
    mut v_cmp_2135_: *mut leanh::LeanObject,
    mut v_e_2136_: *mut leanh::LeanObject,
    mut v_s_2137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2138_: u8 = 0;
    leanh::lean_inc(v_s_2137_);
    leanh::lean_inc(v_e_2136_);
    leanh::lean_inc_ref(v_cmp_2135_);
    v___x_2138_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2135_, v_e_2136_, v_s_2137_);
    if v___x_2138_ == 0 {
        let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2139_ = leanh::lean_box(0);
        v___x_2140_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2135_,
            v_e_2136_,
            v___x_2139_,
            v_s_2137_,
        );
        return v___x_2140_;
    } else {
        leanh::lean_dec(v_e_2136_);
        leanh::lean_dec_ref(v_cmp_2135_);
        return v_s_2137_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_instInsertOfTransCmp___redArg(
    mut v_cmp_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2142_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2142_, 0, v_cmp_2141_);
    return v___f_2142_;
}
pub unsafe fn l_Std_ExtTreeSet_instInsertOfTransCmp(
    mut v_00_u03b1_2143_: *mut leanh::LeanObject,
    mut v_cmp_2144_: *mut leanh::LeanObject,
    mut v_inst_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2146_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instInsertOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2146_, 0, v_cmp_2144_);
    return v___f_2146_;
}
pub unsafe fn l_Std_ExtTreeSet_containsThenInsert___redArg(
    mut v_cmp_2147_: *mut leanh::LeanObject,
    mut v_t_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2150_: u8 = 0;
    leanh::lean_inc(v_t_2148_);
    leanh::lean_inc(v_a_2149_);
    leanh::lean_inc_ref(v_cmp_2147_);
    v___x_2150_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2147_, v_a_2149_, v_t_2148_);
    if v___x_2150_ == 0 {
        let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2151_ = leanh::lean_box(0);
        v___x_2152_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2147_,
            v_a_2149_,
            v___x_2151_,
            v_t_2148_,
        );
        v___x_2153_ = leanh::lean_box((v___x_2150_) as usize);
        v___x_2154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2154_, 0, v___x_2153_);
        leanh::lean_ctor_set(v___x_2154_, 1, v___x_2152_);
        return v___x_2154_;
    } else {
        let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_2149_);
        leanh::lean_dec_ref(v_cmp_2147_);
        v___x_2155_ = leanh::lean_box((v___x_2150_) as usize);
        v___x_2156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2156_, 0, v___x_2155_);
        leanh::lean_ctor_set(v___x_2156_, 1, v_t_2148_);
        return v___x_2156_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_containsThenInsert(
    mut v_00_u03b1_2157_: *mut leanh::LeanObject,
    mut v_cmp_2158_: *mut leanh::LeanObject,
    mut v_inst_2159_: *mut leanh::LeanObject,
    mut v_t_2160_: *mut leanh::LeanObject,
    mut v_a_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2162_: u8 = 0;
    leanh::lean_inc(v_t_2160_);
    leanh::lean_inc(v_a_2161_);
    leanh::lean_inc_ref(v_cmp_2158_);
    v___x_2162_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2158_, v_a_2161_, v_t_2160_);
    if v___x_2162_ == 0 {
        let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2163_ = leanh::lean_box(0);
        v___x_2164_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2158_,
            v_a_2161_,
            v___x_2163_,
            v_t_2160_,
        );
        v___x_2165_ = leanh::lean_box((v___x_2162_) as usize);
        v___x_2166_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
        leanh::lean_ctor_set(v___x_2166_, 1, v___x_2164_);
        return v___x_2166_;
    } else {
        let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_2161_);
        leanh::lean_dec_ref(v_cmp_2158_);
        v___x_2167_ = leanh::lean_box((v___x_2162_) as usize);
        v___x_2168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2168_, 0, v___x_2167_);
        leanh::lean_ctor_set(v___x_2168_, 1, v_t_2160_);
        return v___x_2168_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_contains___redArg(
    mut v_cmp_2169_: *mut leanh::LeanObject,
    mut v_l_2170_: *mut leanh::LeanObject,
    mut v_a_2171_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2172_: u8 = 0;
    v___x_2172_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2169_, v_a_2171_, v_l_2170_);
    return v___x_2172_;
}
pub unsafe fn l_Std_ExtTreeSet_contains___redArg___boxed(
    mut v_cmp_2173_: *mut leanh::LeanObject,
    mut v_l_2174_: *mut leanh::LeanObject,
    mut v_a_2175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2176_: u8 = 0;
    let mut v_r_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2176_ = l_Std_ExtTreeSet_contains___redArg(v_cmp_2173_, v_l_2174_, v_a_2175_);
    v_r_2177_ = leanh::lean_box((v_res_2176_) as usize);
    return v_r_2177_;
}
pub unsafe fn l_Std_ExtTreeSet_contains(
    mut v_00_u03b1_2178_: *mut leanh::LeanObject,
    mut v_cmp_2179_: *mut leanh::LeanObject,
    mut v_inst_2180_: *mut leanh::LeanObject,
    mut v_l_2181_: *mut leanh::LeanObject,
    mut v_a_2182_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2183_: u8 = 0;
    v___x_2183_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2179_, v_a_2182_, v_l_2181_);
    return v___x_2183_;
}
pub unsafe fn l_Std_ExtTreeSet_contains___boxed(
    mut v_00_u03b1_2184_: *mut leanh::LeanObject,
    mut v_cmp_2185_: *mut leanh::LeanObject,
    mut v_inst_2186_: *mut leanh::LeanObject,
    mut v_l_2187_: *mut leanh::LeanObject,
    mut v_a_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2189_: u8 = 0;
    let mut v_r_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2189_ = l_Std_ExtTreeSet_contains(
        v_00_u03b1_2184_,
        v_cmp_2185_,
        v_inst_2186_,
        v_l_2187_,
        v_a_2188_,
    );
    v_r_2190_ = leanh::lean_box((v_res_2189_) as usize);
    return v_r_2190_;
}
pub unsafe fn l_Std_ExtTreeSet_instMembershipOfTransCmp(
    mut v_00_u03b1_2191_: *mut leanh::LeanObject,
    mut v_cmp_2192_: *mut leanh::LeanObject,
    mut v_inst_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = leanh::lean_box(0);
    return v___x_2194_;
}
pub unsafe fn l_Std_ExtTreeSet_instMembershipOfTransCmp___boxed(
    mut v_00_u03b1_2195_: *mut leanh::LeanObject,
    mut v_cmp_2196_: *mut leanh::LeanObject,
    mut v_inst_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ =
        l_Std_ExtTreeSet_instMembershipOfTransCmp(v_00_u03b1_2195_, v_cmp_2196_, v_inst_2197_);
    leanh::lean_dec_ref(v_cmp_2196_);
    return v_res_2198_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem___redArg(
    mut v_cmp_2199_: *mut leanh::LeanObject,
    mut v_m_2200_: *mut leanh::LeanObject,
    mut v_a_2201_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2202_: u8 = 0;
    v___x_2202_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2199_, v_a_2201_, v_m_2200_);
    return v___x_2202_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem___redArg___boxed(
    mut v_cmp_2203_: *mut leanh::LeanObject,
    mut v_m_2204_: *mut leanh::LeanObject,
    mut v_a_2205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2206_: u8 = 0;
    let mut v_r_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Std_ExtTreeSet_instDecidableMem___redArg(v_cmp_2203_, v_m_2204_, v_a_2205_);
    v_r_2207_ = leanh::lean_box((v_res_2206_) as usize);
    return v_r_2207_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem(
    mut v_00_u03b1_2208_: *mut leanh::LeanObject,
    mut v_cmp_2209_: *mut leanh::LeanObject,
    mut v_inst_2210_: *mut leanh::LeanObject,
    mut v_m_2211_: *mut leanh::LeanObject,
    mut v_a_2212_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2213_: u8 = 0;
    v___x_2213_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2209_, v_a_2212_, v_m_2211_);
    return v___x_2213_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableMem___boxed(
    mut v_00_u03b1_2214_: *mut leanh::LeanObject,
    mut v_cmp_2215_: *mut leanh::LeanObject,
    mut v_inst_2216_: *mut leanh::LeanObject,
    mut v_m_2217_: *mut leanh::LeanObject,
    mut v_a_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2219_: u8 = 0;
    let mut v_r_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2219_ = l_Std_ExtTreeSet_instDecidableMem(
        v_00_u03b1_2214_,
        v_cmp_2215_,
        v_inst_2216_,
        v_m_2217_,
        v_a_2218_,
    );
    v_r_2220_ = leanh::lean_box((v_res_2219_) as usize);
    return v_r_2220_;
}
pub unsafe fn l_Std_ExtTreeSet_size___redArg(
    mut v_t_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_2221_) == 0 {
        let mut v_size_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_size_2222_ = leanh::lean_ctor_get(v_t_2221_, 0);
        leanh::lean_inc(v_size_2222_);
        return v_size_2222_;
    } else {
        let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2223_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2223_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_size___redArg___boxed(
    mut v_t_2224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2225_ = l_Std_ExtTreeSet_size___redArg(v_t_2224_);
    leanh::lean_dec(v_t_2224_);
    return v_res_2225_;
}
pub unsafe fn l_Std_ExtTreeSet_size(
    mut v_00_u03b1_2226_: *mut leanh::LeanObject,
    mut v_cmp_2227_: *mut leanh::LeanObject,
    mut v_t_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_2228_) == 0 {
        let mut v_size_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_size_2229_ = leanh::lean_ctor_get(v_t_2228_, 0);
        leanh::lean_inc(v_size_2229_);
        return v_size_2229_;
    } else {
        let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2230_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2230_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_size___boxed(
    mut v_00_u03b1_2231_: *mut leanh::LeanObject,
    mut v_cmp_2232_: *mut leanh::LeanObject,
    mut v_t_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2234_ = l_Std_ExtTreeSet_size(v_00_u03b1_2231_, v_cmp_2232_, v_t_2233_);
    leanh::lean_dec(v_t_2233_);
    leanh::lean_dec_ref(v_cmp_2232_);
    return v_res_2234_;
}
pub unsafe fn l_Std_ExtTreeSet_isEmpty___redArg(
    mut v_t_2235_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_t_2235_) == 0 {
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
    mut v_t_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2239_: u8 = 0;
    let mut v_r_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Std_ExtTreeSet_isEmpty___redArg(v_t_2238_);
    leanh::lean_dec(v_t_2238_);
    v_r_2240_ = leanh::lean_box((v_res_2239_) as usize);
    return v_r_2240_;
}
pub unsafe fn l_Std_ExtTreeSet_isEmpty(
    mut v_00_u03b1_2241_: *mut leanh::LeanObject,
    mut v_cmp_2242_: *mut leanh::LeanObject,
    mut v_t_2243_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_t_2243_) == 0 {
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
    mut v_00_u03b1_2246_: *mut leanh::LeanObject,
    mut v_cmp_2247_: *mut leanh::LeanObject,
    mut v_t_2248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2249_: u8 = 0;
    let mut v_r_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2249_ = l_Std_ExtTreeSet_isEmpty(v_00_u03b1_2246_, v_cmp_2247_, v_t_2248_);
    leanh::lean_dec(v_t_2248_);
    leanh::lean_dec_ref(v_cmp_2247_);
    v_r_2250_ = leanh::lean_box((v_res_2249_) as usize);
    return v_r_2250_;
}
pub unsafe fn l_Std_ExtTreeSet_erase___redArg(
    mut v_cmp_2251_: *mut leanh::LeanObject,
    mut v_t_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2251_, v_a_2253_, v_t_2252_);
    return v___x_2254_;
}
pub unsafe fn l_Std_ExtTreeSet_erase(
    mut v_00_u03b1_2255_: *mut leanh::LeanObject,
    mut v_cmp_2256_: *mut leanh::LeanObject,
    mut v_inst_2257_: *mut leanh::LeanObject,
    mut v_t_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2256_, v_a_2259_, v_t_2258_);
    return v___x_2260_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x3f___redArg(
    mut v_cmp_2261_: *mut leanh::LeanObject,
    mut v_t_2262_: *mut leanh::LeanObject,
    mut v_a_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2261_, v_t_2262_, v_a_2263_);
    return v___x_2264_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x3f(
    mut v_00_u03b1_2265_: *mut leanh::LeanObject,
    mut v_cmp_2266_: *mut leanh::LeanObject,
    mut v_inst_2267_: *mut leanh::LeanObject,
    mut v_t_2268_: *mut leanh::LeanObject,
    mut v_a_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2270_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2266_, v_t_2268_, v_a_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Std_ExtTreeSet_get___redArg(
    mut v_cmp_2271_: *mut leanh::LeanObject,
    mut v_t_2272_: *mut leanh::LeanObject,
    mut v_a_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2274_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2271_, v_t_2272_, v_a_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Std_ExtTreeSet_get(
    mut v_00_u03b1_2275_: *mut leanh::LeanObject,
    mut v_cmp_2276_: *mut leanh::LeanObject,
    mut v_inst_2277_: *mut leanh::LeanObject,
    mut v_t_2278_: *mut leanh::LeanObject,
    mut v_a_2279_: *mut leanh::LeanObject,
    mut v_h_2280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2276_, v_t_2278_, v_a_2279_);
    return v___x_2281_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21___redArg(
    mut v_cmp_2282_: *mut leanh::LeanObject,
    mut v_inst_2283_: *mut leanh::LeanObject,
    mut v_t_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2282_,
        v_t_2284_,
        v_a_2285_,
        v_inst_2283_,
    );
    return v___x_2286_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21___redArg___boxed(
    mut v_cmp_2287_: *mut leanh::LeanObject,
    mut v_inst_2288_: *mut leanh::LeanObject,
    mut v_t_2289_: *mut leanh::LeanObject,
    mut v_a_2290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2291_ =
        l_Std_ExtTreeSet_get_x21___redArg(v_cmp_2287_, v_inst_2288_, v_t_2289_, v_a_2290_);
    leanh::lean_dec(v_inst_2288_);
    return v_res_2291_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21(
    mut v_00_u03b1_2292_: *mut leanh::LeanObject,
    mut v_cmp_2293_: *mut leanh::LeanObject,
    mut v_inst_2294_: *mut leanh::LeanObject,
    mut v_inst_2295_: *mut leanh::LeanObject,
    mut v_t_2296_: *mut leanh::LeanObject,
    mut v_a_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2293_,
        v_t_2296_,
        v_a_2297_,
        v_inst_2295_,
    );
    return v___x_2298_;
}
pub unsafe fn l_Std_ExtTreeSet_get_x21___boxed(
    mut v_00_u03b1_2299_: *mut leanh::LeanObject,
    mut v_cmp_2300_: *mut leanh::LeanObject,
    mut v_inst_2301_: *mut leanh::LeanObject,
    mut v_inst_2302_: *mut leanh::LeanObject,
    mut v_t_2303_: *mut leanh::LeanObject,
    mut v_a_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2305_ = l_Std_ExtTreeSet_get_x21(
        v_00_u03b1_2299_,
        v_cmp_2300_,
        v_inst_2301_,
        v_inst_2302_,
        v_t_2303_,
        v_a_2304_,
    );
    leanh::lean_dec(v_inst_2302_);
    return v_res_2305_;
}
pub unsafe fn l_Std_ExtTreeSet_getD___redArg(
    mut v_cmp_2306_: *mut leanh::LeanObject,
    mut v_t_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
    mut v_fallback_2309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2306_,
        v_t_2307_,
        v_a_2308_,
        v_fallback_2309_,
    );
    return v___x_2310_;
}
pub unsafe fn l_Std_ExtTreeSet_getD___redArg___boxed(
    mut v_cmp_2311_: *mut leanh::LeanObject,
    mut v_t_2312_: *mut leanh::LeanObject,
    mut v_a_2313_: *mut leanh::LeanObject,
    mut v_fallback_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ =
        l_Std_ExtTreeSet_getD___redArg(v_cmp_2311_, v_t_2312_, v_a_2313_, v_fallback_2314_);
    leanh::lean_dec(v_fallback_2314_);
    return v_res_2315_;
}
pub unsafe fn l_Std_ExtTreeSet_getD(
    mut v_00_u03b1_2316_: *mut leanh::LeanObject,
    mut v_cmp_2317_: *mut leanh::LeanObject,
    mut v_inst_2318_: *mut leanh::LeanObject,
    mut v_t_2319_: *mut leanh::LeanObject,
    mut v_a_2320_: *mut leanh::LeanObject,
    mut v_fallback_2321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2322_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2317_,
        v_t_2319_,
        v_a_2320_,
        v_fallback_2321_,
    );
    return v___x_2322_;
}
pub unsafe fn l_Std_ExtTreeSet_getD___boxed(
    mut v_00_u03b1_2323_: *mut leanh::LeanObject,
    mut v_cmp_2324_: *mut leanh::LeanObject,
    mut v_inst_2325_: *mut leanh::LeanObject,
    mut v_t_2326_: *mut leanh::LeanObject,
    mut v_a_2327_: *mut leanh::LeanObject,
    mut v_fallback_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Std_ExtTreeSet_getD(
        v_00_u03b1_2323_,
        v_cmp_2324_,
        v_inst_2325_,
        v_t_2326_,
        v_a_2327_,
        v_fallback_2328_,
    );
    leanh::lean_dec(v_fallback_2328_);
    return v_res_2329_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f___redArg(
    mut v_t_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2331_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2330_);
    return v___x_2331_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f___redArg___boxed(
    mut v_t_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Std_ExtTreeSet_min_x3f___redArg(v_t_2332_);
    leanh::lean_dec(v_t_2332_);
    return v_res_2333_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f(
    mut v_00_u03b1_2334_: *mut leanh::LeanObject,
    mut v_cmp_2335_: *mut leanh::LeanObject,
    mut v_inst_2336_: *mut leanh::LeanObject,
    mut v_t_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2337_);
    return v___x_2338_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x3f___boxed(
    mut v_00_u03b1_2339_: *mut leanh::LeanObject,
    mut v_cmp_2340_: *mut leanh::LeanObject,
    mut v_inst_2341_: *mut leanh::LeanObject,
    mut v_t_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Std_ExtTreeSet_min_x3f(v_00_u03b1_2339_, v_cmp_2340_, v_inst_2341_, v_t_2342_);
    leanh::lean_dec(v_t_2342_);
    leanh::lean_dec_ref(v_cmp_2340_);
    return v_res_2343_;
}
pub unsafe fn l_Std_ExtTreeSet_min___redArg(
    mut v_t_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2344_);
    return v___x_2345_;
}
pub unsafe fn l_Std_ExtTreeSet_min___redArg___boxed(
    mut v_t_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2347_ = l_Std_ExtTreeSet_min___redArg(v_t_2346_);
    leanh::lean_dec(v_t_2346_);
    return v_res_2347_;
}
pub unsafe fn l_Std_ExtTreeSet_min(
    mut v_00_u03b1_2348_: *mut leanh::LeanObject,
    mut v_cmp_2349_: *mut leanh::LeanObject,
    mut v_inst_2350_: *mut leanh::LeanObject,
    mut v_t_2351_: *mut leanh::LeanObject,
    mut v_h_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2351_);
    return v___x_2353_;
}
pub unsafe fn l_Std_ExtTreeSet_min___boxed(
    mut v_00_u03b1_2354_: *mut leanh::LeanObject,
    mut v_cmp_2355_: *mut leanh::LeanObject,
    mut v_inst_2356_: *mut leanh::LeanObject,
    mut v_t_2357_: *mut leanh::LeanObject,
    mut v_h_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2359_ = l_Std_ExtTreeSet_min(
        v_00_u03b1_2354_,
        v_cmp_2355_,
        v_inst_2356_,
        v_t_2357_,
        v_h_2358_,
    );
    leanh::lean_dec(v_t_2357_);
    leanh::lean_dec_ref(v_cmp_2355_);
    return v_res_2359_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21___redArg(
    mut v_inst_2360_: *mut leanh::LeanObject,
    mut v_t_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2362_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2360_, v_t_2361_);
    return v___x_2362_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21___redArg___boxed(
    mut v_inst_2363_: *mut leanh::LeanObject,
    mut v_t_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2365_ = l_Std_ExtTreeSet_min_x21___redArg(v_inst_2363_, v_t_2364_);
    leanh::lean_dec(v_t_2364_);
    leanh::lean_dec(v_inst_2363_);
    return v_res_2365_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21(
    mut v_00_u03b1_2366_: *mut leanh::LeanObject,
    mut v_cmp_2367_: *mut leanh::LeanObject,
    mut v_inst_2368_: *mut leanh::LeanObject,
    mut v_inst_2369_: *mut leanh::LeanObject,
    mut v_t_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2369_, v_t_2370_);
    return v___x_2371_;
}
pub unsafe fn l_Std_ExtTreeSet_min_x21___boxed(
    mut v_00_u03b1_2372_: *mut leanh::LeanObject,
    mut v_cmp_2373_: *mut leanh::LeanObject,
    mut v_inst_2374_: *mut leanh::LeanObject,
    mut v_inst_2375_: *mut leanh::LeanObject,
    mut v_t_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l_Std_ExtTreeSet_min_x21(
        v_00_u03b1_2372_,
        v_cmp_2373_,
        v_inst_2374_,
        v_inst_2375_,
        v_t_2376_,
    );
    leanh::lean_dec(v_t_2376_);
    leanh::lean_dec(v_inst_2375_);
    leanh::lean_dec_ref(v_cmp_2373_);
    return v_res_2377_;
}
pub unsafe fn l_Std_ExtTreeSet_minD___redArg(
    mut v_t_2378_: *mut leanh::LeanObject,
    mut v_fallback_2379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2380_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2378_, v_fallback_2379_);
    return v___x_2380_;
}
pub unsafe fn l_Std_ExtTreeSet_minD___redArg___boxed(
    mut v_t_2381_: *mut leanh::LeanObject,
    mut v_fallback_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Std_ExtTreeSet_minD___redArg(v_t_2381_, v_fallback_2382_);
    leanh::lean_dec(v_fallback_2382_);
    leanh::lean_dec(v_t_2381_);
    return v_res_2383_;
}
pub unsafe fn l_Std_ExtTreeSet_minD(
    mut v_00_u03b1_2384_: *mut leanh::LeanObject,
    mut v_cmp_2385_: *mut leanh::LeanObject,
    mut v_inst_2386_: *mut leanh::LeanObject,
    mut v_t_2387_: *mut leanh::LeanObject,
    mut v_fallback_2388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2387_, v_fallback_2388_);
    return v___x_2389_;
}
pub unsafe fn l_Std_ExtTreeSet_minD___boxed(
    mut v_00_u03b1_2390_: *mut leanh::LeanObject,
    mut v_cmp_2391_: *mut leanh::LeanObject,
    mut v_inst_2392_: *mut leanh::LeanObject,
    mut v_t_2393_: *mut leanh::LeanObject,
    mut v_fallback_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Std_ExtTreeSet_minD(
        v_00_u03b1_2390_,
        v_cmp_2391_,
        v_inst_2392_,
        v_t_2393_,
        v_fallback_2394_,
    );
    leanh::lean_dec(v_fallback_2394_);
    leanh::lean_dec(v_t_2393_);
    leanh::lean_dec_ref(v_cmp_2391_);
    return v_res_2395_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f___redArg(
    mut v_t_2396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f___redArg___boxed(
    mut v_t_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Std_ExtTreeSet_max_x3f___redArg(v_t_2398_);
    leanh::lean_dec(v_t_2398_);
    return v_res_2399_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f(
    mut v_00_u03b1_2400_: *mut leanh::LeanObject,
    mut v_cmp_2401_: *mut leanh::LeanObject,
    mut v_inst_2402_: *mut leanh::LeanObject,
    mut v_t_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2404_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2403_);
    return v___x_2404_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x3f___boxed(
    mut v_00_u03b1_2405_: *mut leanh::LeanObject,
    mut v_cmp_2406_: *mut leanh::LeanObject,
    mut v_inst_2407_: *mut leanh::LeanObject,
    mut v_t_2408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2409_ = l_Std_ExtTreeSet_max_x3f(v_00_u03b1_2405_, v_cmp_2406_, v_inst_2407_, v_t_2408_);
    leanh::lean_dec(v_t_2408_);
    leanh::lean_dec_ref(v_cmp_2406_);
    return v_res_2409_;
}
pub unsafe fn l_Std_ExtTreeSet_max___redArg(
    mut v_t_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2410_);
    return v___x_2411_;
}
pub unsafe fn l_Std_ExtTreeSet_max___redArg___boxed(
    mut v_t_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Std_ExtTreeSet_max___redArg(v_t_2412_);
    leanh::lean_dec(v_t_2412_);
    return v_res_2413_;
}
pub unsafe fn l_Std_ExtTreeSet_max(
    mut v_00_u03b1_2414_: *mut leanh::LeanObject,
    mut v_cmp_2415_: *mut leanh::LeanObject,
    mut v_inst_2416_: *mut leanh::LeanObject,
    mut v_t_2417_: *mut leanh::LeanObject,
    mut v_h_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2419_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2417_);
    return v___x_2419_;
}
pub unsafe fn l_Std_ExtTreeSet_max___boxed(
    mut v_00_u03b1_2420_: *mut leanh::LeanObject,
    mut v_cmp_2421_: *mut leanh::LeanObject,
    mut v_inst_2422_: *mut leanh::LeanObject,
    mut v_t_2423_: *mut leanh::LeanObject,
    mut v_h_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_Std_ExtTreeSet_max(
        v_00_u03b1_2420_,
        v_cmp_2421_,
        v_inst_2422_,
        v_t_2423_,
        v_h_2424_,
    );
    leanh::lean_dec(v_t_2423_);
    leanh::lean_dec_ref(v_cmp_2421_);
    return v_res_2425_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21___redArg(
    mut v_inst_2426_: *mut leanh::LeanObject,
    mut v_t_2427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2428_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2426_, v_t_2427_);
    return v___x_2428_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21___redArg___boxed(
    mut v_inst_2429_: *mut leanh::LeanObject,
    mut v_t_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Std_ExtTreeSet_max_x21___redArg(v_inst_2429_, v_t_2430_);
    leanh::lean_dec(v_t_2430_);
    leanh::lean_dec(v_inst_2429_);
    return v_res_2431_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21(
    mut v_00_u03b1_2432_: *mut leanh::LeanObject,
    mut v_cmp_2433_: *mut leanh::LeanObject,
    mut v_inst_2434_: *mut leanh::LeanObject,
    mut v_inst_2435_: *mut leanh::LeanObject,
    mut v_t_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2435_, v_t_2436_);
    return v___x_2437_;
}
pub unsafe fn l_Std_ExtTreeSet_max_x21___boxed(
    mut v_00_u03b1_2438_: *mut leanh::LeanObject,
    mut v_cmp_2439_: *mut leanh::LeanObject,
    mut v_inst_2440_: *mut leanh::LeanObject,
    mut v_inst_2441_: *mut leanh::LeanObject,
    mut v_t_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Std_ExtTreeSet_max_x21(
        v_00_u03b1_2438_,
        v_cmp_2439_,
        v_inst_2440_,
        v_inst_2441_,
        v_t_2442_,
    );
    leanh::lean_dec(v_t_2442_);
    leanh::lean_dec(v_inst_2441_);
    leanh::lean_dec_ref(v_cmp_2439_);
    return v_res_2443_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD___redArg(
    mut v_t_2444_: *mut leanh::LeanObject,
    mut v_fallback_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2444_, v_fallback_2445_);
    return v___x_2446_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD___redArg___boxed(
    mut v_t_2447_: *mut leanh::LeanObject,
    mut v_fallback_2448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Std_ExtTreeSet_maxD___redArg(v_t_2447_, v_fallback_2448_);
    leanh::lean_dec(v_fallback_2448_);
    leanh::lean_dec(v_t_2447_);
    return v_res_2449_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD(
    mut v_00_u03b1_2450_: *mut leanh::LeanObject,
    mut v_cmp_2451_: *mut leanh::LeanObject,
    mut v_inst_2452_: *mut leanh::LeanObject,
    mut v_t_2453_: *mut leanh::LeanObject,
    mut v_fallback_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2453_, v_fallback_2454_);
    return v___x_2455_;
}
pub unsafe fn l_Std_ExtTreeSet_maxD___boxed(
    mut v_00_u03b1_2456_: *mut leanh::LeanObject,
    mut v_cmp_2457_: *mut leanh::LeanObject,
    mut v_inst_2458_: *mut leanh::LeanObject,
    mut v_t_2459_: *mut leanh::LeanObject,
    mut v_fallback_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Std_ExtTreeSet_maxD(
        v_00_u03b1_2456_,
        v_cmp_2457_,
        v_inst_2458_,
        v_t_2459_,
        v_fallback_2460_,
    );
    leanh::lean_dec(v_fallback_2460_);
    leanh::lean_dec(v_t_2459_);
    leanh::lean_dec_ref(v_cmp_2457_);
    return v_res_2461_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f___redArg(
    mut v_t_2462_: *mut leanh::LeanObject,
    mut v_n_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2464_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2462_, v_n_2463_);
    return v___x_2464_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f___redArg___boxed(
    mut v_t_2465_: *mut leanh::LeanObject,
    mut v_n_2466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2467_ = l_Std_ExtTreeSet_atIdx_x3f___redArg(v_t_2465_, v_n_2466_);
    leanh::lean_dec(v_t_2465_);
    return v_res_2467_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f(
    mut v_00_u03b1_2468_: *mut leanh::LeanObject,
    mut v_cmp_2469_: *mut leanh::LeanObject,
    mut v_inst_2470_: *mut leanh::LeanObject,
    mut v_t_2471_: *mut leanh::LeanObject,
    mut v_n_2472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2471_, v_n_2472_);
    return v___x_2473_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x3f___boxed(
    mut v_00_u03b1_2474_: *mut leanh::LeanObject,
    mut v_cmp_2475_: *mut leanh::LeanObject,
    mut v_inst_2476_: *mut leanh::LeanObject,
    mut v_t_2477_: *mut leanh::LeanObject,
    mut v_n_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_Std_ExtTreeSet_atIdx_x3f(
        v_00_u03b1_2474_,
        v_cmp_2475_,
        v_inst_2476_,
        v_t_2477_,
        v_n_2478_,
    );
    leanh::lean_dec(v_t_2477_);
    leanh::lean_dec_ref(v_cmp_2475_);
    return v_res_2479_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx___redArg(
    mut v_t_2480_: *mut leanh::LeanObject,
    mut v_n_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2480_, v_n_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx___redArg___boxed(
    mut v_t_2483_: *mut leanh::LeanObject,
    mut v_n_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2485_ = l_Std_ExtTreeSet_atIdx___redArg(v_t_2483_, v_n_2484_);
    leanh::lean_dec(v_t_2483_);
    return v_res_2485_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx(
    mut v_00_u03b1_2486_: *mut leanh::LeanObject,
    mut v_cmp_2487_: *mut leanh::LeanObject,
    mut v_inst_2488_: *mut leanh::LeanObject,
    mut v_t_2489_: *mut leanh::LeanObject,
    mut v_n_2490_: *mut leanh::LeanObject,
    mut v_h_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2489_, v_n_2490_);
    return v___x_2492_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx___boxed(
    mut v_00_u03b1_2493_: *mut leanh::LeanObject,
    mut v_cmp_2494_: *mut leanh::LeanObject,
    mut v_inst_2495_: *mut leanh::LeanObject,
    mut v_t_2496_: *mut leanh::LeanObject,
    mut v_n_2497_: *mut leanh::LeanObject,
    mut v_h_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2499_ = l_Std_ExtTreeSet_atIdx(
        v_00_u03b1_2493_,
        v_cmp_2494_,
        v_inst_2495_,
        v_t_2496_,
        v_n_2497_,
        v_h_2498_,
    );
    leanh::lean_dec(v_t_2496_);
    leanh::lean_dec_ref(v_cmp_2494_);
    return v_res_2499_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21___redArg(
    mut v_inst_2500_: *mut leanh::LeanObject,
    mut v_t_2501_: *mut leanh::LeanObject,
    mut v_n_2502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2500_, v_t_2501_, v_n_2502_);
    return v___x_2503_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21___redArg___boxed(
    mut v_inst_2504_: *mut leanh::LeanObject,
    mut v_t_2505_: *mut leanh::LeanObject,
    mut v_n_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2507_ = l_Std_ExtTreeSet_atIdx_x21___redArg(v_inst_2504_, v_t_2505_, v_n_2506_);
    leanh::lean_dec(v_t_2505_);
    leanh::lean_dec(v_inst_2504_);
    return v_res_2507_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21(
    mut v_00_u03b1_2508_: *mut leanh::LeanObject,
    mut v_cmp_2509_: *mut leanh::LeanObject,
    mut v_inst_2510_: *mut leanh::LeanObject,
    mut v_inst_2511_: *mut leanh::LeanObject,
    mut v_t_2512_: *mut leanh::LeanObject,
    mut v_n_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2514_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2511_, v_t_2512_, v_n_2513_);
    return v___x_2514_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdx_x21___boxed(
    mut v_00_u03b1_2515_: *mut leanh::LeanObject,
    mut v_cmp_2516_: *mut leanh::LeanObject,
    mut v_inst_2517_: *mut leanh::LeanObject,
    mut v_inst_2518_: *mut leanh::LeanObject,
    mut v_t_2519_: *mut leanh::LeanObject,
    mut v_n_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Std_ExtTreeSet_atIdx_x21(
        v_00_u03b1_2515_,
        v_cmp_2516_,
        v_inst_2517_,
        v_inst_2518_,
        v_t_2519_,
        v_n_2520_,
    );
    leanh::lean_dec(v_t_2519_);
    leanh::lean_dec(v_inst_2518_);
    leanh::lean_dec_ref(v_cmp_2516_);
    return v_res_2521_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD___redArg(
    mut v_t_2522_: *mut leanh::LeanObject,
    mut v_n_2523_: *mut leanh::LeanObject,
    mut v_fallback_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2522_, v_n_2523_, v_fallback_2524_);
    return v___x_2525_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD___redArg___boxed(
    mut v_t_2526_: *mut leanh::LeanObject,
    mut v_n_2527_: *mut leanh::LeanObject,
    mut v_fallback_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_ExtTreeSet_atIdxD___redArg(v_t_2526_, v_n_2527_, v_fallback_2528_);
    leanh::lean_dec(v_fallback_2528_);
    leanh::lean_dec(v_t_2526_);
    return v_res_2529_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD(
    mut v_00_u03b1_2530_: *mut leanh::LeanObject,
    mut v_cmp_2531_: *mut leanh::LeanObject,
    mut v_inst_2532_: *mut leanh::LeanObject,
    mut v_t_2533_: *mut leanh::LeanObject,
    mut v_n_2534_: *mut leanh::LeanObject,
    mut v_fallback_2535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2536_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2533_, v_n_2534_, v_fallback_2535_);
    return v___x_2536_;
}
pub unsafe fn l_Std_ExtTreeSet_atIdxD___boxed(
    mut v_00_u03b1_2537_: *mut leanh::LeanObject,
    mut v_cmp_2538_: *mut leanh::LeanObject,
    mut v_inst_2539_: *mut leanh::LeanObject,
    mut v_t_2540_: *mut leanh::LeanObject,
    mut v_n_2541_: *mut leanh::LeanObject,
    mut v_fallback_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2543_ = l_Std_ExtTreeSet_atIdxD(
        v_00_u03b1_2537_,
        v_cmp_2538_,
        v_inst_2539_,
        v_t_2540_,
        v_n_2541_,
        v_fallback_2542_,
    );
    leanh::lean_dec(v_fallback_2542_);
    leanh::lean_dec(v_t_2540_);
    leanh::lean_dec_ref(v_cmp_2538_);
    return v_res_2543_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x3f___redArg(
    mut v_cmp_2544_: *mut leanh::LeanObject,
    mut v_t_2545_: *mut leanh::LeanObject,
    mut v_k_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = leanh::lean_box(0);
    v___x_2548_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2544_,
        v_k_2546_,
        v___x_2547_,
        v_t_2545_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x3f(
    mut v_00_u03b1_2549_: *mut leanh::LeanObject,
    mut v_cmp_2550_: *mut leanh::LeanObject,
    mut v_inst_2551_: *mut leanh::LeanObject,
    mut v_t_2552_: *mut leanh::LeanObject,
    mut v_k_2553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = leanh::lean_box(0);
    v___x_2555_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2550_,
        v_k_2553_,
        v___x_2554_,
        v_t_2552_,
    );
    return v___x_2555_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x3f___redArg(
    mut v_cmp_2556_: *mut leanh::LeanObject,
    mut v_t_2557_: *mut leanh::LeanObject,
    mut v_k_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2559_ = leanh::lean_box(0);
    v___x_2560_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2556_,
        v_k_2558_,
        v___x_2559_,
        v_t_2557_,
    );
    return v___x_2560_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x3f(
    mut v_00_u03b1_2561_: *mut leanh::LeanObject,
    mut v_cmp_2562_: *mut leanh::LeanObject,
    mut v_inst_2563_: *mut leanh::LeanObject,
    mut v_t_2564_: *mut leanh::LeanObject,
    mut v_k_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = leanh::lean_box(0);
    v___x_2567_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2562_,
        v_k_2565_,
        v___x_2566_,
        v_t_2564_,
    );
    return v___x_2567_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x3f___redArg(
    mut v_cmp_2568_: *mut leanh::LeanObject,
    mut v_t_2569_: *mut leanh::LeanObject,
    mut v_k_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2571_ = leanh::lean_box(0);
    v___x_2572_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2568_,
        v_k_2570_,
        v___x_2571_,
        v_t_2569_,
    );
    return v___x_2572_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x3f(
    mut v_00_u03b1_2573_: *mut leanh::LeanObject,
    mut v_cmp_2574_: *mut leanh::LeanObject,
    mut v_inst_2575_: *mut leanh::LeanObject,
    mut v_t_2576_: *mut leanh::LeanObject,
    mut v_k_2577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = leanh::lean_box(0);
    v___x_2579_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2574_,
        v_k_2577_,
        v___x_2578_,
        v_t_2576_,
    );
    return v___x_2579_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x3f___redArg(
    mut v_cmp_2580_: *mut leanh::LeanObject,
    mut v_t_2581_: *mut leanh::LeanObject,
    mut v_k_2582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2583_ = leanh::lean_box(0);
    v___x_2584_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2580_,
        v_k_2582_,
        v___x_2583_,
        v_t_2581_,
    );
    return v___x_2584_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x3f(
    mut v_00_u03b1_2585_: *mut leanh::LeanObject,
    mut v_cmp_2586_: *mut leanh::LeanObject,
    mut v_inst_2587_: *mut leanh::LeanObject,
    mut v_t_2588_: *mut leanh::LeanObject,
    mut v_k_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = leanh::lean_box(0);
    v___x_2591_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2586_,
        v_k_2589_,
        v___x_2590_,
        v_t_2588_,
    );
    return v___x_2591_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE___redArg(
    mut v_cmp_2592_: *mut leanh::LeanObject,
    mut v_t_2593_: *mut leanh::LeanObject,
    mut v_k_2594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2595_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_2592_, v_k_2594_, v_t_2593_);
    return v___x_2595_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE(
    mut v_00_u03b1_2596_: *mut leanh::LeanObject,
    mut v_cmp_2597_: *mut leanh::LeanObject,
    mut v_inst_2598_: *mut leanh::LeanObject,
    mut v_t_2599_: *mut leanh::LeanObject,
    mut v_k_2600_: *mut leanh::LeanObject,
    mut v_h_2601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_2597_, v_k_2600_, v_t_2599_);
    return v___x_2602_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT___redArg(
    mut v_cmp_2603_: *mut leanh::LeanObject,
    mut v_t_2604_: *mut leanh::LeanObject,
    mut v_k_2605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2606_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_2603_, v_k_2605_, v_t_2604_);
    return v___x_2606_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT(
    mut v_00_u03b1_2607_: *mut leanh::LeanObject,
    mut v_cmp_2608_: *mut leanh::LeanObject,
    mut v_inst_2609_: *mut leanh::LeanObject,
    mut v_t_2610_: *mut leanh::LeanObject,
    mut v_k_2611_: *mut leanh::LeanObject,
    mut v_h_2612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_2608_, v_k_2611_, v_t_2610_);
    return v___x_2613_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE___redArg(
    mut v_cmp_2614_: *mut leanh::LeanObject,
    mut v_t_2615_: *mut leanh::LeanObject,
    mut v_k_2616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2617_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_2614_, v_k_2616_, v_t_2615_);
    return v___x_2617_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE(
    mut v_00_u03b1_2618_: *mut leanh::LeanObject,
    mut v_cmp_2619_: *mut leanh::LeanObject,
    mut v_inst_2620_: *mut leanh::LeanObject,
    mut v_t_2621_: *mut leanh::LeanObject,
    mut v_k_2622_: *mut leanh::LeanObject,
    mut v_h_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_2619_, v_k_2622_, v_t_2621_);
    return v___x_2624_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT___redArg(
    mut v_cmp_2625_: *mut leanh::LeanObject,
    mut v_t_2626_: *mut leanh::LeanObject,
    mut v_k_2627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2628_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_2625_, v_k_2627_, v_t_2626_);
    return v___x_2628_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT(
    mut v_00_u03b1_2629_: *mut leanh::LeanObject,
    mut v_cmp_2630_: *mut leanh::LeanObject,
    mut v_inst_2631_: *mut leanh::LeanObject,
    mut v_t_2632_: *mut leanh::LeanObject,
    mut v_k_2633_: *mut leanh::LeanObject,
    mut v_h_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2635_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_2630_, v_k_2633_, v_t_2632_);
    return v___x_2635_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Std_ExtTreeSet_getGE_x21___redArg___closed__2;
    v___x_2640_ = leanh::lean_unsigned_to_nat(14);
    v___x_2641_ = leanh::lean_unsigned_to_nat(22);
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
    mut v_cmp_2645_: *mut leanh::LeanObject,
    mut v_inst_2646_: *mut leanh::LeanObject,
    mut v_t_2647_: *mut leanh::LeanObject,
    mut v_k_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2649_ = leanh::lean_box(0);
    v___x_2650_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2645_,
        v_k_2648_,
        v___x_2649_,
        v_t_2647_,
    );
    if leanh::lean_obj_tag(v___x_2650_) == 0 {
        let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2651_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2652_ = l_panic___redArg(v_inst_2646_, v___x_2651_);
        return v___x_2652_;
    } else {
        let mut v_val_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2653_ = leanh::lean_ctor_get(v___x_2650_, 0);
        leanh::lean_inc(v_val_2653_);
        leanh::lean_dec_ref_known(v___x_2650_, 1);
        return v_val_2653_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x21___redArg___boxed(
    mut v_cmp_2654_: *mut leanh::LeanObject,
    mut v_inst_2655_: *mut leanh::LeanObject,
    mut v_t_2656_: *mut leanh::LeanObject,
    mut v_k_2657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2658_ =
        l_Std_ExtTreeSet_getGE_x21___redArg(v_cmp_2654_, v_inst_2655_, v_t_2656_, v_k_2657_);
    leanh::lean_dec(v_inst_2655_);
    return v_res_2658_;
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x21(
    mut v_00_u03b1_2659_: *mut leanh::LeanObject,
    mut v_cmp_2660_: *mut leanh::LeanObject,
    mut v_inst_2661_: *mut leanh::LeanObject,
    mut v_inst_2662_: *mut leanh::LeanObject,
    mut v_t_2663_: *mut leanh::LeanObject,
    mut v_k_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = leanh::lean_box(0);
    v___x_2666_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2660_,
        v_k_2664_,
        v___x_2665_,
        v_t_2663_,
    );
    if leanh::lean_obj_tag(v___x_2666_) == 0 {
        let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2667_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2668_ = l_panic___redArg(v_inst_2662_, v___x_2667_);
        return v___x_2668_;
    } else {
        let mut v_val_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2669_ = leanh::lean_ctor_get(v___x_2666_, 0);
        leanh::lean_inc(v_val_2669_);
        leanh::lean_dec_ref_known(v___x_2666_, 1);
        return v_val_2669_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGE_x21___boxed(
    mut v_00_u03b1_2670_: *mut leanh::LeanObject,
    mut v_cmp_2671_: *mut leanh::LeanObject,
    mut v_inst_2672_: *mut leanh::LeanObject,
    mut v_inst_2673_: *mut leanh::LeanObject,
    mut v_t_2674_: *mut leanh::LeanObject,
    mut v_k_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Std_ExtTreeSet_getGE_x21(
        v_00_u03b1_2670_,
        v_cmp_2671_,
        v_inst_2672_,
        v_inst_2673_,
        v_t_2674_,
        v_k_2675_,
    );
    leanh::lean_dec(v_inst_2673_);
    return v_res_2676_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21___redArg(
    mut v_cmp_2677_: *mut leanh::LeanObject,
    mut v_inst_2678_: *mut leanh::LeanObject,
    mut v_t_2679_: *mut leanh::LeanObject,
    mut v_k_2680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = leanh::lean_box(0);
    v___x_2682_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2677_,
        v_k_2680_,
        v___x_2681_,
        v_t_2679_,
    );
    if leanh::lean_obj_tag(v___x_2682_) == 0 {
        let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2683_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2684_ = l_panic___redArg(v_inst_2678_, v___x_2683_);
        return v___x_2684_;
    } else {
        let mut v_val_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2685_ = leanh::lean_ctor_get(v___x_2682_, 0);
        leanh::lean_inc(v_val_2685_);
        leanh::lean_dec_ref_known(v___x_2682_, 1);
        return v_val_2685_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21___redArg___boxed(
    mut v_cmp_2686_: *mut leanh::LeanObject,
    mut v_inst_2687_: *mut leanh::LeanObject,
    mut v_t_2688_: *mut leanh::LeanObject,
    mut v_k_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ =
        l_Std_ExtTreeSet_getGT_x21___redArg(v_cmp_2686_, v_inst_2687_, v_t_2688_, v_k_2689_);
    leanh::lean_dec(v_inst_2687_);
    return v_res_2690_;
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21(
    mut v_00_u03b1_2691_: *mut leanh::LeanObject,
    mut v_cmp_2692_: *mut leanh::LeanObject,
    mut v_inst_2693_: *mut leanh::LeanObject,
    mut v_inst_2694_: *mut leanh::LeanObject,
    mut v_t_2695_: *mut leanh::LeanObject,
    mut v_k_2696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2697_ = leanh::lean_box(0);
    v___x_2698_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2692_,
        v_k_2696_,
        v___x_2697_,
        v_t_2695_,
    );
    if leanh::lean_obj_tag(v___x_2698_) == 0 {
        let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2699_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2700_ = l_panic___redArg(v_inst_2694_, v___x_2699_);
        return v___x_2700_;
    } else {
        let mut v_val_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2701_ = leanh::lean_ctor_get(v___x_2698_, 0);
        leanh::lean_inc(v_val_2701_);
        leanh::lean_dec_ref_known(v___x_2698_, 1);
        return v_val_2701_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGT_x21___boxed(
    mut v_00_u03b1_2702_: *mut leanh::LeanObject,
    mut v_cmp_2703_: *mut leanh::LeanObject,
    mut v_inst_2704_: *mut leanh::LeanObject,
    mut v_inst_2705_: *mut leanh::LeanObject,
    mut v_t_2706_: *mut leanh::LeanObject,
    mut v_k_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_Std_ExtTreeSet_getGT_x21(
        v_00_u03b1_2702_,
        v_cmp_2703_,
        v_inst_2704_,
        v_inst_2705_,
        v_t_2706_,
        v_k_2707_,
    );
    leanh::lean_dec(v_inst_2705_);
    return v_res_2708_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21___redArg(
    mut v_cmp_2709_: *mut leanh::LeanObject,
    mut v_inst_2710_: *mut leanh::LeanObject,
    mut v_t_2711_: *mut leanh::LeanObject,
    mut v_k_2712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2713_ = leanh::lean_box(0);
    v___x_2714_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2709_,
        v_k_2712_,
        v___x_2713_,
        v_t_2711_,
    );
    if leanh::lean_obj_tag(v___x_2714_) == 0 {
        let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2715_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2716_ = l_panic___redArg(v_inst_2710_, v___x_2715_);
        return v___x_2716_;
    } else {
        let mut v_val_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2717_ = leanh::lean_ctor_get(v___x_2714_, 0);
        leanh::lean_inc(v_val_2717_);
        leanh::lean_dec_ref_known(v___x_2714_, 1);
        return v_val_2717_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21___redArg___boxed(
    mut v_cmp_2718_: *mut leanh::LeanObject,
    mut v_inst_2719_: *mut leanh::LeanObject,
    mut v_t_2720_: *mut leanh::LeanObject,
    mut v_k_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ =
        l_Std_ExtTreeSet_getLE_x21___redArg(v_cmp_2718_, v_inst_2719_, v_t_2720_, v_k_2721_);
    leanh::lean_dec(v_inst_2719_);
    return v_res_2722_;
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21(
    mut v_00_u03b1_2723_: *mut leanh::LeanObject,
    mut v_cmp_2724_: *mut leanh::LeanObject,
    mut v_inst_2725_: *mut leanh::LeanObject,
    mut v_inst_2726_: *mut leanh::LeanObject,
    mut v_t_2727_: *mut leanh::LeanObject,
    mut v_k_2728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2729_ = leanh::lean_box(0);
    v___x_2730_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2724_,
        v_k_2728_,
        v___x_2729_,
        v_t_2727_,
    );
    if leanh::lean_obj_tag(v___x_2730_) == 0 {
        let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2731_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2732_ = l_panic___redArg(v_inst_2726_, v___x_2731_);
        return v___x_2732_;
    } else {
        let mut v_val_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2733_ = leanh::lean_ctor_get(v___x_2730_, 0);
        leanh::lean_inc(v_val_2733_);
        leanh::lean_dec_ref_known(v___x_2730_, 1);
        return v_val_2733_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLE_x21___boxed(
    mut v_00_u03b1_2734_: *mut leanh::LeanObject,
    mut v_cmp_2735_: *mut leanh::LeanObject,
    mut v_inst_2736_: *mut leanh::LeanObject,
    mut v_inst_2737_: *mut leanh::LeanObject,
    mut v_t_2738_: *mut leanh::LeanObject,
    mut v_k_2739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2740_ = l_Std_ExtTreeSet_getLE_x21(
        v_00_u03b1_2734_,
        v_cmp_2735_,
        v_inst_2736_,
        v_inst_2737_,
        v_t_2738_,
        v_k_2739_,
    );
    leanh::lean_dec(v_inst_2737_);
    return v_res_2740_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21___redArg(
    mut v_cmp_2741_: *mut leanh::LeanObject,
    mut v_inst_2742_: *mut leanh::LeanObject,
    mut v_t_2743_: *mut leanh::LeanObject,
    mut v_k_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = leanh::lean_box(0);
    v___x_2746_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2741_,
        v_k_2744_,
        v___x_2745_,
        v_t_2743_,
    );
    if leanh::lean_obj_tag(v___x_2746_) == 0 {
        let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2747_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2748_ = l_panic___redArg(v_inst_2742_, v___x_2747_);
        return v___x_2748_;
    } else {
        let mut v_val_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2749_ = leanh::lean_ctor_get(v___x_2746_, 0);
        leanh::lean_inc(v_val_2749_);
        leanh::lean_dec_ref_known(v___x_2746_, 1);
        return v_val_2749_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21___redArg___boxed(
    mut v_cmp_2750_: *mut leanh::LeanObject,
    mut v_inst_2751_: *mut leanh::LeanObject,
    mut v_t_2752_: *mut leanh::LeanObject,
    mut v_k_2753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2754_ =
        l_Std_ExtTreeSet_getLT_x21___redArg(v_cmp_2750_, v_inst_2751_, v_t_2752_, v_k_2753_);
    leanh::lean_dec(v_inst_2751_);
    return v_res_2754_;
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21(
    mut v_00_u03b1_2755_: *mut leanh::LeanObject,
    mut v_cmp_2756_: *mut leanh::LeanObject,
    mut v_inst_2757_: *mut leanh::LeanObject,
    mut v_inst_2758_: *mut leanh::LeanObject,
    mut v_t_2759_: *mut leanh::LeanObject,
    mut v_k_2760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = leanh::lean_box(0);
    v___x_2762_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2756_,
        v_k_2760_,
        v___x_2761_,
        v_t_2759_,
    );
    if leanh::lean_obj_tag(v___x_2762_) == 0 {
        let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2763_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2764_ = l_panic___redArg(v_inst_2758_, v___x_2763_);
        return v___x_2764_;
    } else {
        let mut v_val_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2765_ = leanh::lean_ctor_get(v___x_2762_, 0);
        leanh::lean_inc(v_val_2765_);
        leanh::lean_dec_ref_known(v___x_2762_, 1);
        return v_val_2765_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLT_x21___boxed(
    mut v_00_u03b1_2766_: *mut leanh::LeanObject,
    mut v_cmp_2767_: *mut leanh::LeanObject,
    mut v_inst_2768_: *mut leanh::LeanObject,
    mut v_inst_2769_: *mut leanh::LeanObject,
    mut v_t_2770_: *mut leanh::LeanObject,
    mut v_k_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Std_ExtTreeSet_getLT_x21(
        v_00_u03b1_2766_,
        v_cmp_2767_,
        v_inst_2768_,
        v_inst_2769_,
        v_t_2770_,
        v_k_2771_,
    );
    leanh::lean_dec(v_inst_2769_);
    return v_res_2772_;
}
pub unsafe fn l_Std_ExtTreeSet_getGED___redArg(
    mut v_cmp_2773_: *mut leanh::LeanObject,
    mut v_t_2774_: *mut leanh::LeanObject,
    mut v_k_2775_: *mut leanh::LeanObject,
    mut v_fallback_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2777_ = leanh::lean_box(0);
    v___x_2778_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2773_,
        v_k_2775_,
        v___x_2777_,
        v_t_2774_,
    );
    if leanh::lean_obj_tag(v___x_2778_) == 0 {
        leanh::lean_inc(v_fallback_2776_);
        return v_fallback_2776_;
    } else {
        let mut v_val_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2779_ = leanh::lean_ctor_get(v___x_2778_, 0);
        leanh::lean_inc(v_val_2779_);
        leanh::lean_dec_ref_known(v___x_2778_, 1);
        return v_val_2779_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGED___redArg___boxed(
    mut v_cmp_2780_: *mut leanh::LeanObject,
    mut v_t_2781_: *mut leanh::LeanObject,
    mut v_k_2782_: *mut leanh::LeanObject,
    mut v_fallback_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2784_ =
        l_Std_ExtTreeSet_getGED___redArg(v_cmp_2780_, v_t_2781_, v_k_2782_, v_fallback_2783_);
    leanh::lean_dec(v_fallback_2783_);
    return v_res_2784_;
}
pub unsafe fn l_Std_ExtTreeSet_getGED(
    mut v_00_u03b1_2785_: *mut leanh::LeanObject,
    mut v_cmp_2786_: *mut leanh::LeanObject,
    mut v_inst_2787_: *mut leanh::LeanObject,
    mut v_t_2788_: *mut leanh::LeanObject,
    mut v_k_2789_: *mut leanh::LeanObject,
    mut v_fallback_2790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = leanh::lean_box(0);
    v___x_2792_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2786_,
        v_k_2789_,
        v___x_2791_,
        v_t_2788_,
    );
    if leanh::lean_obj_tag(v___x_2792_) == 0 {
        leanh::lean_inc(v_fallback_2790_);
        return v_fallback_2790_;
    } else {
        let mut v_val_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2793_ = leanh::lean_ctor_get(v___x_2792_, 0);
        leanh::lean_inc(v_val_2793_);
        leanh::lean_dec_ref_known(v___x_2792_, 1);
        return v_val_2793_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGED___boxed(
    mut v_00_u03b1_2794_: *mut leanh::LeanObject,
    mut v_cmp_2795_: *mut leanh::LeanObject,
    mut v_inst_2796_: *mut leanh::LeanObject,
    mut v_t_2797_: *mut leanh::LeanObject,
    mut v_k_2798_: *mut leanh::LeanObject,
    mut v_fallback_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_Std_ExtTreeSet_getGED(
        v_00_u03b1_2794_,
        v_cmp_2795_,
        v_inst_2796_,
        v_t_2797_,
        v_k_2798_,
        v_fallback_2799_,
    );
    leanh::lean_dec(v_fallback_2799_);
    return v_res_2800_;
}
pub unsafe fn l_Std_ExtTreeSet_getGTD___redArg(
    mut v_cmp_2801_: *mut leanh::LeanObject,
    mut v_t_2802_: *mut leanh::LeanObject,
    mut v_k_2803_: *mut leanh::LeanObject,
    mut v_fallback_2804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2805_ = leanh::lean_box(0);
    v___x_2806_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2801_,
        v_k_2803_,
        v___x_2805_,
        v_t_2802_,
    );
    if leanh::lean_obj_tag(v___x_2806_) == 0 {
        leanh::lean_inc(v_fallback_2804_);
        return v_fallback_2804_;
    } else {
        let mut v_val_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2807_ = leanh::lean_ctor_get(v___x_2806_, 0);
        leanh::lean_inc(v_val_2807_);
        leanh::lean_dec_ref_known(v___x_2806_, 1);
        return v_val_2807_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGTD___redArg___boxed(
    mut v_cmp_2808_: *mut leanh::LeanObject,
    mut v_t_2809_: *mut leanh::LeanObject,
    mut v_k_2810_: *mut leanh::LeanObject,
    mut v_fallback_2811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2812_ =
        l_Std_ExtTreeSet_getGTD___redArg(v_cmp_2808_, v_t_2809_, v_k_2810_, v_fallback_2811_);
    leanh::lean_dec(v_fallback_2811_);
    return v_res_2812_;
}
pub unsafe fn l_Std_ExtTreeSet_getGTD(
    mut v_00_u03b1_2813_: *mut leanh::LeanObject,
    mut v_cmp_2814_: *mut leanh::LeanObject,
    mut v_inst_2815_: *mut leanh::LeanObject,
    mut v_t_2816_: *mut leanh::LeanObject,
    mut v_k_2817_: *mut leanh::LeanObject,
    mut v_fallback_2818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = leanh::lean_box(0);
    v___x_2820_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2814_,
        v_k_2817_,
        v___x_2819_,
        v_t_2816_,
    );
    if leanh::lean_obj_tag(v___x_2820_) == 0 {
        leanh::lean_inc(v_fallback_2818_);
        return v_fallback_2818_;
    } else {
        let mut v_val_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2821_ = leanh::lean_ctor_get(v___x_2820_, 0);
        leanh::lean_inc(v_val_2821_);
        leanh::lean_dec_ref_known(v___x_2820_, 1);
        return v_val_2821_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getGTD___boxed(
    mut v_00_u03b1_2822_: *mut leanh::LeanObject,
    mut v_cmp_2823_: *mut leanh::LeanObject,
    mut v_inst_2824_: *mut leanh::LeanObject,
    mut v_t_2825_: *mut leanh::LeanObject,
    mut v_k_2826_: *mut leanh::LeanObject,
    mut v_fallback_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2828_ = l_Std_ExtTreeSet_getGTD(
        v_00_u03b1_2822_,
        v_cmp_2823_,
        v_inst_2824_,
        v_t_2825_,
        v_k_2826_,
        v_fallback_2827_,
    );
    leanh::lean_dec(v_fallback_2827_);
    return v_res_2828_;
}
pub unsafe fn l_Std_ExtTreeSet_getLED___redArg(
    mut v_cmp_2829_: *mut leanh::LeanObject,
    mut v_t_2830_: *mut leanh::LeanObject,
    mut v_k_2831_: *mut leanh::LeanObject,
    mut v_fallback_2832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2833_ = leanh::lean_box(0);
    v___x_2834_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2829_,
        v_k_2831_,
        v___x_2833_,
        v_t_2830_,
    );
    if leanh::lean_obj_tag(v___x_2834_) == 0 {
        leanh::lean_inc(v_fallback_2832_);
        return v_fallback_2832_;
    } else {
        let mut v_val_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2835_ = leanh::lean_ctor_get(v___x_2834_, 0);
        leanh::lean_inc(v_val_2835_);
        leanh::lean_dec_ref_known(v___x_2834_, 1);
        return v_val_2835_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLED___redArg___boxed(
    mut v_cmp_2836_: *mut leanh::LeanObject,
    mut v_t_2837_: *mut leanh::LeanObject,
    mut v_k_2838_: *mut leanh::LeanObject,
    mut v_fallback_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2840_ =
        l_Std_ExtTreeSet_getLED___redArg(v_cmp_2836_, v_t_2837_, v_k_2838_, v_fallback_2839_);
    leanh::lean_dec(v_fallback_2839_);
    return v_res_2840_;
}
pub unsafe fn l_Std_ExtTreeSet_getLED(
    mut v_00_u03b1_2841_: *mut leanh::LeanObject,
    mut v_cmp_2842_: *mut leanh::LeanObject,
    mut v_inst_2843_: *mut leanh::LeanObject,
    mut v_t_2844_: *mut leanh::LeanObject,
    mut v_k_2845_: *mut leanh::LeanObject,
    mut v_fallback_2846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2847_ = leanh::lean_box(0);
    v___x_2848_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2842_,
        v_k_2845_,
        v___x_2847_,
        v_t_2844_,
    );
    if leanh::lean_obj_tag(v___x_2848_) == 0 {
        leanh::lean_inc(v_fallback_2846_);
        return v_fallback_2846_;
    } else {
        let mut v_val_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2849_ = leanh::lean_ctor_get(v___x_2848_, 0);
        leanh::lean_inc(v_val_2849_);
        leanh::lean_dec_ref_known(v___x_2848_, 1);
        return v_val_2849_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLED___boxed(
    mut v_00_u03b1_2850_: *mut leanh::LeanObject,
    mut v_cmp_2851_: *mut leanh::LeanObject,
    mut v_inst_2852_: *mut leanh::LeanObject,
    mut v_t_2853_: *mut leanh::LeanObject,
    mut v_k_2854_: *mut leanh::LeanObject,
    mut v_fallback_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2856_ = l_Std_ExtTreeSet_getLED(
        v_00_u03b1_2850_,
        v_cmp_2851_,
        v_inst_2852_,
        v_t_2853_,
        v_k_2854_,
        v_fallback_2855_,
    );
    leanh::lean_dec(v_fallback_2855_);
    return v_res_2856_;
}
pub unsafe fn l_Std_ExtTreeSet_getLTD___redArg(
    mut v_cmp_2857_: *mut leanh::LeanObject,
    mut v_t_2858_: *mut leanh::LeanObject,
    mut v_k_2859_: *mut leanh::LeanObject,
    mut v_fallback_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2861_ = leanh::lean_box(0);
    v___x_2862_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2857_,
        v_k_2859_,
        v___x_2861_,
        v_t_2858_,
    );
    if leanh::lean_obj_tag(v___x_2862_) == 0 {
        leanh::lean_inc(v_fallback_2860_);
        return v_fallback_2860_;
    } else {
        let mut v_val_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2863_ = leanh::lean_ctor_get(v___x_2862_, 0);
        leanh::lean_inc(v_val_2863_);
        leanh::lean_dec_ref_known(v___x_2862_, 1);
        return v_val_2863_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLTD___redArg___boxed(
    mut v_cmp_2864_: *mut leanh::LeanObject,
    mut v_t_2865_: *mut leanh::LeanObject,
    mut v_k_2866_: *mut leanh::LeanObject,
    mut v_fallback_2867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2868_ =
        l_Std_ExtTreeSet_getLTD___redArg(v_cmp_2864_, v_t_2865_, v_k_2866_, v_fallback_2867_);
    leanh::lean_dec(v_fallback_2867_);
    return v_res_2868_;
}
pub unsafe fn l_Std_ExtTreeSet_getLTD(
    mut v_00_u03b1_2869_: *mut leanh::LeanObject,
    mut v_cmp_2870_: *mut leanh::LeanObject,
    mut v_inst_2871_: *mut leanh::LeanObject,
    mut v_t_2872_: *mut leanh::LeanObject,
    mut v_k_2873_: *mut leanh::LeanObject,
    mut v_fallback_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = leanh::lean_box(0);
    v___x_2876_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2870_,
        v_k_2873_,
        v___x_2875_,
        v_t_2872_,
    );
    if leanh::lean_obj_tag(v___x_2876_) == 0 {
        leanh::lean_inc(v_fallback_2874_);
        return v_fallback_2874_;
    } else {
        let mut v_val_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2877_ = leanh::lean_ctor_get(v___x_2876_, 0);
        leanh::lean_inc(v_val_2877_);
        leanh::lean_dec_ref_known(v___x_2876_, 1);
        return v_val_2877_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_getLTD___boxed(
    mut v_00_u03b1_2878_: *mut leanh::LeanObject,
    mut v_cmp_2879_: *mut leanh::LeanObject,
    mut v_inst_2880_: *mut leanh::LeanObject,
    mut v_t_2881_: *mut leanh::LeanObject,
    mut v_k_2882_: *mut leanh::LeanObject,
    mut v_fallback_2883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2884_ = l_Std_ExtTreeSet_getLTD(
        v_00_u03b1_2878_,
        v_cmp_2879_,
        v_inst_2880_,
        v_t_2881_,
        v_k_2882_,
        v_fallback_2883_,
    );
    leanh::lean_dec(v_fallback_2883_);
    return v_res_2884_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___redArg___lam__0(
    mut v_f_2885_: *mut leanh::LeanObject,
    mut v_a_2886_: *mut leanh::LeanObject,
    mut v_x_2887_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    v___x_2888_ = leanh::lean_apply_1(v_f_2885_, v_a_2886_);
    v___x_2889_ = (leanh::lean_unbox(v___x_2888_) as u8);
    return v___x_2889_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___redArg___lam__0___boxed(
    mut v_f_2890_: *mut leanh::LeanObject,
    mut v_a_2891_: *mut leanh::LeanObject,
    mut v_x_2892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2893_: u8 = 0;
    let mut v_r_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2893_ = l_Std_ExtTreeSet_filter___redArg___lam__0(v_f_2890_, v_a_2891_, v_x_2892_);
    v_r_2894_ = leanh::lean_box((v_res_2893_) as usize);
    return v_r_2894_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___redArg(
    mut v_f_2895_: *mut leanh::LeanObject,
    mut v_m_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2897_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2897_, 0, v_f_2895_);
    v___x_2898_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_2897_, v_m_2896_);
    return v___x_2898_;
}
pub unsafe fn l_Std_ExtTreeSet_filter(
    mut v_00_u03b1_2899_: *mut leanh::LeanObject,
    mut v_cmp_2900_: *mut leanh::LeanObject,
    mut v_f_2901_: *mut leanh::LeanObject,
    mut v_m_2902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2903_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2903_, 0, v_f_2901_);
    v___x_2904_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_2903_, v_m_2902_);
    return v___x_2904_;
}
pub unsafe fn l_Std_ExtTreeSet_filter___boxed(
    mut v_00_u03b1_2905_: *mut leanh::LeanObject,
    mut v_cmp_2906_: *mut leanh::LeanObject,
    mut v_f_2907_: *mut leanh::LeanObject,
    mut v_m_2908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2909_ = l_Std_ExtTreeSet_filter(v_00_u03b1_2905_, v_cmp_2906_, v_f_2907_, v_m_2908_);
    leanh::lean_dec_ref(v_cmp_2906_);
    return v_res_2909_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM___redArg___lam__0(
    mut v_f_2910_: *mut leanh::LeanObject,
    mut v_c_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
    mut v_x_2913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = leanh::lean_apply_2(v_f_2910_, v_c_2911_, v_a_2912_);
    return v___x_2914_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM___redArg(
    mut v_inst_2915_: *mut leanh::LeanObject,
    mut v_f_2916_: *mut leanh::LeanObject,
    mut v_init_2917_: *mut leanh::LeanObject,
    mut v_t_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2919_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2919_, 0, v_f_2916_);
    v___x_2920_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2915_,
        v___f_2919_,
        v_init_2917_,
        v_t_2918_,
    );
    return v___x_2920_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM(
    mut v_00_u03b1_2921_: *mut leanh::LeanObject,
    mut v_cmp_2922_: *mut leanh::LeanObject,
    mut v_00_u03b4_2923_: *mut leanh::LeanObject,
    mut v_m_2924_: *mut leanh::LeanObject,
    mut v_inst_2925_: *mut leanh::LeanObject,
    mut v_inst_2926_: *mut leanh::LeanObject,
    mut v_inst_2927_: *mut leanh::LeanObject,
    mut v_f_2928_: *mut leanh::LeanObject,
    mut v_init_2929_: *mut leanh::LeanObject,
    mut v_t_2930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2931_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2931_, 0, v_f_2928_);
    v___x_2932_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2925_,
        v___f_2931_,
        v_init_2929_,
        v_t_2930_,
    );
    return v___x_2932_;
}
pub unsafe fn l_Std_ExtTreeSet_foldlM___boxed(
    mut v_00_u03b1_2933_: *mut leanh::LeanObject,
    mut v_cmp_2934_: *mut leanh::LeanObject,
    mut v_00_u03b4_2935_: *mut leanh::LeanObject,
    mut v_m_2936_: *mut leanh::LeanObject,
    mut v_inst_2937_: *mut leanh::LeanObject,
    mut v_inst_2938_: *mut leanh::LeanObject,
    mut v_inst_2939_: *mut leanh::LeanObject,
    mut v_f_2940_: *mut leanh::LeanObject,
    mut v_init_2941_: *mut leanh::LeanObject,
    mut v_t_2942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_cmp_2934_);
    return v_res_2943_;
}
pub unsafe fn l_Std_ExtTreeSet_foldl___redArg(
    mut v_f_2944_: *mut leanh::LeanObject,
    mut v_init_2945_: *mut leanh::LeanObject,
    mut v_t_2946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2947_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2947_, 0, v_f_2944_);
    v___x_2948_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2947_, v_init_2945_, v_t_2946_);
    return v___x_2948_;
}
pub unsafe fn l_Std_ExtTreeSet_foldl(
    mut v_00_u03b1_2949_: *mut leanh::LeanObject,
    mut v_cmp_2950_: *mut leanh::LeanObject,
    mut v_00_u03b4_2951_: *mut leanh::LeanObject,
    mut v_inst_2952_: *mut leanh::LeanObject,
    mut v_f_2953_: *mut leanh::LeanObject,
    mut v_init_2954_: *mut leanh::LeanObject,
    mut v_t_2955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2956_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2956_, 0, v_f_2953_);
    v___x_2957_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2956_, v_init_2954_, v_t_2955_);
    return v___x_2957_;
}
pub unsafe fn l_Std_ExtTreeSet_foldl___boxed(
    mut v_00_u03b1_2958_: *mut leanh::LeanObject,
    mut v_cmp_2959_: *mut leanh::LeanObject,
    mut v_00_u03b4_2960_: *mut leanh::LeanObject,
    mut v_inst_2961_: *mut leanh::LeanObject,
    mut v_f_2962_: *mut leanh::LeanObject,
    mut v_init_2963_: *mut leanh::LeanObject,
    mut v_t_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Std_ExtTreeSet_foldl(
        v_00_u03b1_2958_,
        v_cmp_2959_,
        v_00_u03b4_2960_,
        v_inst_2961_,
        v_f_2962_,
        v_init_2963_,
        v_t_2964_,
    );
    leanh::lean_dec_ref(v_cmp_2959_);
    return v_res_2965_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM___redArg___lam__0(
    mut v_f_2966_: *mut leanh::LeanObject,
    mut v_a_2967_: *mut leanh::LeanObject,
    mut v_x_2968_: *mut leanh::LeanObject,
    mut v_acc_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2970_ = leanh::lean_apply_2(v_f_2966_, v_a_2967_, v_acc_2969_);
    return v___x_2970_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM___redArg(
    mut v_inst_2971_: *mut leanh::LeanObject,
    mut v_f_2972_: *mut leanh::LeanObject,
    mut v_init_2973_: *mut leanh::LeanObject,
    mut v_t_2974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2975_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2975_, 0, v_f_2972_);
    v___x_2976_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2971_,
        v___f_2975_,
        v_init_2973_,
        v_t_2974_,
    );
    return v___x_2976_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM(
    mut v_00_u03b1_2977_: *mut leanh::LeanObject,
    mut v_cmp_2978_: *mut leanh::LeanObject,
    mut v_00_u03b4_2979_: *mut leanh::LeanObject,
    mut v_m_2980_: *mut leanh::LeanObject,
    mut v_inst_2981_: *mut leanh::LeanObject,
    mut v_inst_2982_: *mut leanh::LeanObject,
    mut v_inst_2983_: *mut leanh::LeanObject,
    mut v_f_2984_: *mut leanh::LeanObject,
    mut v_init_2985_: *mut leanh::LeanObject,
    mut v_t_2986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2987_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2987_, 0, v_f_2984_);
    v___x_2988_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2981_,
        v___f_2987_,
        v_init_2985_,
        v_t_2986_,
    );
    return v___x_2988_;
}
pub unsafe fn l_Std_ExtTreeSet_foldrM___boxed(
    mut v_00_u03b1_2989_: *mut leanh::LeanObject,
    mut v_cmp_2990_: *mut leanh::LeanObject,
    mut v_00_u03b4_2991_: *mut leanh::LeanObject,
    mut v_m_2992_: *mut leanh::LeanObject,
    mut v_inst_2993_: *mut leanh::LeanObject,
    mut v_inst_2994_: *mut leanh::LeanObject,
    mut v_inst_2995_: *mut leanh::LeanObject,
    mut v_f_2996_: *mut leanh::LeanObject,
    mut v_init_2997_: *mut leanh::LeanObject,
    mut v_t_2998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_cmp_2990_);
    return v_res_2999_;
}
pub unsafe fn l_Std_ExtTreeSet_foldr___redArg___lam__0(
    mut v_f_3000_: *mut leanh::LeanObject,
    mut v_x1_3001_: *mut leanh::LeanObject,
    mut v_x2_3002_: *mut leanh::LeanObject,
    mut v_x3_3003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3004_ = leanh::lean_apply_2(v_f_3000_, v_x1_3001_, v_x3_3003_);
    return v___x_3004_;
}
pub unsafe fn l_Std_ExtTreeSet_foldr___redArg(
    mut v_f_3024_: *mut leanh::LeanObject,
    mut v_init_3025_: *mut leanh::LeanObject,
    mut v_t_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3027_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3027_, 0, v_f_3024_);
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
    mut v_00_u03b1_3030_: *mut leanh::LeanObject,
    mut v_cmp_3031_: *mut leanh::LeanObject,
    mut v_00_u03b4_3032_: *mut leanh::LeanObject,
    mut v_inst_3033_: *mut leanh::LeanObject,
    mut v_f_3034_: *mut leanh::LeanObject,
    mut v_init_3035_: *mut leanh::LeanObject,
    mut v_t_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3037_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3037_, 0, v_f_3034_);
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
    mut v_00_u03b1_3040_: *mut leanh::LeanObject,
    mut v_cmp_3041_: *mut leanh::LeanObject,
    mut v_00_u03b4_3042_: *mut leanh::LeanObject,
    mut v_inst_3043_: *mut leanh::LeanObject,
    mut v_f_3044_: *mut leanh::LeanObject,
    mut v_init_3045_: *mut leanh::LeanObject,
    mut v_t_3046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3047_ = l_Std_ExtTreeSet_foldr(
        v_00_u03b1_3040_,
        v_cmp_3041_,
        v_00_u03b4_3042_,
        v_inst_3043_,
        v_f_3044_,
        v_init_3045_,
        v_t_3046_,
    );
    leanh::lean_dec_ref(v_cmp_3041_);
    return v_res_3047_;
}
pub unsafe fn l_Std_ExtTreeSet_partition___redArg___lam__0(
    mut v_f_3048_: *mut leanh::LeanObject,
    mut v_cmp_3049_: *mut leanh::LeanObject,
    mut v_x_3050_: *mut leanh::LeanObject,
    mut v_a_3051_: *mut leanh::LeanObject,
    mut v_b_3052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3057_: u8 = 0;
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3053_ = leanh::lean_ctor_get(v_x_3050_, 0);
                v_snd_3054_ = leanh::lean_ctor_get(v_x_3050_, 1);
                v_isSharedCheck_3068_ = (!leanh::lean_is_exclusive(v_x_3050_)) as u8;
                if v_isSharedCheck_3068_ == 0 {
                    v___x_3056_ = v_x_3050_;
                    v_isShared_3057_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3054_);
                    leanh::lean_inc(v_fst_3053_);
                    leanh::lean_dec(v_x_3050_);
                    v___x_3056_ = leanh::lean_box(0);
                    v_isShared_3057_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_3051_);
                v___x_3058_ = leanh::lean_apply_1(v_f_3048_, v_a_3051_);
                v___x_3059_ = (leanh::lean_unbox(v___x_3058_) as u8);
                if v___x_3059_ == 0 {
                    v___x_3060_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_3049_,
                        v_a_3051_,
                        v_b_3052_,
                        v_snd_3054_,
                    );
                    if v_isShared_3057_ == 0 {
                        leanh::lean_ctor_set(v___x_3056_, 1, v___x_3060_);
                        v___x_3062_ = v___x_3056_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_fst_3053_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3060_);
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
                        leanh::lean_ctor_set(v___x_3056_, 0, v___x_3064_);
                        v___x_3066_ = v___x_3056_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3067_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_snd_3054_);
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
    mut v_cmp_3071_: *mut leanh::LeanObject,
    mut v_f_3072_: *mut leanh::LeanObject,
    mut v_t_3073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3081_: u8 = 0;
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3074_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_3074_, 0, v_f_3072_);
                leanh::lean_closure_set(v___f_3074_, 1, v_cmp_3071_);
                v___x_3075_ = l_Std_ExtTreeSet_partition___redArg___closed__0;
                v_p_3076_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3074_,
                    v___x_3075_,
                    v_t_3073_,
                );
                v_fst_3077_ = leanh::lean_ctor_get(v_p_3076_, 0);
                v_snd_3078_ = leanh::lean_ctor_get(v_p_3076_, 1);
                v_isSharedCheck_3085_ = (!leanh::lean_is_exclusive(v_p_3076_)) as u8;
                if v_isSharedCheck_3085_ == 0 {
                    v___x_3080_ = v_p_3076_;
                    v_isShared_3081_ = v_isSharedCheck_3085_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3078_);
                    leanh::lean_inc(v_fst_3077_);
                    leanh::lean_dec(v_p_3076_);
                    v___x_3080_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_fst_3077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_snd_3078_);
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
    mut v_00_u03b1_3086_: *mut leanh::LeanObject,
    mut v_cmp_3087_: *mut leanh::LeanObject,
    mut v_inst_3088_: *mut leanh::LeanObject,
    mut v_f_3089_: *mut leanh::LeanObject,
    mut v_t_3090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3091_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_3091_, 0, v_f_3089_);
                leanh::lean_closure_set(v___f_3091_, 1, v_cmp_3087_);
                v___x_3092_ = l_Std_ExtTreeSet_partition___redArg___closed__0;
                v_p_3093_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3091_,
                    v___x_3092_,
                    v_t_3090_,
                );
                v_fst_3094_ = leanh::lean_ctor_get(v_p_3093_, 0);
                v_snd_3095_ = leanh::lean_ctor_get(v_p_3093_, 1);
                v_isSharedCheck_3102_ = (!leanh::lean_is_exclusive(v_p_3093_)) as u8;
                if v_isSharedCheck_3102_ == 0 {
                    v___x_3097_ = v_p_3093_;
                    v_isShared_3098_ = v_isSharedCheck_3102_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3095_);
                    leanh::lean_inc(v_fst_3094_);
                    leanh::lean_dec(v_p_3093_);
                    v___x_3097_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3101_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_fst_3094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_snd_3095_);
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
    mut v_f_3103_: *mut leanh::LeanObject,
    mut v_x_3104_: *mut leanh::LeanObject,
    mut v_k_3105_: *mut leanh::LeanObject,
    mut v_v_3106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3107_ = leanh::lean_apply_1(v_f_3103_, v_k_3105_);
    return v___x_3107_;
}
pub unsafe fn l_Std_ExtTreeSet_forM___redArg(
    mut v_inst_3108_: *mut leanh::LeanObject,
    mut v_f_3109_: *mut leanh::LeanObject,
    mut v_t_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3111_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3111_, 0, v_f_3109_);
    v___x_3112_ = leanh::lean_box(0);
    v___x_3113_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3108_,
        v___f_3111_,
        v___x_3112_,
        v_t_3110_,
    );
    return v___x_3113_;
}
pub unsafe fn l_Std_ExtTreeSet_forM(
    mut v_00_u03b1_3114_: *mut leanh::LeanObject,
    mut v_cmp_3115_: *mut leanh::LeanObject,
    mut v_m_3116_: *mut leanh::LeanObject,
    mut v_inst_3117_: *mut leanh::LeanObject,
    mut v_inst_3118_: *mut leanh::LeanObject,
    mut v_inst_3119_: *mut leanh::LeanObject,
    mut v_f_3120_: *mut leanh::LeanObject,
    mut v_t_3121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3122_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3122_, 0, v_f_3120_);
    v___x_3123_ = leanh::lean_box(0);
    v___x_3124_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3117_,
        v___f_3122_,
        v___x_3123_,
        v_t_3121_,
    );
    return v___x_3124_;
}
pub unsafe fn l_Std_ExtTreeSet_forM___boxed(
    mut v_00_u03b1_3125_: *mut leanh::LeanObject,
    mut v_cmp_3126_: *mut leanh::LeanObject,
    mut v_m_3127_: *mut leanh::LeanObject,
    mut v_inst_3128_: *mut leanh::LeanObject,
    mut v_inst_3129_: *mut leanh::LeanObject,
    mut v_inst_3130_: *mut leanh::LeanObject,
    mut v_f_3131_: *mut leanh::LeanObject,
    mut v_t_3132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_cmp_3126_);
    return v_res_3133_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___redArg___lam__0(
    mut v_f_3134_: *mut leanh::LeanObject,
    mut v_a_3135_: *mut leanh::LeanObject,
    mut v_b_3136_: *mut leanh::LeanObject,
    mut v_c_3137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ = leanh::lean_apply_2(v_f_3134_, v_a_3135_, v_c_3137_);
    return v___x_3138_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___redArg___lam__1(
    mut v_toPure_3139_: *mut leanh::LeanObject,
    mut v_____do__lift_3140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_3141_ = leanh::lean_ctor_get(v_____do__lift_3140_, 0);
    leanh::lean_inc(v_a_3141_);
    leanh::lean_dec_ref(v_____do__lift_3140_);
    v___x_3142_ = leanh::lean_apply_2(v_toPure_3139_, leanh::lean_box(0), v_a_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___redArg(
    mut v_inst_3143_: *mut leanh::LeanObject,
    mut v_f_3144_: *mut leanh::LeanObject,
    mut v_init_3145_: *mut leanh::LeanObject,
    mut v_t_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3147_ = leanh::lean_ctor_get(v_inst_3143_, 0);
    v_toBind_3148_ = leanh::lean_ctor_get(v_inst_3143_, 1);
    leanh::lean_inc(v_toBind_3148_);
    v_toPure_3149_ = leanh::lean_ctor_get(v_toApplicative_3147_, 1);
    leanh::lean_inc(v_toPure_3149_);
    v___f_3150_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3150_, 0, v_f_3144_);
    v___x_3151_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3143_,
        v___f_3150_,
        v_init_3145_,
        v_t_3146_,
    );
    v___f_3152_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3152_, 0, v_toPure_3149_);
    v___x_3153_ = leanh::lean_apply_4(
        v_toBind_3148_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3151_,
        v___f_3152_,
    );
    return v___x_3153_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn(
    mut v_00_u03b1_3154_: *mut leanh::LeanObject,
    mut v_cmp_3155_: *mut leanh::LeanObject,
    mut v_00_u03b4_3156_: *mut leanh::LeanObject,
    mut v_m_3157_: *mut leanh::LeanObject,
    mut v_inst_3158_: *mut leanh::LeanObject,
    mut v_inst_3159_: *mut leanh::LeanObject,
    mut v_inst_3160_: *mut leanh::LeanObject,
    mut v_f_3161_: *mut leanh::LeanObject,
    mut v_init_3162_: *mut leanh::LeanObject,
    mut v_t_3163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3164_ = leanh::lean_ctor_get(v_inst_3158_, 0);
    v_toBind_3165_ = leanh::lean_ctor_get(v_inst_3158_, 1);
    leanh::lean_inc(v_toBind_3165_);
    v_toPure_3166_ = leanh::lean_ctor_get(v_toApplicative_3164_, 1);
    leanh::lean_inc(v_toPure_3166_);
    v___f_3167_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3167_, 0, v_f_3161_);
    v___x_3168_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3158_,
        v___f_3167_,
        v_init_3162_,
        v_t_3163_,
    );
    v___f_3169_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3169_, 0, v_toPure_3166_);
    v___x_3170_ = leanh::lean_apply_4(
        v_toBind_3165_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3168_,
        v___f_3169_,
    );
    return v___x_3170_;
}
pub unsafe fn l_Std_ExtTreeSet_forIn___boxed(
    mut v_00_u03b1_3171_: *mut leanh::LeanObject,
    mut v_cmp_3172_: *mut leanh::LeanObject,
    mut v_00_u03b4_3173_: *mut leanh::LeanObject,
    mut v_m_3174_: *mut leanh::LeanObject,
    mut v_inst_3175_: *mut leanh::LeanObject,
    mut v_inst_3176_: *mut leanh::LeanObject,
    mut v_inst_3177_: *mut leanh::LeanObject,
    mut v_f_3178_: *mut leanh::LeanObject,
    mut v_init_3179_: *mut leanh::LeanObject,
    mut v_t_3180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_cmp_3172_);
    return v_res_3181_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1(
    mut v_inst_3182_: *mut leanh::LeanObject,
    mut v_t_3183_: *mut leanh::LeanObject,
    mut v_f_3184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3185_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3185_, 0, v_f_3184_);
    v___x_3186_ = leanh::lean_box(0);
    v___x_3187_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3182_,
        v___f_3185_,
        v___x_3186_,
        v_t_3183_,
    );
    return v___x_3187_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_3188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3189_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3189_, 0, v_inst_3188_);
    return v___f_3189_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_3190_: *mut leanh::LeanObject,
    mut v_cmp_3191_: *mut leanh::LeanObject,
    mut v_m_3192_: *mut leanh::LeanObject,
    mut v_inst_3193_: *mut leanh::LeanObject,
    mut v_inst_3194_: *mut leanh::LeanObject,
    mut v_inst_3195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3196_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3196_, 0, v_inst_3194_);
    return v___f_3196_;
}
pub unsafe fn l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_3197_: *mut leanh::LeanObject,
    mut v_cmp_3198_: *mut leanh::LeanObject,
    mut v_m_3199_: *mut leanh::LeanObject,
    mut v_inst_3200_: *mut leanh::LeanObject,
    mut v_inst_3201_: *mut leanh::LeanObject,
    mut v_inst_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3203_ = l_Std_ExtTreeSet_instForMOfTransCmpOfLawfulMonad(
        v_00_u03b1_3197_,
        v_cmp_3198_,
        v_m_3199_,
        v_inst_3200_,
        v_inst_3201_,
        v_inst_3202_,
    );
    leanh::lean_dec_ref(v_cmp_3198_);
    return v_res_3203_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2(
    mut v_inst_3204_: *mut leanh::LeanObject,
    mut v_00_u03b2_3205_: *mut leanh::LeanObject,
    mut v_m_3206_: *mut leanh::LeanObject,
    mut v_init_3207_: *mut leanh::LeanObject,
    mut v_f_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3209_ = leanh::lean_ctor_get(v_inst_3204_, 0);
    v_toBind_3210_ = leanh::lean_ctor_get(v_inst_3204_, 1);
    leanh::lean_inc(v_toBind_3210_);
    v_toPure_3211_ = leanh::lean_ctor_get(v_toApplicative_3209_, 1);
    leanh::lean_inc(v_toPure_3211_);
    v___f_3212_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3212_, 0, v_f_3208_);
    v___x_3213_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3204_,
        v___f_3212_,
        v_init_3207_,
        v_m_3206_,
    );
    v___f_3214_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3214_, 0, v_toPure_3211_);
    v___x_3215_ = leanh::lean_apply_4(
        v_toBind_3210_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3213_,
        v___f_3214_,
    );
    return v___x_3215_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3217_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3217_, 0, v_inst_3216_);
    return v___f_3217_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_3218_: *mut leanh::LeanObject,
    mut v_cmp_3219_: *mut leanh::LeanObject,
    mut v_m_3220_: *mut leanh::LeanObject,
    mut v_inst_3221_: *mut leanh::LeanObject,
    mut v_inst_3222_: *mut leanh::LeanObject,
    mut v_inst_3223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3224_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3224_, 0, v_inst_3222_);
    return v___f_3224_;
}
pub unsafe fn l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_3225_: *mut leanh::LeanObject,
    mut v_cmp_3226_: *mut leanh::LeanObject,
    mut v_m_3227_: *mut leanh::LeanObject,
    mut v_inst_3228_: *mut leanh::LeanObject,
    mut v_inst_3229_: *mut leanh::LeanObject,
    mut v_inst_3230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3231_ = l_Std_ExtTreeSet_instForInOfTransCmpOfLawfulMonad(
        v_00_u03b1_3225_,
        v_cmp_3226_,
        v_m_3227_,
        v_inst_3228_,
        v_inst_3229_,
        v_inst_3230_,
    );
    leanh::lean_dec_ref(v_cmp_3226_);
    return v_res_3231_;
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg___lam__0(
    mut v_p_3232_: *mut leanh::LeanObject,
    mut v___x_3233_: *mut leanh::LeanObject,
    mut v___x_3234_: *mut leanh::LeanObject,
    mut v_a_3235_: *mut leanh::LeanObject,
    mut v_b_3236_: *mut leanh::LeanObject,
    mut v_acc_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    v___x_3238_ = leanh::lean_apply_1(v_p_3232_, v_a_3235_);
    v___x_3239_ = (leanh::lean_unbox(v___x_3238_) as u8);
    if v___x_3239_ == 0 {
        let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3240_, 0, v___x_3233_);
        return v___x_3240_;
    } else {
        let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_3233_);
        v___x_3241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3241_, 0, v___x_3238_);
        v___x_3242_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3242_, 0, v___x_3241_);
        leanh::lean_ctor_set(v___x_3242_, 1, v___x_3234_);
        v___x_3243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3243_, 0, v___x_3242_);
        return v___x_3243_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg___lam__0___boxed(
    mut v_p_3244_: *mut leanh::LeanObject,
    mut v___x_3245_: *mut leanh::LeanObject,
    mut v___x_3246_: *mut leanh::LeanObject,
    mut v_a_3247_: *mut leanh::LeanObject,
    mut v_b_3248_: *mut leanh::LeanObject,
    mut v_acc_3249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3250_ = l_Std_ExtTreeSet_any___redArg___lam__0(
        v_p_3244_,
        v___x_3245_,
        v___x_3246_,
        v_a_3247_,
        v_b_3248_,
        v_acc_3249_,
    );
    leanh::lean_dec_ref(v_acc_3249_);
    return v_res_3250_;
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg(
    mut v_t_3254_: *mut leanh::LeanObject,
    mut v_p_3255_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: u8 = 0;
    let mut v_val_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3262_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3263_ = leanh::lean_box(0);
                v___x_3264_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3265_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_3265_, 0, v_p_3255_);
                leanh::lean_closure_set(v___f_3265_, 1, v___x_3264_);
                leanh::lean_closure_set(v___f_3265_, 2, v___x_3263_);
                v___x_3266_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3262_,
                    v___f_3265_,
                    v___x_3264_,
                    v_t_3254_,
                );
                v_a_3267_ = leanh::lean_ctor_get(v___x_3266_, 0);
                leanh::lean_inc(v_a_3267_);
                leanh::lean_dec(v___x_3266_);
                v___y_3257_ = v_a_3267_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3258_ = leanh::lean_ctor_get(v___y_3257_, 0);
                leanh::lean_inc(v_fst_3258_);
                leanh::lean_dec_ref(v___y_3257_);
                if leanh::lean_obj_tag(v_fst_3258_) == 0 {
                    v___x_3259_ = 0;
                    return v___x_3259_;
                } else {
                    v_val_3260_ = leanh::lean_ctor_get(v_fst_3258_, 0);
                    leanh::lean_inc(v_val_3260_);
                    leanh::lean_dec_ref_known(v_fst_3258_, 1);
                    v___x_3261_ = (leanh::lean_unbox(v_val_3260_) as u8);
                    leanh::lean_dec(v_val_3260_);
                    return v___x_3261_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_any___redArg___boxed(
    mut v_t_3268_: *mut leanh::LeanObject,
    mut v_p_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3270_: u8 = 0;
    let mut v_r_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Std_ExtTreeSet_any___redArg(v_t_3268_, v_p_3269_);
    v_r_3271_ = leanh::lean_box((v_res_3270_) as usize);
    return v_r_3271_;
}
pub unsafe fn l_Std_ExtTreeSet_any(
    mut v_00_u03b1_3272_: *mut leanh::LeanObject,
    mut v_cmp_3273_: *mut leanh::LeanObject,
    mut v_inst_3274_: *mut leanh::LeanObject,
    mut v_t_3275_: *mut leanh::LeanObject,
    mut v_p_3276_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v_val_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3283_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3284_ = leanh::lean_box(0);
                v___x_3285_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3286_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_3286_, 0, v_p_3276_);
                leanh::lean_closure_set(v___f_3286_, 1, v___x_3285_);
                leanh::lean_closure_set(v___f_3286_, 2, v___x_3284_);
                v___x_3287_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3283_,
                    v___f_3286_,
                    v___x_3285_,
                    v_t_3275_,
                );
                v_a_3288_ = leanh::lean_ctor_get(v___x_3287_, 0);
                leanh::lean_inc(v_a_3288_);
                leanh::lean_dec(v___x_3287_);
                v___y_3278_ = v_a_3288_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3279_ = leanh::lean_ctor_get(v___y_3278_, 0);
                leanh::lean_inc(v_fst_3279_);
                leanh::lean_dec_ref(v___y_3278_);
                if leanh::lean_obj_tag(v_fst_3279_) == 0 {
                    v___x_3280_ = 0;
                    return v___x_3280_;
                } else {
                    v_val_3281_ = leanh::lean_ctor_get(v_fst_3279_, 0);
                    leanh::lean_inc(v_val_3281_);
                    leanh::lean_dec_ref_known(v_fst_3279_, 1);
                    v___x_3282_ = (leanh::lean_unbox(v_val_3281_) as u8);
                    leanh::lean_dec(v_val_3281_);
                    return v___x_3282_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_any___boxed(
    mut v_00_u03b1_3289_: *mut leanh::LeanObject,
    mut v_cmp_3290_: *mut leanh::LeanObject,
    mut v_inst_3291_: *mut leanh::LeanObject,
    mut v_t_3292_: *mut leanh::LeanObject,
    mut v_p_3293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3294_: u8 = 0;
    let mut v_r_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3294_ = l_Std_ExtTreeSet_any(
        v_00_u03b1_3289_,
        v_cmp_3290_,
        v_inst_3291_,
        v_t_3292_,
        v_p_3293_,
    );
    leanh::lean_dec_ref(v_cmp_3290_);
    v_r_3295_ = leanh::lean_box((v_res_3294_) as usize);
    return v_r_3295_;
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg___lam__0(
    mut v_p_3296_: *mut leanh::LeanObject,
    mut v___x_3297_: *mut leanh::LeanObject,
    mut v___x_3298_: *mut leanh::LeanObject,
    mut v_a_3299_: *mut leanh::LeanObject,
    mut v_b_3300_: *mut leanh::LeanObject,
    mut v_acc_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: u8 = 0;
    v___x_3302_ = leanh::lean_apply_1(v_p_3296_, v_a_3299_);
    v___x_3303_ = (leanh::lean_unbox(v___x_3302_) as u8);
    if v___x_3303_ == 0 {
        let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_3298_);
        v___x_3304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3304_, 0, v___x_3302_);
        v___x_3305_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3305_, 0, v___x_3304_);
        leanh::lean_ctor_set(v___x_3305_, 1, v___x_3297_);
        v___x_3306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3306_, 0, v___x_3305_);
        return v___x_3306_;
    } else {
        let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3307_, 0, v___x_3298_);
        return v___x_3307_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg___lam__0___boxed(
    mut v_p_3308_: *mut leanh::LeanObject,
    mut v___x_3309_: *mut leanh::LeanObject,
    mut v___x_3310_: *mut leanh::LeanObject,
    mut v_a_3311_: *mut leanh::LeanObject,
    mut v_b_3312_: *mut leanh::LeanObject,
    mut v_acc_3313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_Std_ExtTreeSet_all___redArg___lam__0(
        v_p_3308_,
        v___x_3309_,
        v___x_3310_,
        v_a_3311_,
        v_b_3312_,
        v_acc_3313_,
    );
    leanh::lean_dec_ref(v_acc_3313_);
    return v_res_3314_;
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg(
    mut v_t_3315_: *mut leanh::LeanObject,
    mut v_p_3316_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v_val_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3323_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3324_ = leanh::lean_box(0);
                v___x_3325_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3326_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_3326_, 0, v_p_3316_);
                leanh::lean_closure_set(v___f_3326_, 1, v___x_3324_);
                leanh::lean_closure_set(v___f_3326_, 2, v___x_3325_);
                v___x_3327_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3323_,
                    v___f_3326_,
                    v___x_3325_,
                    v_t_3315_,
                );
                v_a_3328_ = leanh::lean_ctor_get(v___x_3327_, 0);
                leanh::lean_inc(v_a_3328_);
                leanh::lean_dec(v___x_3327_);
                v___y_3318_ = v_a_3328_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3319_ = leanh::lean_ctor_get(v___y_3318_, 0);
                leanh::lean_inc(v_fst_3319_);
                leanh::lean_dec_ref(v___y_3318_);
                if leanh::lean_obj_tag(v_fst_3319_) == 0 {
                    v___x_3320_ = 1;
                    return v___x_3320_;
                } else {
                    v_val_3321_ = leanh::lean_ctor_get(v_fst_3319_, 0);
                    leanh::lean_inc(v_val_3321_);
                    leanh::lean_dec_ref_known(v_fst_3319_, 1);
                    v___x_3322_ = (leanh::lean_unbox(v_val_3321_) as u8);
                    leanh::lean_dec(v_val_3321_);
                    return v___x_3322_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_all___redArg___boxed(
    mut v_t_3329_: *mut leanh::LeanObject,
    mut v_p_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3331_: u8 = 0;
    let mut v_r_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Std_ExtTreeSet_all___redArg(v_t_3329_, v_p_3330_);
    v_r_3332_ = leanh::lean_box((v_res_3331_) as usize);
    return v_r_3332_;
}
pub unsafe fn l_Std_ExtTreeSet_all(
    mut v_00_u03b1_3333_: *mut leanh::LeanObject,
    mut v_cmp_3334_: *mut leanh::LeanObject,
    mut v_inst_3335_: *mut leanh::LeanObject,
    mut v_t_3336_: *mut leanh::LeanObject,
    mut v_p_3337_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v_val_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3344_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
                v___x_3345_ = leanh::lean_box(0);
                v___x_3346_ = l_Std_ExtTreeSet_any___redArg___closed__0;
                v___f_3347_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_3347_, 0, v_p_3337_);
                leanh::lean_closure_set(v___f_3347_, 1, v___x_3345_);
                leanh::lean_closure_set(v___f_3347_, 2, v___x_3346_);
                v___x_3348_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3344_,
                    v___f_3347_,
                    v___x_3346_,
                    v_t_3336_,
                );
                v_a_3349_ = leanh::lean_ctor_get(v___x_3348_, 0);
                leanh::lean_inc(v_a_3349_);
                leanh::lean_dec(v___x_3348_);
                v___y_3339_ = v_a_3349_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3340_ = leanh::lean_ctor_get(v___y_3339_, 0);
                leanh::lean_inc(v_fst_3340_);
                leanh::lean_dec_ref(v___y_3339_);
                if leanh::lean_obj_tag(v_fst_3340_) == 0 {
                    v___x_3341_ = 1;
                    return v___x_3341_;
                } else {
                    v_val_3342_ = leanh::lean_ctor_get(v_fst_3340_, 0);
                    leanh::lean_inc(v_val_3342_);
                    leanh::lean_dec_ref_known(v_fst_3340_, 1);
                    v___x_3343_ = (leanh::lean_unbox(v_val_3342_) as u8);
                    leanh::lean_dec(v_val_3342_);
                    return v___x_3343_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeSet_all___boxed(
    mut v_00_u03b1_3350_: *mut leanh::LeanObject,
    mut v_cmp_3351_: *mut leanh::LeanObject,
    mut v_inst_3352_: *mut leanh::LeanObject,
    mut v_t_3353_: *mut leanh::LeanObject,
    mut v_p_3354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3355_: u8 = 0;
    let mut v_r_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Std_ExtTreeSet_all(
        v_00_u03b1_3350_,
        v_cmp_3351_,
        v_inst_3352_,
        v_t_3353_,
        v_p_3354_,
    );
    leanh::lean_dec_ref(v_cmp_3351_);
    v_r_3356_ = leanh::lean_box((v_res_3355_) as usize);
    return v_r_3356_;
}
pub unsafe fn l_Std_ExtTreeSet_toList___redArg___lam__0(
    mut v_x1_3357_: *mut leanh::LeanObject,
    mut v_x2_3358_: *mut leanh::LeanObject,
    mut v_x3_3359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3360_, 0, v_x1_3357_);
    leanh::lean_ctor_set(v___x_3360_, 1, v_x3_3359_);
    return v___x_3360_;
}
pub unsafe fn l_Std_ExtTreeSet_toList___redArg(
    mut v_t_3362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3363_ = l_Std_ExtTreeSet_toList___redArg___closed__0;
    v___x_3364_ = leanh::lean_box(0);
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
    mut v_00_u03b1_3367_: *mut leanh::LeanObject,
    mut v_cmp_3368_: *mut leanh::LeanObject,
    mut v_inst_3369_: *mut leanh::LeanObject,
    mut v_t_3370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3371_ = l_Std_ExtTreeSet_toList___redArg___closed__0;
    v___x_3372_ = leanh::lean_box(0);
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
    mut v_00_u03b1_3375_: *mut leanh::LeanObject,
    mut v_cmp_3376_: *mut leanh::LeanObject,
    mut v_inst_3377_: *mut leanh::LeanObject,
    mut v_t_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3379_ = l_Std_ExtTreeSet_toList(v_00_u03b1_3375_, v_cmp_3376_, v_inst_3377_, v_t_3378_);
    leanh::lean_dec_ref(v_cmp_3376_);
    return v_res_3379_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_ofList___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__26,
    );
    return v___x_3380_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(
    mut v_cmp_3381_: *mut leanh::LeanObject,
    mut v_k_3382_: *mut leanh::LeanObject,
    mut v_v_3383_: *mut leanh::LeanObject,
    mut v_t_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3392_: u8 = 0;
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v_impl_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: u8 = 0;
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v_size_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: u8 = 0;
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut v_unused_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_unused_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_unused_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut v_unused_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v_k_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut v_unused_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v_size_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut v_unused_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3603_: u8 = 0;
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3607_: u8 = 0;
    let mut v_unused_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut v_unused_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v_k_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3631_: u8 = 0;
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v_unused_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_unused_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_unused_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3384_) == 0 {
                    v_size_3385_ = leanh::lean_ctor_get(v_t_3384_, 0);
                    v_k_3386_ = leanh::lean_ctor_get(v_t_3384_, 1);
                    v_v_3387_ = leanh::lean_ctor_get(v_t_3384_, 2);
                    v_l_3388_ = leanh::lean_ctor_get(v_t_3384_, 3);
                    v_r_3389_ = leanh::lean_ctor_get(v_t_3384_, 4);
                    v_isSharedCheck_3670_ = (!leanh::lean_is_exclusive(v_t_3384_)) as u8;
                    if v_isSharedCheck_3670_ == 0 {
                        v___x_3391_ = v_t_3384_;
                        v_isShared_3392_ = v_isSharedCheck_3670_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_3389_);
                        leanh::lean_inc(v_l_3388_);
                        leanh::lean_inc(v_v_3387_);
                        leanh::lean_inc(v_k_3386_);
                        leanh::lean_inc(v_size_3385_);
                        leanh::lean_dec(v_t_3384_);
                        v___x_3391_ = leanh::lean_box(0);
                        v_isShared_3392_ = v_isSharedCheck_3670_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_cmp_3381_);
                    v___x_3671_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3672_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_3672_, 0, v___x_3671_);
                    leanh::lean_ctor_set(v___x_3672_, 1, v_k_3382_);
                    leanh::lean_ctor_set(v___x_3672_, 2, v_v_3383_);
                    leanh::lean_ctor_set(v___x_3672_, 3, v_t_3384_);
                    leanh::lean_ctor_set(v___x_3672_, 4, v_t_3384_);
                    return v___x_3672_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_cmp_3381_);
                leanh::lean_inc(v_k_3386_);
                leanh::lean_inc(v_k_3382_);
                v___x_3393_ = leanh::lean_apply_2(v_cmp_3381_, v_k_3382_, v_k_3386_);
                v___x_3394_ = (leanh::lean_unbox(v___x_3393_) as u8);
                match v___x_3394_ {
                    0 => {
                        leanh::lean_dec(v_size_3385_);
                        v_impl_3395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_3381_, v_k_3382_, v_v_3383_, v_l_3388_);
                        v___x_3396_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_3389_) == 0 {
                            v_size_3397_ = leanh::lean_ctor_get(v_r_3389_, 0);
                            v_size_3398_ = leanh::lean_ctor_get(v_impl_3395_, 0);
                            leanh::lean_inc(v_size_3398_);
                            v_k_3399_ = leanh::lean_ctor_get(v_impl_3395_, 1);
                            leanh::lean_inc(v_k_3399_);
                            v_v_3400_ = leanh::lean_ctor_get(v_impl_3395_, 2);
                            leanh::lean_inc(v_v_3400_);
                            v_l_3401_ = leanh::lean_ctor_get(v_impl_3395_, 3);
                            leanh::lean_inc(v_l_3401_);
                            v_r_3402_ = leanh::lean_ctor_get(v_impl_3395_, 4);
                            leanh::lean_inc(v_r_3402_);
                            v___x_3403_ = leanh::lean_unsigned_to_nat(3);
                            v___x_3404_ = lean_nat_mul(v___x_3403_, v_size_3397_);
                            v___x_3405_ = lean_nat_dec_lt(v___x_3404_, v_size_3398_);
                            leanh::lean_dec(v___x_3404_);
                            if v___x_3405_ == 0 {
                                leanh::lean_dec(v_r_3402_);
                                leanh::lean_dec(v_l_3401_);
                                leanh::lean_dec(v_v_3400_);
                                leanh::lean_dec(v_k_3399_);
                                v___x_3406_ = lean_nat_add(v___x_3396_, v_size_3398_);
                                leanh::lean_dec(v_size_3398_);
                                v___x_3407_ = lean_nat_add(v___x_3406_, v_size_3397_);
                                leanh::lean_dec(v___x_3406_);
                                if v_isShared_3392_ == 0 {
                                    leanh::lean_ctor_set(v___x_3391_, 3, v_impl_3395_);
                                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3407_);
                                    v___x_3409_ = v___x_3391_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3410_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3410_,
                                        0,
                                        v___x_3407_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3410_,
                                        1,
                                        v_k_3386_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3410_,
                                        2,
                                        v_v_3387_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3410_,
                                        3,
                                        v_impl_3395_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3410_,
                                        4,
                                        v_r_3389_,
                                    );
                                    v___x_3409_ = v_reuseFailAlloc_3410_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3476_ =
                                    (!leanh::lean_is_exclusive(v_impl_3395_)) as u8;
                                if v_isSharedCheck_3476_ == 0 {
                                    v_unused_3477_ = leanh::lean_ctor_get(v_impl_3395_, 4);
                                    leanh::lean_dec(v_unused_3477_);
                                    v_unused_3478_ = leanh::lean_ctor_get(v_impl_3395_, 3);
                                    leanh::lean_dec(v_unused_3478_);
                                    v_unused_3479_ = leanh::lean_ctor_get(v_impl_3395_, 2);
                                    leanh::lean_dec(v_unused_3479_);
                                    v_unused_3480_ = leanh::lean_ctor_get(v_impl_3395_, 1);
                                    leanh::lean_dec(v_unused_3480_);
                                    v_unused_3481_ = leanh::lean_ctor_get(v_impl_3395_, 0);
                                    leanh::lean_dec(v_unused_3481_);
                                    v___x_3412_ = v_impl_3395_;
                                    v_isShared_3413_ = v_isSharedCheck_3476_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_3395_);
                                    v___x_3412_ = leanh::lean_box(0);
                                    v_isShared_3413_ = v_isSharedCheck_3476_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3482_ = leanh::lean_ctor_get(v_impl_3395_, 3);
                            leanh::lean_inc(v_l_3482_);
                            if leanh::lean_obj_tag(v_l_3482_) == 0 {
                                v_r_3483_ = leanh::lean_ctor_get(v_impl_3395_, 4);
                                v_k_3484_ = leanh::lean_ctor_get(v_impl_3395_, 1);
                                v_v_3485_ = leanh::lean_ctor_get(v_impl_3395_, 2);
                                v_isSharedCheck_3496_ =
                                    (!leanh::lean_is_exclusive(v_impl_3395_)) as u8;
                                if v_isSharedCheck_3496_ == 0 {
                                    v_unused_3497_ = leanh::lean_ctor_get(v_impl_3395_, 3);
                                    leanh::lean_dec(v_unused_3497_);
                                    v_unused_3498_ = leanh::lean_ctor_get(v_impl_3395_, 0);
                                    leanh::lean_dec(v_unused_3498_);
                                    v___x_3487_ = v_impl_3395_;
                                    v_isShared_3488_ = v_isSharedCheck_3496_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_3483_);
                                    leanh::lean_inc(v_v_3485_);
                                    leanh::lean_inc(v_k_3484_);
                                    leanh::lean_dec(v_impl_3395_);
                                    v___x_3487_ = leanh::lean_box(0);
                                    v_isShared_3488_ = v_isSharedCheck_3496_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3499_ = leanh::lean_ctor_get(v_impl_3395_, 4);
                                leanh::lean_inc(v_r_3499_);
                                if leanh::lean_obj_tag(v_r_3499_) == 0 {
                                    v_k_3500_ = leanh::lean_ctor_get(v_impl_3395_, 1);
                                    v_v_3501_ = leanh::lean_ctor_get(v_impl_3395_, 2);
                                    v_isSharedCheck_3524_ =
                                        (!leanh::lean_is_exclusive(v_impl_3395_)) as u8;
                                    if v_isSharedCheck_3524_ == 0 {
                                        v_unused_3525_ =
                                            leanh::lean_ctor_get(v_impl_3395_, 4);
                                        leanh::lean_dec(v_unused_3525_);
                                        v_unused_3526_ =
                                            leanh::lean_ctor_get(v_impl_3395_, 3);
                                        leanh::lean_dec(v_unused_3526_);
                                        v_unused_3527_ =
                                            leanh::lean_ctor_get(v_impl_3395_, 0);
                                        leanh::lean_dec(v_unused_3527_);
                                        v___x_3503_ = v_impl_3395_;
                                        v_isShared_3504_ = v_isSharedCheck_3524_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_3501_);
                                        leanh::lean_inc(v_k_3500_);
                                        leanh::lean_dec(v_impl_3395_);
                                        v___x_3503_ = leanh::lean_box(0);
                                        v_isShared_3504_ = v_isSharedCheck_3524_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_3528_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_3392_ == 0 {
                                        leanh::lean_ctor_set(v___x_3391_, 4, v_r_3499_);
                                        leanh::lean_ctor_set(v___x_3391_, 3, v_impl_3395_);
                                        leanh::lean_ctor_set(v___x_3391_, 0, v___x_3528_);
                                        v___x_3530_ = v___x_3391_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3531_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            0,
                                            v___x_3528_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            1,
                                            v_k_3386_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            2,
                                            v_v_3387_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            3,
                                            v_impl_3395_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            4,
                                            v_r_3499_,
                                        );
                                        v___x_3530_ = v_reuseFailAlloc_3531_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_3387_);
                        leanh::lean_dec(v_k_3386_);
                        leanh::lean_dec_ref(v_cmp_3381_);
                        if v_isShared_3392_ == 0 {
                            leanh::lean_ctor_set(v___x_3391_, 2, v_v_3383_);
                            leanh::lean_ctor_set(v___x_3391_, 1, v_k_3382_);
                            v___x_3533_ = v___x_3391_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3534_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_size_3385_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_k_3382_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_v_3383_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_l_3388_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_r_3389_);
                            v___x_3533_ = v_reuseFailAlloc_3534_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_3385_);
                        v_impl_3535_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1___redArg(v_cmp_3381_, v_k_3382_, v_v_3383_, v_r_3389_);
                        v___x_3536_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_3388_) == 0 {
                            v_size_3537_ = leanh::lean_ctor_get(v_l_3388_, 0);
                            v_size_3538_ = leanh::lean_ctor_get(v_impl_3535_, 0);
                            leanh::lean_inc(v_size_3538_);
                            v_k_3539_ = leanh::lean_ctor_get(v_impl_3535_, 1);
                            leanh::lean_inc(v_k_3539_);
                            v_v_3540_ = leanh::lean_ctor_get(v_impl_3535_, 2);
                            leanh::lean_inc(v_v_3540_);
                            v_l_3541_ = leanh::lean_ctor_get(v_impl_3535_, 3);
                            leanh::lean_inc(v_l_3541_);
                            v_r_3542_ = leanh::lean_ctor_get(v_impl_3535_, 4);
                            leanh::lean_inc(v_r_3542_);
                            v___x_3543_ = leanh::lean_unsigned_to_nat(3);
                            v___x_3544_ = lean_nat_mul(v___x_3543_, v_size_3537_);
                            v___x_3545_ = lean_nat_dec_lt(v___x_3544_, v_size_3538_);
                            leanh::lean_dec(v___x_3544_);
                            if v___x_3545_ == 0 {
                                leanh::lean_dec(v_r_3542_);
                                leanh::lean_dec(v_l_3541_);
                                leanh::lean_dec(v_v_3540_);
                                leanh::lean_dec(v_k_3539_);
                                v___x_3546_ = lean_nat_add(v___x_3536_, v_size_3537_);
                                v___x_3547_ = lean_nat_add(v___x_3546_, v_size_3538_);
                                leanh::lean_dec(v_size_3538_);
                                leanh::lean_dec(v___x_3546_);
                                if v_isShared_3392_ == 0 {
                                    leanh::lean_ctor_set(v___x_3391_, 4, v_impl_3535_);
                                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3547_);
                                    v___x_3549_ = v___x_3391_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3550_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3550_,
                                        0,
                                        v___x_3547_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3550_,
                                        1,
                                        v_k_3386_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3550_,
                                        2,
                                        v_v_3387_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3550_,
                                        3,
                                        v_l_3388_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3550_,
                                        4,
                                        v_impl_3535_,
                                    );
                                    v___x_3549_ = v_reuseFailAlloc_3550_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3614_ =
                                    (!leanh::lean_is_exclusive(v_impl_3535_)) as u8;
                                if v_isSharedCheck_3614_ == 0 {
                                    v_unused_3615_ = leanh::lean_ctor_get(v_impl_3535_, 4);
                                    leanh::lean_dec(v_unused_3615_);
                                    v_unused_3616_ = leanh::lean_ctor_get(v_impl_3535_, 3);
                                    leanh::lean_dec(v_unused_3616_);
                                    v_unused_3617_ = leanh::lean_ctor_get(v_impl_3535_, 2);
                                    leanh::lean_dec(v_unused_3617_);
                                    v_unused_3618_ = leanh::lean_ctor_get(v_impl_3535_, 1);
                                    leanh::lean_dec(v_unused_3618_);
                                    v_unused_3619_ = leanh::lean_ctor_get(v_impl_3535_, 0);
                                    leanh::lean_dec(v_unused_3619_);
                                    v___x_3552_ = v_impl_3535_;
                                    v_isShared_3553_ = v_isSharedCheck_3614_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_3535_);
                                    v___x_3552_ = leanh::lean_box(0);
                                    v_isShared_3553_ = v_isSharedCheck_3614_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3620_ = leanh::lean_ctor_get(v_impl_3535_, 3);
                            leanh::lean_inc(v_l_3620_);
                            if leanh::lean_obj_tag(v_l_3620_) == 0 {
                                v_r_3621_ = leanh::lean_ctor_get(v_impl_3535_, 4);
                                v_k_3622_ = leanh::lean_ctor_get(v_impl_3535_, 1);
                                v_v_3623_ = leanh::lean_ctor_get(v_impl_3535_, 2);
                                v_isSharedCheck_3646_ =
                                    (!leanh::lean_is_exclusive(v_impl_3535_)) as u8;
                                if v_isSharedCheck_3646_ == 0 {
                                    v_unused_3647_ = leanh::lean_ctor_get(v_impl_3535_, 3);
                                    leanh::lean_dec(v_unused_3647_);
                                    v_unused_3648_ = leanh::lean_ctor_get(v_impl_3535_, 0);
                                    leanh::lean_dec(v_unused_3648_);
                                    v___x_3625_ = v_impl_3535_;
                                    v_isShared_3626_ = v_isSharedCheck_3646_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_3621_);
                                    leanh::lean_inc(v_v_3623_);
                                    leanh::lean_inc(v_k_3622_);
                                    leanh::lean_dec(v_impl_3535_);
                                    v___x_3625_ = leanh::lean_box(0);
                                    v_isShared_3626_ = v_isSharedCheck_3646_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3649_ = leanh::lean_ctor_get(v_impl_3535_, 4);
                                leanh::lean_inc(v_r_3649_);
                                if leanh::lean_obj_tag(v_r_3649_) == 0 {
                                    v_k_3650_ = leanh::lean_ctor_get(v_impl_3535_, 1);
                                    v_v_3651_ = leanh::lean_ctor_get(v_impl_3535_, 2);
                                    v_isSharedCheck_3662_ =
                                        (!leanh::lean_is_exclusive(v_impl_3535_)) as u8;
                                    if v_isSharedCheck_3662_ == 0 {
                                        v_unused_3663_ =
                                            leanh::lean_ctor_get(v_impl_3535_, 4);
                                        leanh::lean_dec(v_unused_3663_);
                                        v_unused_3664_ =
                                            leanh::lean_ctor_get(v_impl_3535_, 3);
                                        leanh::lean_dec(v_unused_3664_);
                                        v_unused_3665_ =
                                            leanh::lean_ctor_get(v_impl_3535_, 0);
                                        leanh::lean_dec(v_unused_3665_);
                                        v___x_3653_ = v_impl_3535_;
                                        v_isShared_3654_ = v_isSharedCheck_3662_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_3651_);
                                        leanh::lean_inc(v_k_3650_);
                                        leanh::lean_dec(v_impl_3535_);
                                        v___x_3653_ = leanh::lean_box(0);
                                        v_isShared_3654_ = v_isSharedCheck_3662_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3666_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_3392_ == 0 {
                                        leanh::lean_ctor_set(v___x_3391_, 4, v_impl_3535_);
                                        leanh::lean_ctor_set(v___x_3391_, 3, v_r_3649_);
                                        leanh::lean_ctor_set(v___x_3391_, 0, v___x_3666_);
                                        v___x_3668_ = v___x_3391_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3669_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3669_,
                                            0,
                                            v___x_3666_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3669_,
                                            1,
                                            v_k_3386_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3669_,
                                            2,
                                            v_v_3387_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3669_,
                                            3,
                                            v_r_3649_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3669_,
                                            4,
                                            v_impl_3535_,
                                        );
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
                v_size_3414_ = leanh::lean_ctor_get(v_l_3401_, 0);
                v_size_3415_ = leanh::lean_ctor_get(v_r_3402_, 0);
                v_k_3416_ = leanh::lean_ctor_get(v_r_3402_, 1);
                v_v_3417_ = leanh::lean_ctor_get(v_r_3402_, 2);
                v_l_3418_ = leanh::lean_ctor_get(v_r_3402_, 3);
                v_r_3419_ = leanh::lean_ctor_get(v_r_3402_, 4);
                v___x_3420_ = leanh::lean_unsigned_to_nat(2);
                v___x_3421_ = lean_nat_mul(v___x_3420_, v_size_3414_);
                v___x_3422_ = lean_nat_dec_lt(v_size_3415_, v___x_3421_);
                leanh::lean_dec(v___x_3421_);
                if v___x_3422_ == 0 {
                    leanh::lean_inc(v_r_3419_);
                    leanh::lean_inc(v_l_3418_);
                    leanh::lean_inc(v_v_3417_);
                    leanh::lean_inc(v_k_3416_);
                    v_isSharedCheck_3451_ = (!leanh::lean_is_exclusive(v_r_3402_)) as u8;
                    if v_isSharedCheck_3451_ == 0 {
                        v_unused_3452_ = leanh::lean_ctor_get(v_r_3402_, 4);
                        leanh::lean_dec(v_unused_3452_);
                        v_unused_3453_ = leanh::lean_ctor_get(v_r_3402_, 3);
                        leanh::lean_dec(v_unused_3453_);
                        v_unused_3454_ = leanh::lean_ctor_get(v_r_3402_, 2);
                        leanh::lean_dec(v_unused_3454_);
                        v_unused_3455_ = leanh::lean_ctor_get(v_r_3402_, 1);
                        leanh::lean_dec(v_unused_3455_);
                        v_unused_3456_ = leanh::lean_ctor_get(v_r_3402_, 0);
                        leanh::lean_dec(v_unused_3456_);
                        v___x_3424_ = v_r_3402_;
                        v_isShared_3425_ = v_isSharedCheck_3451_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_3402_);
                        v___x_3424_ = leanh::lean_box(0);
                        v_isShared_3425_ = v_isSharedCheck_3451_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3391_);
                    v___x_3457_ = lean_nat_add(v___x_3396_, v_size_3398_);
                    leanh::lean_dec(v_size_3398_);
                    v___x_3458_ = lean_nat_add(v___x_3457_, v_size_3397_);
                    leanh::lean_dec(v___x_3457_);
                    v___x_3459_ = lean_nat_add(v___x_3396_, v_size_3397_);
                    v___x_3460_ = lean_nat_add(v___x_3459_, v_size_3415_);
                    leanh::lean_dec(v___x_3459_);
                    leanh::lean_inc_ref(v_r_3389_);
                    if v_isShared_3413_ == 0 {
                        leanh::lean_ctor_set(v___x_3412_, 4, v_r_3389_);
                        leanh::lean_ctor_set(v___x_3412_, 3, v_r_3402_);
                        leanh::lean_ctor_set(v___x_3412_, 2, v_v_3387_);
                        leanh::lean_ctor_set(v___x_3412_, 1, v_k_3386_);
                        leanh::lean_ctor_set(v___x_3412_, 0, v___x_3460_);
                        v___x_3462_ = v___x_3412_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3475_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3460_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_k_3386_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 2, v_v_3387_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_r_3402_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 4, v_r_3389_);
                        v___x_3462_ = v_reuseFailAlloc_3475_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3426_ = lean_nat_add(v___x_3396_, v_size_3398_);
                leanh::lean_dec(v_size_3398_);
                v___x_3427_ = lean_nat_add(v___x_3426_, v_size_3397_);
                leanh::lean_dec(v___x_3426_);
                v___x_3439_ = lean_nat_add(v___x_3396_, v_size_3414_);
                if leanh::lean_obj_tag(v_l_3418_) == 0 {
                    v_size_3449_ = leanh::lean_ctor_get(v_l_3418_, 0);
                    leanh::lean_inc(v_size_3449_);
                    v___y_3441_ = v_size_3449_;
                    state = 8;
                    continue;
                } else {
                    v___x_3450_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3441_ = v___x_3450_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3432_ = lean_nat_add(v___y_3429_, v___y_3431_);
                leanh::lean_dec(v___y_3431_);
                leanh::lean_dec(v___y_3429_);
                if v_isShared_3425_ == 0 {
                    leanh::lean_ctor_set(v___x_3424_, 4, v_r_3389_);
                    leanh::lean_ctor_set(v___x_3424_, 3, v_r_3419_);
                    leanh::lean_ctor_set(v___x_3424_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v___x_3424_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v___x_3424_, 0, v___x_3432_);
                    v___x_3434_ = v___x_3424_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 3, v_r_3419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 4, v_r_3389_);
                    v___x_3434_ = v_reuseFailAlloc_3438_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3413_ == 0 {
                    leanh::lean_ctor_set(v___x_3412_, 4, v___x_3434_);
                    leanh::lean_ctor_set(v___x_3412_, 3, v___y_3430_);
                    leanh::lean_ctor_set(v___x_3412_, 2, v_v_3417_);
                    leanh::lean_ctor_set(v___x_3412_, 1, v_k_3416_);
                    leanh::lean_ctor_set(v___x_3412_, 0, v___x_3427_);
                    v___x_3436_ = v___x_3412_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_k_3416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_v_3417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 3, v___y_3430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 4, v___x_3434_);
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
                leanh::lean_dec(v___y_3441_);
                leanh::lean_dec(v___x_3439_);
                if v_isShared_3392_ == 0 {
                    leanh::lean_ctor_set(v___x_3391_, 4, v_l_3418_);
                    leanh::lean_ctor_set(v___x_3391_, 3, v_l_3401_);
                    leanh::lean_ctor_set(v___x_3391_, 2, v_v_3400_);
                    leanh::lean_ctor_set(v___x_3391_, 1, v_k_3399_);
                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3442_);
                    v___x_3444_ = v___x_3391_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3448_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_l_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_l_3418_);
                    v___x_3444_ = v_reuseFailAlloc_3448_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3445_ = lean_nat_add(v___x_3396_, v_size_3397_);
                if leanh::lean_obj_tag(v_r_3419_) == 0 {
                    v_size_3446_ = leanh::lean_ctor_get(v_r_3419_, 0);
                    leanh::lean_inc(v_size_3446_);
                    v___y_3429_ = v___x_3445_;
                    v___y_3430_ = v___x_3444_;
                    v___y_3431_ = v_size_3446_;
                    state = 5;
                    continue;
                } else {
                    v___x_3447_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3429_ = v___x_3445_;
                    v___y_3430_ = v___x_3444_;
                    v___y_3431_ = v___x_3447_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3469_ = (!leanh::lean_is_exclusive(v_r_3389_)) as u8;
                if v_isSharedCheck_3469_ == 0 {
                    v_unused_3470_ = leanh::lean_ctor_get(v_r_3389_, 4);
                    leanh::lean_dec(v_unused_3470_);
                    v_unused_3471_ = leanh::lean_ctor_get(v_r_3389_, 3);
                    leanh::lean_dec(v_unused_3471_);
                    v_unused_3472_ = leanh::lean_ctor_get(v_r_3389_, 2);
                    leanh::lean_dec(v_unused_3472_);
                    v_unused_3473_ = leanh::lean_ctor_get(v_r_3389_, 1);
                    leanh::lean_dec(v_unused_3473_);
                    v_unused_3474_ = leanh::lean_ctor_get(v_r_3389_, 0);
                    leanh::lean_dec(v_unused_3474_);
                    v___x_3464_ = v_r_3389_;
                    v_isShared_3465_ = v_isSharedCheck_3469_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_3389_);
                    v___x_3464_ = leanh::lean_box(0);
                    v_isShared_3465_ = v_isSharedCheck_3469_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3465_ == 0 {
                    leanh::lean_ctor_set(v___x_3464_, 4, v___x_3462_);
                    leanh::lean_ctor_set(v___x_3464_, 3, v_l_3401_);
                    leanh::lean_ctor_set(v___x_3464_, 2, v_v_3400_);
                    leanh::lean_ctor_set(v___x_3464_, 1, v_k_3399_);
                    leanh::lean_ctor_set(v___x_3464_, 0, v___x_3458_);
                    v___x_3467_ = v___x_3464_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3458_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_k_3399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_v_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_l_3401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 4, v___x_3462_);
                    v___x_3467_ = v_reuseFailAlloc_3468_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3467_;
            }
            13 => {
                v___x_3489_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_3483_);
                if v_isShared_3488_ == 0 {
                    leanh::lean_ctor_set(v___x_3487_, 3, v_r_3483_);
                    leanh::lean_ctor_set(v___x_3487_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v___x_3487_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v___x_3487_, 0, v___x_3396_);
                    v___x_3491_ = v___x_3487_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_r_3483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_r_3483_);
                    v___x_3491_ = v_reuseFailAlloc_3495_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_3392_ == 0 {
                    leanh::lean_ctor_set(v___x_3391_, 4, v___x_3491_);
                    leanh::lean_ctor_set(v___x_3391_, 3, v_l_3482_);
                    leanh::lean_ctor_set(v___x_3391_, 2, v_v_3485_);
                    leanh::lean_ctor_set(v___x_3391_, 1, v_k_3484_);
                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3489_);
                    v___x_3493_ = v___x_3391_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3489_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_l_3482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 4, v___x_3491_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3493_;
            }
            16 => {
                v_k_3505_ = leanh::lean_ctor_get(v_r_3499_, 1);
                v_v_3506_ = leanh::lean_ctor_get(v_r_3499_, 2);
                v_isSharedCheck_3520_ = (!leanh::lean_is_exclusive(v_r_3499_)) as u8;
                if v_isSharedCheck_3520_ == 0 {
                    v_unused_3521_ = leanh::lean_ctor_get(v_r_3499_, 4);
                    leanh::lean_dec(v_unused_3521_);
                    v_unused_3522_ = leanh::lean_ctor_get(v_r_3499_, 3);
                    leanh::lean_dec(v_unused_3522_);
                    v_unused_3523_ = leanh::lean_ctor_get(v_r_3499_, 0);
                    leanh::lean_dec(v_unused_3523_);
                    v___x_3508_ = v_r_3499_;
                    v_isShared_3509_ = v_isSharedCheck_3520_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3506_);
                    leanh::lean_inc(v_k_3505_);
                    leanh::lean_dec(v_r_3499_);
                    v___x_3508_ = leanh::lean_box(0);
                    v_isShared_3509_ = v_isSharedCheck_3520_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3510_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3509_ == 0 {
                    leanh::lean_ctor_set(v___x_3508_, 4, v_l_3482_);
                    leanh::lean_ctor_set(v___x_3508_, 3, v_l_3482_);
                    leanh::lean_ctor_set(v___x_3508_, 2, v_v_3501_);
                    leanh::lean_ctor_set(v___x_3508_, 1, v_k_3500_);
                    leanh::lean_ctor_set(v___x_3508_, 0, v___x_3396_);
                    v___x_3512_ = v___x_3508_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_k_3500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 2, v_v_3501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 3, v_l_3482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 4, v_l_3482_);
                    v___x_3512_ = v_reuseFailAlloc_3519_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3504_ == 0 {
                    leanh::lean_ctor_set(v___x_3503_, 4, v_l_3482_);
                    leanh::lean_ctor_set(v___x_3503_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v___x_3503_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v___x_3503_, 0, v___x_3396_);
                    v___x_3514_ = v___x_3503_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3518_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 3, v_l_3482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 4, v_l_3482_);
                    v___x_3514_ = v_reuseFailAlloc_3518_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3392_ == 0 {
                    leanh::lean_ctor_set(v___x_3391_, 4, v___x_3514_);
                    leanh::lean_ctor_set(v___x_3391_, 3, v___x_3512_);
                    leanh::lean_ctor_set(v___x_3391_, 2, v_v_3506_);
                    leanh::lean_ctor_set(v___x_3391_, 1, v_k_3505_);
                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3510_);
                    v___x_3516_ = v___x_3391_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_k_3505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_v_3506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 3, v___x_3512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 4, v___x_3514_);
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
                v_size_3554_ = leanh::lean_ctor_get(v_l_3541_, 0);
                v_k_3555_ = leanh::lean_ctor_get(v_l_3541_, 1);
                v_v_3556_ = leanh::lean_ctor_get(v_l_3541_, 2);
                v_l_3557_ = leanh::lean_ctor_get(v_l_3541_, 3);
                v_r_3558_ = leanh::lean_ctor_get(v_l_3541_, 4);
                v_size_3559_ = leanh::lean_ctor_get(v_r_3542_, 0);
                v___x_3560_ = leanh::lean_unsigned_to_nat(2);
                v___x_3561_ = lean_nat_mul(v___x_3560_, v_size_3559_);
                v___x_3562_ = lean_nat_dec_lt(v_size_3554_, v___x_3561_);
                leanh::lean_dec(v___x_3561_);
                if v___x_3562_ == 0 {
                    leanh::lean_inc(v_r_3558_);
                    leanh::lean_inc(v_l_3557_);
                    leanh::lean_inc(v_v_3556_);
                    leanh::lean_inc(v_k_3555_);
                    v_isSharedCheck_3590_ = (!leanh::lean_is_exclusive(v_l_3541_)) as u8;
                    if v_isSharedCheck_3590_ == 0 {
                        v_unused_3591_ = leanh::lean_ctor_get(v_l_3541_, 4);
                        leanh::lean_dec(v_unused_3591_);
                        v_unused_3592_ = leanh::lean_ctor_get(v_l_3541_, 3);
                        leanh::lean_dec(v_unused_3592_);
                        v_unused_3593_ = leanh::lean_ctor_get(v_l_3541_, 2);
                        leanh::lean_dec(v_unused_3593_);
                        v_unused_3594_ = leanh::lean_ctor_get(v_l_3541_, 1);
                        leanh::lean_dec(v_unused_3594_);
                        v_unused_3595_ = leanh::lean_ctor_get(v_l_3541_, 0);
                        leanh::lean_dec(v_unused_3595_);
                        v___x_3564_ = v_l_3541_;
                        v_isShared_3565_ = v_isSharedCheck_3590_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_3541_);
                        v___x_3564_ = leanh::lean_box(0);
                        v_isShared_3565_ = v_isSharedCheck_3590_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3391_);
                    v___x_3596_ = lean_nat_add(v___x_3536_, v_size_3537_);
                    v___x_3597_ = lean_nat_add(v___x_3596_, v_size_3538_);
                    leanh::lean_dec(v_size_3538_);
                    v___x_3598_ = lean_nat_add(v___x_3596_, v_size_3554_);
                    leanh::lean_dec(v___x_3596_);
                    leanh::lean_inc_ref(v_l_3388_);
                    if v_isShared_3553_ == 0 {
                        leanh::lean_ctor_set(v___x_3552_, 4, v_l_3541_);
                        leanh::lean_ctor_set(v___x_3552_, 3, v_l_3388_);
                        leanh::lean_ctor_set(v___x_3552_, 2, v_v_3387_);
                        leanh::lean_ctor_set(v___x_3552_, 1, v_k_3386_);
                        leanh::lean_ctor_set(v___x_3552_, 0, v___x_3598_);
                        v___x_3600_ = v___x_3552_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3613_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3598_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_k_3386_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_v_3387_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_l_3388_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 4, v_l_3541_);
                        v___x_3600_ = v_reuseFailAlloc_3613_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3566_ = lean_nat_add(v___x_3536_, v_size_3537_);
                v___x_3567_ = lean_nat_add(v___x_3566_, v_size_3538_);
                leanh::lean_dec(v_size_3538_);
                if leanh::lean_obj_tag(v_l_3557_) == 0 {
                    v_size_3588_ = leanh::lean_ctor_get(v_l_3557_, 0);
                    leanh::lean_inc(v_size_3588_);
                    v___y_3580_ = v_size_3588_;
                    state = 29;
                    continue;
                } else {
                    v___x_3589_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3580_ = v___x_3589_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3572_ = lean_nat_add(v___y_3569_, v___y_3571_);
                leanh::lean_dec(v___y_3571_);
                leanh::lean_dec(v___y_3569_);
                if v_isShared_3565_ == 0 {
                    leanh::lean_ctor_set(v___x_3564_, 4, v_r_3542_);
                    leanh::lean_ctor_set(v___x_3564_, 3, v_r_3558_);
                    leanh::lean_ctor_set(v___x_3564_, 2, v_v_3540_);
                    leanh::lean_ctor_set(v___x_3564_, 1, v_k_3539_);
                    leanh::lean_ctor_set(v___x_3564_, 0, v___x_3572_);
                    v___x_3574_ = v___x_3564_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_k_3539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_v_3540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_r_3558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 4, v_r_3542_);
                    v___x_3574_ = v_reuseFailAlloc_3578_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3553_ == 0 {
                    leanh::lean_ctor_set(v___x_3552_, 4, v___x_3574_);
                    leanh::lean_ctor_set(v___x_3552_, 3, v___y_3570_);
                    leanh::lean_ctor_set(v___x_3552_, 2, v_v_3556_);
                    leanh::lean_ctor_set(v___x_3552_, 1, v_k_3555_);
                    leanh::lean_ctor_set(v___x_3552_, 0, v___x_3567_);
                    v___x_3576_ = v___x_3552_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_k_3555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_v_3556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 3, v___y_3570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 4, v___x_3574_);
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
                leanh::lean_dec(v___y_3580_);
                leanh::lean_dec(v___x_3566_);
                if v_isShared_3392_ == 0 {
                    leanh::lean_ctor_set(v___x_3391_, 4, v_l_3557_);
                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3581_);
                    v___x_3583_ = v___x_3391_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_l_3388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_l_3557_);
                    v___x_3583_ = v_reuseFailAlloc_3587_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3584_ = lean_nat_add(v___x_3536_, v_size_3559_);
                if leanh::lean_obj_tag(v_r_3558_) == 0 {
                    v_size_3585_ = leanh::lean_ctor_get(v_r_3558_, 0);
                    leanh::lean_inc(v_size_3585_);
                    v___y_3569_ = v___x_3584_;
                    v___y_3570_ = v___x_3583_;
                    v___y_3571_ = v_size_3585_;
                    state = 26;
                    continue;
                } else {
                    v___x_3586_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3569_ = v___x_3584_;
                    v___y_3570_ = v___x_3583_;
                    v___y_3571_ = v___x_3586_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3607_ = (!leanh::lean_is_exclusive(v_l_3388_)) as u8;
                if v_isSharedCheck_3607_ == 0 {
                    v_unused_3608_ = leanh::lean_ctor_get(v_l_3388_, 4);
                    leanh::lean_dec(v_unused_3608_);
                    v_unused_3609_ = leanh::lean_ctor_get(v_l_3388_, 3);
                    leanh::lean_dec(v_unused_3609_);
                    v_unused_3610_ = leanh::lean_ctor_get(v_l_3388_, 2);
                    leanh::lean_dec(v_unused_3610_);
                    v_unused_3611_ = leanh::lean_ctor_get(v_l_3388_, 1);
                    leanh::lean_dec(v_unused_3611_);
                    v_unused_3612_ = leanh::lean_ctor_get(v_l_3388_, 0);
                    leanh::lean_dec(v_unused_3612_);
                    v___x_3602_ = v_l_3388_;
                    v_isShared_3603_ = v_isSharedCheck_3607_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_3388_);
                    v___x_3602_ = leanh::lean_box(0);
                    v_isShared_3603_ = v_isSharedCheck_3607_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3603_ == 0 {
                    leanh::lean_ctor_set(v___x_3602_, 4, v_r_3542_);
                    leanh::lean_ctor_set(v___x_3602_, 3, v___x_3600_);
                    leanh::lean_ctor_set(v___x_3602_, 2, v_v_3540_);
                    leanh::lean_ctor_set(v___x_3602_, 1, v_k_3539_);
                    leanh::lean_ctor_set(v___x_3602_, 0, v___x_3597_);
                    v___x_3605_ = v___x_3602_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3606_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3597_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_k_3539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 2, v_v_3540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 3, v___x_3600_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 4, v_r_3542_);
                    v___x_3605_ = v_reuseFailAlloc_3606_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3605_;
            }
            34 => {
                v_k_3627_ = leanh::lean_ctor_get(v_l_3620_, 1);
                v_v_3628_ = leanh::lean_ctor_get(v_l_3620_, 2);
                v_isSharedCheck_3642_ = (!leanh::lean_is_exclusive(v_l_3620_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v_unused_3643_ = leanh::lean_ctor_get(v_l_3620_, 4);
                    leanh::lean_dec(v_unused_3643_);
                    v_unused_3644_ = leanh::lean_ctor_get(v_l_3620_, 3);
                    leanh::lean_dec(v_unused_3644_);
                    v_unused_3645_ = leanh::lean_ctor_get(v_l_3620_, 0);
                    leanh::lean_dec(v_unused_3645_);
                    v___x_3630_ = v_l_3620_;
                    v_isShared_3631_ = v_isSharedCheck_3642_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3628_);
                    leanh::lean_inc(v_k_3627_);
                    leanh::lean_dec(v_l_3620_);
                    v___x_3630_ = leanh::lean_box(0);
                    v_isShared_3631_ = v_isSharedCheck_3642_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3632_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_3621_, 2);
                if v_isShared_3631_ == 0 {
                    leanh::lean_ctor_set(v___x_3630_, 4, v_r_3621_);
                    leanh::lean_ctor_set(v___x_3630_, 3, v_r_3621_);
                    leanh::lean_ctor_set(v___x_3630_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v___x_3630_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v___x_3630_, 0, v___x_3536_);
                    v___x_3634_ = v___x_3630_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_r_3621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_r_3621_);
                    v___x_3634_ = v_reuseFailAlloc_3641_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_3621_);
                if v_isShared_3626_ == 0 {
                    leanh::lean_ctor_set(v___x_3625_, 3, v_r_3621_);
                    leanh::lean_ctor_set(v___x_3625_, 0, v___x_3536_);
                    v___x_3636_ = v___x_3625_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_k_3622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 2, v_v_3623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 3, v_r_3621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 4, v_r_3621_);
                    v___x_3636_ = v_reuseFailAlloc_3640_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3392_ == 0 {
                    leanh::lean_ctor_set(v___x_3391_, 4, v___x_3636_);
                    leanh::lean_ctor_set(v___x_3391_, 3, v___x_3634_);
                    leanh::lean_ctor_set(v___x_3391_, 2, v_v_3628_);
                    leanh::lean_ctor_set(v___x_3391_, 1, v_k_3627_);
                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3632_);
                    v___x_3638_ = v___x_3391_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3639_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_k_3627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_v_3628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 3, v___x_3634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 4, v___x_3636_);
                    v___x_3638_ = v_reuseFailAlloc_3639_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3638_;
            }
            39 => {
                v___x_3655_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3654_ == 0 {
                    leanh::lean_ctor_set(v___x_3653_, 4, v_l_3620_);
                    leanh::lean_ctor_set(v___x_3653_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v___x_3653_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v___x_3653_, 0, v___x_3536_);
                    v___x_3657_ = v___x_3653_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_k_3386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_v_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 3, v_l_3620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 4, v_l_3620_);
                    v___x_3657_ = v_reuseFailAlloc_3661_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3392_ == 0 {
                    leanh::lean_ctor_set(v___x_3391_, 4, v_r_3649_);
                    leanh::lean_ctor_set(v___x_3391_, 3, v___x_3657_);
                    leanh::lean_ctor_set(v___x_3391_, 2, v_v_3651_);
                    leanh::lean_ctor_set(v___x_3391_, 1, v_k_3650_);
                    leanh::lean_ctor_set(v___x_3391_, 0, v___x_3655_);
                    v___x_3659_ = v___x_3391_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 3, v___x_3657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_r_3649_);
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
    mut v_cmp_3673_: *mut leanh::LeanObject,
    mut v_k_3674_: *mut leanh::LeanObject,
    mut v_t_3675_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: u8 = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3675_) == 0 {
                    v_k_3676_ = leanh::lean_ctor_get(v_t_3675_, 1);
                    leanh::lean_inc(v_k_3676_);
                    v_l_3677_ = leanh::lean_ctor_get(v_t_3675_, 3);
                    leanh::lean_inc(v_l_3677_);
                    v_r_3678_ = leanh::lean_ctor_get(v_t_3675_, 4);
                    leanh::lean_inc(v_r_3678_);
                    leanh::lean_dec_ref_known(v_t_3675_, 5);
                    leanh::lean_inc_ref(v_cmp_3673_);
                    leanh::lean_inc(v_k_3674_);
                    v___x_3679_ = leanh::lean_apply_2(v_cmp_3673_, v_k_3674_, v_k_3676_);
                    v___x_3680_ = (leanh::lean_unbox(v___x_3679_) as u8);
                    match v___x_3680_ {
                        0 => {
                            leanh::lean_dec(v_r_3678_);
                            v_t_3675_ = v_l_3677_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_dec(v_r_3678_);
                            leanh::lean_dec(v_l_3677_);
                            leanh::lean_dec(v_k_3674_);
                            leanh::lean_dec_ref(v_cmp_3673_);
                            v___x_3682_ = 1;
                            return v___x_3682_;
                        }
                        _ => {
                            leanh::lean_dec(v_l_3677_);
                            v_t_3675_ = v_r_3678_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_k_3674_);
                    leanh::lean_dec_ref(v_cmp_3673_);
                    v___x_3684_ = 0;
                    return v___x_3684_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg___boxed(
    mut v_cmp_3685_: *mut leanh::LeanObject,
    mut v_k_3686_: *mut leanh::LeanObject,
    mut v_t_3687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3688_: u8 = 0;
    let mut v_r_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3688_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(
            v_cmp_3685_,
            v_k_3686_,
            v_t_3687_,
        );
    v_r_3689_ = leanh::lean_box((v_res_3688_) as usize);
    return v_r_3689_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
    mut v_cmp_3690_: *mut leanh::LeanObject,
    mut v_as_x27_3691_: *mut leanh::LeanObject,
    mut v_b_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3691_) == 0 {
                    leanh::lean_dec_ref(v_cmp_3690_);
                    return v_b_3692_;
                } else {
                    v_head_3693_ = leanh::lean_ctor_get(v_as_x27_3691_, 0);
                    v_tail_3694_ = leanh::lean_ctor_get(v_as_x27_3691_, 1);
                    leanh::lean_inc(v_b_3692_);
                    leanh::lean_inc(v_head_3693_);
                    leanh::lean_inc_ref(v_cmp_3690_);
                    v___x_3695_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_3690_, v_head_3693_, v_b_3692_);
                    if v___x_3695_ == 0 {
                        v___x_3696_ = leanh::lean_box(0);
                        leanh::lean_inc(v_head_3693_);
                        leanh::lean_inc_ref(v_cmp_3690_);
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
    mut v_cmp_3700_: *mut leanh::LeanObject,
    mut v_as_x27_3701_: *mut leanh::LeanObject,
    mut v_b_3702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3703_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
        v_cmp_3700_,
        v_as_x27_3701_,
        v_b_3702_,
    );
    leanh::lean_dec(v_as_x27_3701_);
    return v_res_3703_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList___redArg(
    mut v_l_3704_: *mut leanh::LeanObject,
    mut v_cmp_3705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_3706_ = leanh::lean_box(1);
    v___x_3707_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
        v_cmp_3705_,
        v_l_3704_,
        v_r_3706_,
    );
    return v___x_3707_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList___redArg___boxed(
    mut v_l_3708_: *mut leanh::LeanObject,
    mut v_cmp_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Std_ExtTreeSet_ofList___redArg(v_l_3708_, v_cmp_3709_);
    leanh::lean_dec(v_l_3708_);
    return v_res_3710_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList(
    mut v_00_u03b1_3711_: *mut leanh::LeanObject,
    mut v_l_3712_: *mut leanh::LeanObject,
    mut v_cmp_3713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l_Std_ExtTreeSet_ofList___redArg(v_l_3712_, v_cmp_3713_);
    return v___x_3714_;
}
pub unsafe fn l_Std_ExtTreeSet_ofList___boxed(
    mut v_00_u03b1_3715_: *mut leanh::LeanObject,
    mut v_l_3716_: *mut leanh::LeanObject,
    mut v_cmp_3717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3718_ = l_Std_ExtTreeSet_ofList(v_00_u03b1_3715_, v_l_3716_, v_cmp_3717_);
    leanh::lean_dec(v_l_3716_);
    return v_res_3718_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(
    mut v_00_u03b1_3719_: *mut leanh::LeanObject,
    mut v_cmp_3720_: *mut leanh::LeanObject,
    mut v_00_u03b2_3721_: *mut leanh::LeanObject,
    mut v_k_3722_: *mut leanh::LeanObject,
    mut v_t_3723_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_3725_: *mut leanh::LeanObject,
    mut v_cmp_3726_: *mut leanh::LeanObject,
    mut v_00_u03b2_3727_: *mut leanh::LeanObject,
    mut v_k_3728_: *mut leanh::LeanObject,
    mut v_t_3729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3730_: u8 = 0;
    let mut v_r_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0(
        v_00_u03b1_3725_,
        v_cmp_3726_,
        v_00_u03b2_3727_,
        v_k_3728_,
        v_t_3729_,
    );
    v_r_3731_ = leanh::lean_box((v_res_3730_) as usize);
    return v_r_3731_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_ExtTreeSet_ofList_spec__1(
    mut v_00_u03b1_3732_: *mut leanh::LeanObject,
    mut v_cmp_3733_: *mut leanh::LeanObject,
    mut v_00_u03b2_3734_: *mut leanh::LeanObject,
    mut v_k_3735_: *mut leanh::LeanObject,
    mut v_v_3736_: *mut leanh::LeanObject,
    mut v_t_3737_: *mut leanh::LeanObject,
    mut v_hl_3738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3740_: *mut leanh::LeanObject,
    mut v_cmp_3741_: *mut leanh::LeanObject,
    mut v_as_3742_: *mut leanh::LeanObject,
    mut v_as_x27_3743_: *mut leanh::LeanObject,
    mut v_b_3744_: *mut leanh::LeanObject,
    mut v_a_3745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___redArg(
        v_cmp_3741_,
        v_as_x27_3743_,
        v_b_3744_,
    );
    return v___x_3746_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2___boxed(
    mut v_00_u03b1_3747_: *mut leanh::LeanObject,
    mut v_cmp_3748_: *mut leanh::LeanObject,
    mut v_as_3749_: *mut leanh::LeanObject,
    mut v_as_x27_3750_: *mut leanh::LeanObject,
    mut v_b_3751_: *mut leanh::LeanObject,
    mut v_a_3752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3753_ = l_List_forIn_x27_loop___at___00Std_ExtTreeSet_ofList_spec__2(
        v_00_u03b1_3747_,
        v_cmp_3748_,
        v_as_3749_,
        v_as_x27_3750_,
        v_b_3751_,
        v_a_3752_,
    );
    leanh::lean_dec(v_as_x27_3750_);
    leanh::lean_dec(v_as_3749_);
    return v_res_3753_;
}
pub unsafe fn l_Std_ExtTreeSet_toArray___redArg___lam__0(
    mut v_l_3754_: *mut leanh::LeanObject,
    mut v_k_3755_: *mut leanh::LeanObject,
    mut v_x_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = lean_array_push(v_l_3754_, v_k_3755_);
    return v___x_3757_;
}
pub unsafe fn l_Std_ExtTreeSet_toArray___redArg(
    mut v_t_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3760_ = l_Std_ExtTreeSet_toArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_3759_) == 0 {
                    v_size_3765_ = leanh::lean_ctor_get(v_t_3759_, 0);
                    leanh::lean_inc(v_size_3765_);
                    v___y_3762_ = v_size_3765_;
                    state = 1;
                    continue;
                } else {
                    v___x_3766_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3762_ = v___x_3766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3763_ = lean_mk_empty_array_with_capacity(v___y_3762_);
                leanh::lean_dec(v___y_3762_);
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
    mut v_00_u03b1_3767_: *mut leanh::LeanObject,
    mut v_cmp_3768_: *mut leanh::LeanObject,
    mut v_inst_3769_: *mut leanh::LeanObject,
    mut v_t_3770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3771_ = l_Std_ExtTreeSet_toArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_3770_) == 0 {
                    v_size_3776_ = leanh::lean_ctor_get(v_t_3770_, 0);
                    leanh::lean_inc(v_size_3776_);
                    v___y_3773_ = v_size_3776_;
                    state = 1;
                    continue;
                } else {
                    v___x_3777_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3773_ = v___x_3777_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3774_ = lean_mk_empty_array_with_capacity(v___y_3773_);
                leanh::lean_dec(v___y_3773_);
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
    mut v_00_u03b1_3778_: *mut leanh::LeanObject,
    mut v_cmp_3779_: *mut leanh::LeanObject,
    mut v_inst_3780_: *mut leanh::LeanObject,
    mut v_t_3781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_Std_ExtTreeSet_toArray(v_00_u03b1_3778_, v_cmp_3779_, v_inst_3780_, v_t_3781_);
    leanh::lean_dec_ref(v_cmp_3779_);
    return v_res_3782_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_ofArray___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3783_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_ExtTreeSet___auto__1___closed__26,
    );
    return v___x_3783_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(
    mut v_cmp_3784_: *mut leanh::LeanObject,
    mut v_as_3785_: *mut leanh::LeanObject,
    mut v_sz_3786_: usize,
    mut v_i_3787_: usize,
    mut v_b_3788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: usize = 0;
    let mut v___x_3792_: usize = 0;
    let mut v___x_3794_: u8 = 0;
    let mut v_a_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3794_ = lean_usize_dec_lt(v_i_3787_, v_sz_3786_);
                if v___x_3794_ == 0 {
                    leanh::lean_dec_ref(v_cmp_3784_);
                    return v_b_3788_;
                } else {
                    v_a_3795_ = lean_array_uget_borrowed(v_as_3785_, v_i_3787_);
                    leanh::lean_inc(v_b_3788_);
                    leanh::lean_inc(v_a_3795_);
                    leanh::lean_inc_ref(v_cmp_3784_);
                    v___x_3796_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_ExtTreeSet_ofList_spec__0___redArg(v_cmp_3784_, v_a_3795_, v_b_3788_);
                    if v___x_3796_ == 0 {
                        v___x_3797_ = leanh::lean_box(0);
                        leanh::lean_inc(v_a_3795_);
                        leanh::lean_inc_ref(v_cmp_3784_);
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
    mut v_cmp_3799_: *mut leanh::LeanObject,
    mut v_as_3800_: *mut leanh::LeanObject,
    mut v_sz_3801_: *mut leanh::LeanObject,
    mut v_i_3802_: *mut leanh::LeanObject,
    mut v_b_3803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3804_: usize = 0;
    let mut v_i_boxed_3805_: usize = 0;
    let mut v_res_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3804_ = leanh::lean_unbox_usize(v_sz_3801_);
    leanh::lean_dec(v_sz_3801_);
    v_i_boxed_3805_ = leanh::lean_unbox_usize(v_i_3802_);
    leanh::lean_dec(v_i_3802_);
    v_res_3806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_3799_, v_as_3800_, v_sz_boxed_3804_, v_i_boxed_3805_, v_b_3803_);
    leanh::lean_dec_ref(v_as_3800_);
    return v_res_3806_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray___redArg(
    mut v_a_3807_: *mut leanh::LeanObject,
    mut v_cmp_3808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3810_: usize = 0;
    let mut v___x_3811_: usize = 0;
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_3809_ = leanh::lean_box(1);
    v_sz_3810_ = lean_array_size(v_a_3807_);
    v___x_3811_ = 0usize;
    v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_3808_, v_a_3807_, v_sz_3810_, v___x_3811_, v_r_3809_);
    return v___x_3812_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray___redArg___boxed(
    mut v_a_3813_: *mut leanh::LeanObject,
    mut v_cmp_3814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3815_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_3813_, v_cmp_3814_);
    leanh::lean_dec_ref(v_a_3813_);
    return v_res_3815_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray(
    mut v_00_u03b1_3816_: *mut leanh::LeanObject,
    mut v_a_3817_: *mut leanh::LeanObject,
    mut v_cmp_3818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3819_ = l_Std_ExtTreeSet_ofArray___redArg(v_a_3817_, v_cmp_3818_);
    return v___x_3819_;
}
pub unsafe fn l_Std_ExtTreeSet_ofArray___boxed(
    mut v_00_u03b1_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_cmp_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Std_ExtTreeSet_ofArray(v_00_u03b1_3820_, v_a_3821_, v_cmp_3822_);
    leanh::lean_dec_ref(v_a_3821_);
    return v_res_3823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(
    mut v_00_u03b1_3824_: *mut leanh::LeanObject,
    mut v_cmp_3825_: *mut leanh::LeanObject,
    mut v_as_3826_: *mut leanh::LeanObject,
    mut v_sz_3827_: usize,
    mut v_i_3828_: usize,
    mut v_b_3829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___redArg(v_cmp_3825_, v_as_3826_, v_sz_3827_, v_i_3828_, v_b_3829_);
    return v___x_3830_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0___boxed(
    mut v_00_u03b1_3831_: *mut leanh::LeanObject,
    mut v_cmp_3832_: *mut leanh::LeanObject,
    mut v_as_3833_: *mut leanh::LeanObject,
    mut v_sz_3834_: *mut leanh::LeanObject,
    mut v_i_3835_: *mut leanh::LeanObject,
    mut v_b_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3837_: usize = 0;
    let mut v_i_boxed_3838_: usize = 0;
    let mut v_res_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3837_ = leanh::lean_unbox_usize(v_sz_3834_);
    leanh::lean_dec(v_sz_3834_);
    v_i_boxed_3838_ = leanh::lean_unbox_usize(v_i_3835_);
    leanh::lean_dec(v_i_3835_);
    v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_ExtTreeSet_ofArray_spec__0(v_00_u03b1_3831_, v_cmp_3832_, v_as_3833_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3836_);
    leanh::lean_dec_ref(v_as_3833_);
    return v_res_3839_;
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg___lam__0(
    mut v_b_u2082_3842_: *mut leanh::LeanObject,
    mut v_x_3843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3843_) == 0 {
        let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3844_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3844_, 0, v_b_u2082_3842_);
        return v___x_3844_;
    } else {
        let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3845_ = l_Std_ExtTreeSet_merge___redArg___lam__0___closed__0;
        return v___x_3845_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg___lam__0___boxed(
    mut v_b_u2082_3846_: *mut leanh::LeanObject,
    mut v_x_3847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3848_ = l_Std_ExtTreeSet_merge___redArg___lam__0(v_b_u2082_3846_, v_x_3847_);
    leanh::lean_dec(v_x_3847_);
    return v_res_3848_;
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg___lam__1(
    mut v_cmp_3849_: *mut leanh::LeanObject,
    mut v_t_3850_: *mut leanh::LeanObject,
    mut v_a_3851_: *mut leanh::LeanObject,
    mut v_b_u2082_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3853_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_merge___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3853_, 0, v_b_u2082_3852_);
    v___x_3854_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_3849_,
        v_a_3851_,
        v___f_3853_,
        v_t_3850_,
    );
    return v___x_3854_;
}
pub unsafe fn l_Std_ExtTreeSet_merge___redArg(
    mut v_cmp_3855_: *mut leanh::LeanObject,
    mut v_t_u2081_3856_: *mut leanh::LeanObject,
    mut v_t_u2082_3857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3858_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3858_, 0, v_cmp_3855_);
    v___x_3859_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3858_, v_t_u2081_3856_, v_t_u2082_3857_);
    return v___x_3859_;
}
pub unsafe fn l_Std_ExtTreeSet_merge(
    mut v_00_u03b1_3860_: *mut leanh::LeanObject,
    mut v_cmp_3861_: *mut leanh::LeanObject,
    mut v_inst_3862_: *mut leanh::LeanObject,
    mut v_t_u2081_3863_: *mut leanh::LeanObject,
    mut v_t_u2082_3864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3865_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3865_, 0, v_cmp_3861_);
    v___x_3866_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3865_, v_t_u2081_3863_, v_t_u2082_3864_);
    return v___x_3866_;
}
pub unsafe fn l_Std_ExtTreeSet_insertMany___redArg___lam__0(
    mut v_cmp_3867_: *mut leanh::LeanObject,
    mut v_a_3868_: *mut leanh::LeanObject,
    mut v_____s_3869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3870_: u8 = 0;
    leanh::lean_inc(v_____s_3869_);
    leanh::lean_inc(v_a_3868_);
    leanh::lean_inc_ref(v_cmp_3867_);
    v___x_3870_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3867_, v_a_3868_, v_____s_3869_);
    if v___x_3870_ == 0 {
        let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3871_ = leanh::lean_box(0);
        v___x_3872_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_3867_,
            v_a_3868_,
            v___x_3871_,
            v_____s_3869_,
        );
        v___x_3873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3873_, 0, v___x_3872_);
        return v___x_3873_;
    } else {
        let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3868_);
        leanh::lean_dec_ref(v_cmp_3867_);
        v___x_3874_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3874_, 0, v_____s_3869_);
        return v___x_3874_;
    }
}
pub unsafe fn l_Std_ExtTreeSet_insertMany___redArg(
    mut v_cmp_3875_: *mut leanh::LeanObject,
    mut v_inst_3876_: *mut leanh::LeanObject,
    mut v_t_3877_: *mut leanh::LeanObject,
    mut v_l_3878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3879_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3879_, 0, v_cmp_3875_);
    v___x_3880_ = leanh::lean_apply_4(
        v_inst_3876_,
        leanh::lean_box(0),
        v_l_3878_,
        v_t_3877_,
        v___f_3879_,
    );
    return v___x_3880_;
}
pub unsafe fn l_Std_ExtTreeSet_insertMany(
    mut v_00_u03b1_3881_: *mut leanh::LeanObject,
    mut v_cmp_3882_: *mut leanh::LeanObject,
    mut v_inst_3883_: *mut leanh::LeanObject,
    mut v_00_u03c1_3884_: *mut leanh::LeanObject,
    mut v_inst_3885_: *mut leanh::LeanObject,
    mut v_t_3886_: *mut leanh::LeanObject,
    mut v_l_3887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3888_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3888_, 0, v_cmp_3882_);
    v___x_3889_ = leanh::lean_apply_4(
        v_inst_3885_,
        leanh::lean_box(0),
        v_l_3887_,
        v_t_3886_,
        v___f_3888_,
    );
    return v___x_3889_;
}
pub unsafe fn l_Std_ExtTreeSet_union___redArg(
    mut v_cmp_3890_: *mut leanh::LeanObject,
    mut v_t_u2081_3891_: *mut leanh::LeanObject,
    mut v_t_u2082_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3893_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3890_,
        v_t_u2081_3891_,
        v_t_u2082_3892_,
    );
    return v___x_3893_;
}
pub unsafe fn l_Std_ExtTreeSet_union(
    mut v_00_u03b1_3894_: *mut leanh::LeanObject,
    mut v_cmp_3895_: *mut leanh::LeanObject,
    mut v_inst_3896_: *mut leanh::LeanObject,
    mut v_t_u2081_3897_: *mut leanh::LeanObject,
    mut v_t_u2082_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3895_,
        v_t_u2081_3897_,
        v_t_u2082_3898_,
    );
    return v___x_3899_;
}
pub unsafe fn l_Std_ExtTreeSet_instUnionOfTransCmp___redArg(
    mut v_cmp_3900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3901_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeSet_union as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_3901_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3901_, 1, v_cmp_3900_);
    leanh::lean_closure_set(v___x_3901_, 2, leanh::lean_box(0));
    return v___x_3901_;
}
pub unsafe fn l_Std_ExtTreeSet_instUnionOfTransCmp(
    mut v_00_u03b1_3902_: *mut leanh::LeanObject,
    mut v_cmp_3903_: *mut leanh::LeanObject,
    mut v_inst_3904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3905_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeSet_union as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_3905_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3905_, 1, v_cmp_3903_);
    leanh::lean_closure_set(v___x_3905_, 2, leanh::lean_box(0));
    return v___x_3905_;
}
pub unsafe fn l_Std_ExtTreeSet_inter___redArg(
    mut v_cmp_3906_: *mut leanh::LeanObject,
    mut v_t_u2081_3907_: *mut leanh::LeanObject,
    mut v_t_u2082_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3909_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3906_,
        v_t_u2081_3907_,
        v_t_u2082_3908_,
    );
    return v___x_3909_;
}
pub unsafe fn l_Std_ExtTreeSet_inter(
    mut v_00_u03b1_3910_: *mut leanh::LeanObject,
    mut v_cmp_3911_: *mut leanh::LeanObject,
    mut v_inst_3912_: *mut leanh::LeanObject,
    mut v_t_u2081_3913_: *mut leanh::LeanObject,
    mut v_t_u2082_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3915_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3911_,
        v_t_u2081_3913_,
        v_t_u2082_3914_,
    );
    return v___x_3915_;
}
pub unsafe fn l_Std_ExtTreeSet_instInterOfTransCmp___redArg(
    mut v_cmp_3916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3917_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeSet_inter as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_3917_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3917_, 1, v_cmp_3916_);
    leanh::lean_closure_set(v___x_3917_, 2, leanh::lean_box(0));
    return v___x_3917_;
}
pub unsafe fn l_Std_ExtTreeSet_instInterOfTransCmp(
    mut v_00_u03b1_3918_: *mut leanh::LeanObject,
    mut v_cmp_3919_: *mut leanh::LeanObject,
    mut v_inst_3920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3921_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeSet_inter as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_3921_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3921_, 1, v_cmp_3919_);
    leanh::lean_closure_set(v___x_3921_, 2, leanh::lean_box(0));
    return v___x_3921_;
}
pub unsafe fn _init_l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3922_ = leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3923_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3923_, 0, v___x_3922_);
    return v___f_3923_;
}
pub unsafe fn l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(
    mut v_cmp_3924_: *mut leanh::LeanObject,
    mut v_m_u2081_3925_: *mut leanh::LeanObject,
    mut v_m_u2082_3926_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    v___f_3927_ = leanh::lean_obj_once(
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
    mut v_cmp_3929_: *mut leanh::LeanObject,
    mut v_m_u2081_3930_: *mut leanh::LeanObject,
    mut v_m_u2082_3931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3932_: u8 = 0;
    let mut v_r_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3932_ = l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0(
        v_cmp_3929_,
        v_m_u2081_3930_,
        v_m_u2082_3931_,
    );
    v_r_3933_ = leanh::lean_box((v_res_3932_) as usize);
    return v_r_3933_;
}
pub unsafe fn l_Std_ExtTreeSet_instBEqOfTransCmp___redArg(
    mut v_cmp_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3935_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3935_, 0, v_cmp_3934_);
    return v___f_3935_;
}
pub unsafe fn l_Std_ExtTreeSet_instBEqOfTransCmp(
    mut v_00_u03b1_3936_: *mut leanh::LeanObject,
    mut v_cmp_3937_: *mut leanh::LeanObject,
    mut v_inst_3938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3939_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instBEqOfTransCmp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3939_, 0, v_cmp_3937_);
    return v___f_3939_;
}
pub unsafe fn l_Std_ExtTreeSet_diff___redArg(
    mut v_cmp_3940_: *mut leanh::LeanObject,
    mut v_t_u2081_3941_: *mut leanh::LeanObject,
    mut v_t_u2082_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_3940_,
        v_t_u2081_3941_,
        v_t_u2082_3942_,
    );
    return v___x_3943_;
}
pub unsafe fn l_Std_ExtTreeSet_diff(
    mut v_00_u03b1_3944_: *mut leanh::LeanObject,
    mut v_cmp_3945_: *mut leanh::LeanObject,
    mut v_inst_3946_: *mut leanh::LeanObject,
    mut v_t_u2081_3947_: *mut leanh::LeanObject,
    mut v_t_u2082_3948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3949_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_3945_,
        v_t_u2081_3947_,
        v_t_u2082_3948_,
    );
    return v___x_3949_;
}
pub unsafe fn l_Std_ExtTreeSet_instSDiffOfTransCmp___redArg(
    mut v_cmp_3950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeSet_diff as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_3951_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3951_, 1, v_cmp_3950_);
    leanh::lean_closure_set(v___x_3951_, 2, leanh::lean_box(0));
    return v___x_3951_;
}
pub unsafe fn l_Std_ExtTreeSet_instSDiffOfTransCmp(
    mut v_00_u03b1_3952_: *mut leanh::LeanObject,
    mut v_cmp_3953_: *mut leanh::LeanObject,
    mut v_inst_3954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeSet_diff as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_3955_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3955_, 1, v_cmp_3953_);
    leanh::lean_closure_set(v___x_3955_, 2, leanh::lean_box(0));
    return v___x_3955_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(
    mut v_cmp_3956_: *mut leanh::LeanObject,
    mut v_x_3957_: *mut leanh::LeanObject,
    mut v_x_3958_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: u8 = 0;
    v___f_3959_ = leanh::lean_obj_once(
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
    mut v_cmp_3961_: *mut leanh::LeanObject,
    mut v_x_3962_: *mut leanh::LeanObject,
    mut v_x_3963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3964_: u8 = 0;
    let mut v_r_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp___redArg(
        v_cmp_3961_,
        v_x_3962_,
        v_x_3963_,
    );
    v_r_3965_ = leanh::lean_box((v_res_3964_) as usize);
    return v_r_3965_;
}
pub unsafe fn l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(
    mut v_00_u03b1_3966_: *mut leanh::LeanObject,
    mut v_cmp_3967_: *mut leanh::LeanObject,
    mut v_inst_3968_: *mut leanh::LeanObject,
    mut v_inst_3969_: *mut leanh::LeanObject,
    mut v_x_3970_: *mut leanh::LeanObject,
    mut v_x_3971_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_3973_: *mut leanh::LeanObject,
    mut v_cmp_3974_: *mut leanh::LeanObject,
    mut v_inst_3975_: *mut leanh::LeanObject,
    mut v_inst_3976_: *mut leanh::LeanObject,
    mut v_x_3977_: *mut leanh::LeanObject,
    mut v_x_3978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3979_: u8 = 0;
    let mut v_r_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Std_ExtTreeSet_instDecidableEqOfLawfulEqCmpOfTransCmp(
        v_00_u03b1_3973_,
        v_cmp_3974_,
        v_inst_3975_,
        v_inst_3976_,
        v_x_3977_,
        v_x_3978_,
    );
    v_r_3980_ = leanh::lean_box((v_res_3979_) as usize);
    return v_r_3980_;
}
pub unsafe fn l_Std_ExtTreeSet_eraseMany___redArg___lam__0(
    mut v_cmp_3981_: *mut leanh::LeanObject,
    mut v_a_3982_: *mut leanh::LeanObject,
    mut v_____s_3983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_acc_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_acc_3984_ =
        l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3981_, v_a_3982_, v_____s_3983_);
    v___x_3985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3985_, 0, v_acc_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Std_ExtTreeSet_eraseMany___redArg(
    mut v_cmp_3986_: *mut leanh::LeanObject,
    mut v_inst_3987_: *mut leanh::LeanObject,
    mut v_t_3988_: *mut leanh::LeanObject,
    mut v_l_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3990_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3990_, 0, v_cmp_3986_);
    v___x_3991_ = leanh::lean_apply_4(
        v_inst_3987_,
        leanh::lean_box(0),
        v_l_3989_,
        v_t_3988_,
        v___f_3990_,
    );
    return v___x_3991_;
}
pub unsafe fn l_Std_ExtTreeSet_eraseMany(
    mut v_00_u03b1_3992_: *mut leanh::LeanObject,
    mut v_cmp_3993_: *mut leanh::LeanObject,
    mut v_inst_3994_: *mut leanh::LeanObject,
    mut v_00_u03c1_3995_: *mut leanh::LeanObject,
    mut v_inst_3996_: *mut leanh::LeanObject,
    mut v_t_3997_: *mut leanh::LeanObject,
    mut v_l_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3999_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3999_, 0, v_cmp_3993_);
    v___x_4000_ = leanh::lean_apply_4(
        v_inst_3996_,
        leanh::lean_box(0),
        v_l_3998_,
        v_t_3997_,
        v___f_3999_,
    );
    return v___x_4000_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(
    mut v___f_4004_: *mut leanh::LeanObject,
    mut v_inst_4005_: *mut leanh::LeanObject,
    mut v_m_4006_: *mut leanh::LeanObject,
    mut v_prec_4007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4008_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___closed__1;
    v___x_4009_ = leanh::lean_box(0);
    v___x_4010_ = l_Std_ExtTreeSet_foldr___redArg___closed__9;
    v___x_4011_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4010_,
        v___f_4004_,
        v___x_4009_,
        v_m_4006_,
    );
    v___x_4012_ = l_List_repr___redArg(v_inst_4005_, v___x_4011_);
    v___x_4013_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4013_, 0, v___x_4008_);
    leanh::lean_ctor_set(v___x_4013_, 1, v___x_4012_);
    v___x_4014_ = l_Repr_addAppParen(v___x_4013_, v_prec_4007_);
    return v___x_4014_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed(
    mut v___f_4015_: *mut leanh::LeanObject,
    mut v_inst_4016_: *mut leanh::LeanObject,
    mut v_m_4017_: *mut leanh::LeanObject,
    mut v_prec_4018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4019_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1(
        v___f_4015_,
        v_inst_4016_,
        v_m_4017_,
        v_prec_4018_,
    );
    leanh::lean_dec(v_prec_4018_);
    return v_res_4019_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___redArg(
    mut v_inst_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4021_ = l_Std_ExtTreeSet_toList___redArg___closed__0;
    v___f_4022_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeSet_instReprOfTransCmp___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4022_, 0, v___f_4021_);
    leanh::lean_closure_set(v___f_4022_, 1, v_inst_4020_);
    return v___f_4022_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp(
    mut v_00_u03b1_4023_: *mut leanh::LeanObject,
    mut v_cmp_4024_: *mut leanh::LeanObject,
    mut v_inst_4025_: *mut leanh::LeanObject,
    mut v_inst_4026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_Std_ExtTreeSet_instReprOfTransCmp___redArg(v_inst_4026_);
    return v___x_4027_;
}
pub unsafe fn l_Std_ExtTreeSet_instReprOfTransCmp___boxed(
    mut v_00_u03b1_4028_: *mut leanh::LeanObject,
    mut v_cmp_4029_: *mut leanh::LeanObject,
    mut v_inst_4030_: *mut leanh::LeanObject,
    mut v_inst_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4032_ = l_Std_ExtTreeSet_instReprOfTransCmp(
        v_00_u03b1_4028_,
        v_cmp_4029_,
        v_inst_4030_,
        v_inst_4031_,
    );
    leanh::lean_dec_ref(v_cmp_4029_);
    return v_res_4032_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtTreeSet_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtTreeSet_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_ExtTreeSet___auto__1 = _init_l_Std_ExtTreeSet___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeSet___auto__1);
    l_Std_ExtTreeSet_ofList___auto__1 = _init_l_Std_ExtTreeSet_ofList___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeSet_ofList___auto__1);
    l_Std_ExtTreeSet_ofArray___auto__1 = _init_l_Std_ExtTreeSet_ofArray___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeSet_ofArray___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ExtTreeSet_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtTreeSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtTreeSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_ExtTreeSet_Basic(builtin);
}