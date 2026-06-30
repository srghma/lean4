// Lean compiler output
// Module: Std.Data.ExtTreeMap.Basic
// Imports: Std.Data.ExtDTreeMap.Basic
use crate::ffi::{
    lean_array_push, lean_array_size, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_string_utf8_byte_size,
};
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
use crate::r#gen::Init::Prelude::{l_Lean_mkAtom, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_alter___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_beq___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_modify___redArg,
    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg,
    l_Std_DTreeMap_Internal_Impl_erase___redArg, l_Std_DTreeMap_Internal_Impl_filter___redArg,
    l_Std_DTreeMap_Internal_Impl_filterMap___redArg, l_Std_DTreeMap_Internal_Impl_insert___redArg,
    l_Std_DTreeMap_Internal_Impl_map___redArg,
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
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg,
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
use crate::r#gen::Std::Data::ExtDTreeMap::Basic::{
    initialize_Std_Data_ExtDTreeMap_Basic, runtime_initialize_Std_Data_ExtDTreeMap_Basic,
};
pub static l_Std_ExtTreeMap___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_ExtTreeMap___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeMap___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeMap___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtTreeMap___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__6_value: leanh::LeanStringObject<19> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Std_ExtTreeMap___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeMap___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeMap___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtTreeMap___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap___auto__1___closed__10_value: leanh::LeanStringObject<6> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Std_ExtTreeMap___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeMap___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtTreeMap___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtTreeMap___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeMap___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeMap___auto__1___closed__14_value: leanh::LeanStringObject<8> =
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
static mut l_Std_ExtTreeMap___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeMap___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeMap___auto__1___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16710690322389477741 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeMap___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtTreeMap___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_ExtTreeMap___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0_value:
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
static mut l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1_value:
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
static mut l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2_value:
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
static mut l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeMap_foldr___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtTreeMap_foldr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtTreeMap_foldr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtTreeMap_foldr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtTreeMap_foldr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtTreeMap_foldr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtTreeMap_foldr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtTreeMap_foldr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap_foldr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap_foldr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_foldr___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtTreeMap_foldr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_foldr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_partition___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_ExtTreeMap_partition___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_partition___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_any___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_ExtTreeMap_any___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_any___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_keys___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeMap_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeMap_keys___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_keys___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_keysArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_ExtTreeMap_keysArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_keysArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_values___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeMap_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeMap_values___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_values___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_ExtTreeMap_valuesArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_valuesArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeMap_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtTreeMap_ofList___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_ExtTreeMap_unitOfList___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeMap_toArray___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtTreeMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtTreeMap_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_toArray___redArg___closed__1_value: leanh::LeanArrayObject<0> =
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
static mut l_Std_ExtTreeMap_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtTreeMap_ofArray___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_ExtTreeMap_unitOfArray___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value:
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
        83, 116, 100, 46, 69, 120, 116, 84, 114, 101, 101, 77, 97, 112, 46, 111, 102, 76, 105, 115,
        116, 32, 0,
    ],
};
static mut l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value:
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
        l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2798_ = l_Std_ExtTreeMap___auto__1___closed__10;
    v___x_2799_ = l_Lean_mkAtom(v___x_2798_);
    return v___x_2799_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__12_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__12,
    );
    v___x_2801_ = l_Std_ExtTreeMap___auto__1___closed__5;
    v___x_2802_ = lean_array_push(v___x_2801_, v___x_2800_);
    return v___x_2802_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2804_ = l_Std_ExtTreeMap___auto__1___closed__14;
    v___x_2805_ = lean_string_utf8_byte_size(v___x_2804_);
    return v___x_2805_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2806_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__15_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__15,
    );
    v___x_2807_ = leanh::lean_unsigned_to_nat(0);
    v___x_2808_ = l_Std_ExtTreeMap___auto__1___closed__14;
    v___x_2809_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2809_, 0, v___x_2808_);
    leanh::lean_ctor_set(v___x_2809_, 1, v___x_2807_);
    leanh::lean_ctor_set(v___x_2809_, 2, v___x_2806_);
    return v___x_2809_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2812_ = leanh::lean_box(0);
    v___x_2813_ = l_Std_ExtTreeMap___auto__1___closed__17;
    v___x_2814_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__16_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__16,
    );
    v___x_2815_ = leanh::lean_box(2);
    v___x_2816_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2816_, 0, v___x_2815_);
    leanh::lean_ctor_set(v___x_2816_, 1, v___x_2814_);
    leanh::lean_ctor_set(v___x_2816_, 2, v___x_2813_);
    leanh::lean_ctor_set(v___x_2816_, 3, v___x_2812_);
    return v___x_2816_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__18_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__18,
    );
    v___x_2818_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__13_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__13,
    );
    v___x_2819_ = lean_array_push(v___x_2818_, v___x_2817_);
    return v___x_2819_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2820_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__19_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__19,
    );
    v___x_2821_ = l_Std_ExtTreeMap___auto__1___closed__11;
    v___x_2822_ = leanh::lean_box(2);
    v___x_2823_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2823_, 0, v___x_2822_);
    leanh::lean_ctor_set(v___x_2823_, 1, v___x_2821_);
    leanh::lean_ctor_set(v___x_2823_, 2, v___x_2820_);
    return v___x_2823_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__20_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__20,
    );
    v___x_2825_ = l_Std_ExtTreeMap___auto__1___closed__5;
    v___x_2826_ = lean_array_push(v___x_2825_, v___x_2824_);
    return v___x_2826_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__21_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__21,
    );
    v___x_2828_ = l_Std_ExtTreeMap___auto__1___closed__9;
    v___x_2829_ = leanh::lean_box(2);
    v___x_2830_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2830_, 0, v___x_2829_);
    leanh::lean_ctor_set(v___x_2830_, 1, v___x_2828_);
    leanh::lean_ctor_set(v___x_2830_, 2, v___x_2827_);
    return v___x_2830_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__22_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__22,
    );
    v___x_2832_ = l_Std_ExtTreeMap___auto__1___closed__5;
    v___x_2833_ = lean_array_push(v___x_2832_, v___x_2831_);
    return v___x_2833_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2834_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__23_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__23,
    );
    v___x_2835_ = l_Std_ExtTreeMap___auto__1___closed__7;
    v___x_2836_ = leanh::lean_box(2);
    v___x_2837_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2837_, 0, v___x_2836_);
    leanh::lean_ctor_set(v___x_2837_, 1, v___x_2835_);
    leanh::lean_ctor_set(v___x_2837_, 2, v___x_2834_);
    return v___x_2837_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__24_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__24,
    );
    v___x_2839_ = l_Std_ExtTreeMap___auto__1___closed__5;
    v___x_2840_ = lean_array_push(v___x_2839_, v___x_2838_);
    return v___x_2840_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__25_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__25,
    );
    v___x_2842_ = l_Std_ExtTreeMap___auto__1___closed__4;
    v___x_2843_ = leanh::lean_box(2);
    v___x_2844_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2844_, 0, v___x_2843_);
    leanh::lean_ctor_set(v___x_2844_, 1, v___x_2842_);
    leanh::lean_ctor_set(v___x_2844_, 2, v___x_2841_);
    return v___x_2844_;
}
pub unsafe fn _init_l_Std_ExtTreeMap___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2845_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__26,
    );
    return v___x_2845_;
}
pub unsafe fn l_Std_ExtTreeMap_empty(
    mut v_00_u03b1_2846_: *mut leanh::LeanObject,
    mut v_00_u03b2_2847_: *mut leanh::LeanObject,
    mut v_cmp_2848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2849_ = leanh::lean_box(1);
    return v___x_2849_;
}
pub unsafe fn l_Std_ExtTreeMap_empty___boxed(
    mut v_00_u03b1_2850_: *mut leanh::LeanObject,
    mut v_00_u03b2_2851_: *mut leanh::LeanObject,
    mut v_cmp_2852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2853_ = l_Std_ExtTreeMap_empty(v_00_u03b1_2850_, v_00_u03b2_2851_, v_cmp_2852_);
    leanh::lean_dec_ref(v_cmp_2852_);
    return v_res_2853_;
}
pub unsafe fn l_Std_ExtTreeMap_instEmptyCollection(
    mut v_00_u03b1_2854_: *mut leanh::LeanObject,
    mut v_00_u03b2_2855_: *mut leanh::LeanObject,
    mut v_cmp_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2857_ = leanh::lean_box(1);
    return v___x_2857_;
}
pub unsafe fn l_Std_ExtTreeMap_instEmptyCollection___boxed(
    mut v_00_u03b1_2858_: *mut leanh::LeanObject,
    mut v_00_u03b2_2859_: *mut leanh::LeanObject,
    mut v_cmp_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2861_ =
        l_Std_ExtTreeMap_instEmptyCollection(v_00_u03b1_2858_, v_00_u03b2_2859_, v_cmp_2860_);
    leanh::lean_dec_ref(v_cmp_2860_);
    return v_res_2861_;
}
pub unsafe fn l_Std_ExtTreeMap_instInhabited(
    mut v_00_u03b1_2862_: *mut leanh::LeanObject,
    mut v_00_u03b2_2863_: *mut leanh::LeanObject,
    mut v_cmp_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = leanh::lean_box(1);
    return v___x_2865_;
}
pub unsafe fn l_Std_ExtTreeMap_instInhabited___boxed(
    mut v_00_u03b1_2866_: *mut leanh::LeanObject,
    mut v_00_u03b2_2867_: *mut leanh::LeanObject,
    mut v_cmp_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l_Std_ExtTreeMap_instInhabited(v_00_u03b1_2866_, v_00_u03b2_2867_, v_cmp_2868_);
    leanh::lean_dec_ref(v_cmp_2868_);
    return v_res_2869_;
}
pub unsafe fn l_Std_ExtTreeMap_insert___redArg(
    mut v_cmp_2870_: *mut leanh::LeanObject,
    mut v_l_2871_: *mut leanh::LeanObject,
    mut v_a_2872_: *mut leanh::LeanObject,
    mut v_b_2873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2874_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2870_, v_a_2872_, v_b_2873_, v_l_2871_);
    return v___x_2874_;
}
pub unsafe fn l_Std_ExtTreeMap_insert(
    mut v_00_u03b1_2875_: *mut leanh::LeanObject,
    mut v_00_u03b2_2876_: *mut leanh::LeanObject,
    mut v_cmp_2877_: *mut leanh::LeanObject,
    mut v_inst_2878_: *mut leanh::LeanObject,
    mut v_l_2879_: *mut leanh::LeanObject,
    mut v_a_2880_: *mut leanh::LeanObject,
    mut v_b_2881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2877_, v_a_2880_, v_b_2881_, v_l_2879_);
    return v___x_2882_;
}
pub unsafe fn l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0(
    mut v_cmp_2883_: *mut leanh::LeanObject,
    mut v_e_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2885_ = leanh::lean_ctor_get(v_e_2884_, 0);
    leanh::lean_inc(v_fst_2885_);
    v_snd_2886_ = leanh::lean_ctor_get(v_e_2884_, 1);
    leanh::lean_inc(v_snd_2886_);
    leanh::lean_dec_ref(v_e_2884_);
    v___x_2887_ = leanh::lean_box(1);
    v___x_2888_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_2883_,
        v_fst_2885_,
        v_snd_2886_,
        v___x_2887_,
    );
    return v___x_2888_;
}
pub unsafe fn l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg(
    mut v_cmp_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2890_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2890_, 0, v_cmp_2889_);
    return v___f_2890_;
}
pub unsafe fn l_Std_ExtTreeMap_instSingletonProdOfTransCmp(
    mut v_00_u03b1_2891_: *mut leanh::LeanObject,
    mut v_00_u03b2_2892_: *mut leanh::LeanObject,
    mut v_cmp_2893_: *mut leanh::LeanObject,
    mut v_inst_2894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2895_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instSingletonProdOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2895_, 0, v_cmp_2893_);
    return v___f_2895_;
}
pub unsafe fn l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0(
    mut v_cmp_2896_: *mut leanh::LeanObject,
    mut v_e_2897_: *mut leanh::LeanObject,
    mut v_s_2898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2899_ = leanh::lean_ctor_get(v_e_2897_, 0);
    leanh::lean_inc(v_fst_2899_);
    v_snd_2900_ = leanh::lean_ctor_get(v_e_2897_, 1);
    leanh::lean_inc(v_snd_2900_);
    leanh::lean_dec_ref(v_e_2897_);
    v___x_2901_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_2896_,
        v_fst_2899_,
        v_snd_2900_,
        v_s_2898_,
    );
    return v___x_2901_;
}
pub unsafe fn l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg(
    mut v_cmp_2902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2903_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2903_, 0, v_cmp_2902_);
    return v___f_2903_;
}
pub unsafe fn l_Std_ExtTreeMap_instInsertProdOfTransCmp(
    mut v_00_u03b1_2904_: *mut leanh::LeanObject,
    mut v_00_u03b2_2905_: *mut leanh::LeanObject,
    mut v_cmp_2906_: *mut leanh::LeanObject,
    mut v_inst_2907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2908_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instInsertProdOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2908_, 0, v_cmp_2906_);
    return v___f_2908_;
}
pub unsafe fn l_Std_ExtTreeMap_insertIfNew___redArg(
    mut v_cmp_2909_: *mut leanh::LeanObject,
    mut v_t_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
    mut v_b_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2913_: u8 = 0;
    leanh::lean_inc(v_t_2910_);
    leanh::lean_inc(v_a_2911_);
    leanh::lean_inc_ref(v_cmp_2909_);
    v___x_2913_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2909_, v_a_2911_, v_t_2910_);
    if v___x_2913_ == 0 {
        let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2914_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2909_,
            v_a_2911_,
            v_b_2912_,
            v_t_2910_,
        );
        return v___x_2914_;
    } else {
        leanh::lean_dec(v_b_2912_);
        leanh::lean_dec(v_a_2911_);
        leanh::lean_dec_ref(v_cmp_2909_);
        return v_t_2910_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_insertIfNew(
    mut v_00_u03b1_2915_: *mut leanh::LeanObject,
    mut v_00_u03b2_2916_: *mut leanh::LeanObject,
    mut v_cmp_2917_: *mut leanh::LeanObject,
    mut v_inst_2918_: *mut leanh::LeanObject,
    mut v_t_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
    mut v_b_2921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2922_: u8 = 0;
    leanh::lean_inc(v_t_2919_);
    leanh::lean_inc(v_a_2920_);
    leanh::lean_inc_ref(v_cmp_2917_);
    v___x_2922_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2917_, v_a_2920_, v_t_2919_);
    if v___x_2922_ == 0 {
        let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2923_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2917_,
            v_a_2920_,
            v_b_2921_,
            v_t_2919_,
        );
        return v___x_2923_;
    } else {
        leanh::lean_dec(v_b_2921_);
        leanh::lean_dec(v_a_2920_);
        leanh::lean_dec_ref(v_cmp_2917_);
        return v_t_2919_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_containsThenInsert___redArg(
    mut v_cmp_2924_: *mut leanh::LeanObject,
    mut v_t_2925_: *mut leanh::LeanObject,
    mut v_a_2926_: *mut leanh::LeanObject,
    mut v_b_2927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: u8 = 0;
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2928_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_2925_);
                v_m_2929_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_2924_,
                    v_a_2926_,
                    v_b_2927_,
                    v_t_2925_,
                );
                if leanh::lean_obj_tag(v_m_2929_) == 0 {
                    v_size_2935_ = leanh::lean_ctor_get(v_m_2929_, 0);
                    leanh::lean_inc(v_size_2935_);
                    v___y_2931_ = v_size_2935_;
                    state = 1;
                    continue;
                } else {
                    v___x_2936_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2931_ = v___x_2936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2932_ = lean_nat_dec_eq(v_sz_2928_, v___y_2931_);
                leanh::lean_dec(v___y_2931_);
                leanh::lean_dec(v_sz_2928_);
                v___x_2933_ = leanh::lean_box((v___x_2932_) as usize);
                v___x_2934_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2934_, 0, v___x_2933_);
                leanh::lean_ctor_set(v___x_2934_, 1, v_m_2929_);
                return v___x_2934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_containsThenInsert(
    mut v_00_u03b1_2937_: *mut leanh::LeanObject,
    mut v_00_u03b2_2938_: *mut leanh::LeanObject,
    mut v_cmp_2939_: *mut leanh::LeanObject,
    mut v_inst_2940_: *mut leanh::LeanObject,
    mut v_t_2941_: *mut leanh::LeanObject,
    mut v_a_2942_: *mut leanh::LeanObject,
    mut v_b_2943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2944_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_2941_);
                v_m_2945_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_2939_,
                    v_a_2942_,
                    v_b_2943_,
                    v_t_2941_,
                );
                if leanh::lean_obj_tag(v_m_2945_) == 0 {
                    v_size_2951_ = leanh::lean_ctor_get(v_m_2945_, 0);
                    leanh::lean_inc(v_size_2951_);
                    v___y_2947_ = v_size_2951_;
                    state = 1;
                    continue;
                } else {
                    v___x_2952_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2947_ = v___x_2952_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2948_ = lean_nat_dec_eq(v_sz_2944_, v___y_2947_);
                leanh::lean_dec(v___y_2947_);
                leanh::lean_dec(v_sz_2944_);
                v___x_2949_ = leanh::lean_box((v___x_2948_) as usize);
                v___x_2950_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2950_, 0, v___x_2949_);
                leanh::lean_ctor_set(v___x_2950_, 1, v_m_2945_);
                return v___x_2950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_containsThenInsertIfNew___redArg(
    mut v_cmp_2953_: *mut leanh::LeanObject,
    mut v_t_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_b_2956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2957_: u8 = 0;
    leanh::lean_inc(v_t_2954_);
    leanh::lean_inc(v_a_2955_);
    leanh::lean_inc_ref(v_cmp_2953_);
    v___x_2957_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2953_, v_a_2955_, v_t_2954_);
    if v___x_2957_ == 0 {
        let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2958_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2953_,
            v_a_2955_,
            v_b_2956_,
            v_t_2954_,
        );
        v___x_2959_ = leanh::lean_box((v___x_2957_) as usize);
        v___x_2960_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2960_, 0, v___x_2959_);
        leanh::lean_ctor_set(v___x_2960_, 1, v___x_2958_);
        return v___x_2960_;
    } else {
        let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_2956_);
        leanh::lean_dec(v_a_2955_);
        leanh::lean_dec_ref(v_cmp_2953_);
        v___x_2961_ = leanh::lean_box((v___x_2957_) as usize);
        v___x_2962_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2962_, 0, v___x_2961_);
        leanh::lean_ctor_set(v___x_2962_, 1, v_t_2954_);
        return v___x_2962_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_containsThenInsertIfNew(
    mut v_00_u03b1_2963_: *mut leanh::LeanObject,
    mut v_00_u03b2_2964_: *mut leanh::LeanObject,
    mut v_cmp_2965_: *mut leanh::LeanObject,
    mut v_inst_2966_: *mut leanh::LeanObject,
    mut v_t_2967_: *mut leanh::LeanObject,
    mut v_a_2968_: *mut leanh::LeanObject,
    mut v_b_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2970_: u8 = 0;
    leanh::lean_inc(v_t_2967_);
    leanh::lean_inc(v_a_2968_);
    leanh::lean_inc_ref(v_cmp_2965_);
    v___x_2970_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2965_, v_a_2968_, v_t_2967_);
    if v___x_2970_ == 0 {
        let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2971_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2965_,
            v_a_2968_,
            v_b_2969_,
            v_t_2967_,
        );
        v___x_2972_ = leanh::lean_box((v___x_2970_) as usize);
        v___x_2973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2973_, 0, v___x_2972_);
        leanh::lean_ctor_set(v___x_2973_, 1, v___x_2971_);
        return v___x_2973_;
    } else {
        let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_2969_);
        leanh::lean_dec(v_a_2968_);
        leanh::lean_dec_ref(v_cmp_2965_);
        v___x_2974_ = leanh::lean_box((v___x_2970_) as usize);
        v___x_2975_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2975_, 0, v___x_2974_);
        leanh::lean_ctor_set(v___x_2975_, 1, v_t_2967_);
        return v___x_2975_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getThenInsertIfNew_x3f___redArg(
    mut v_cmp_2976_: *mut leanh::LeanObject,
    mut v_t_2977_: *mut leanh::LeanObject,
    mut v_a_2978_: *mut leanh::LeanObject,
    mut v_b_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2978_);
    leanh::lean_inc(v_t_2977_);
    leanh::lean_inc_ref(v_cmp_2976_);
    v___x_2980_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2976_, v_t_2977_, v_a_2978_);
    if leanh::lean_obj_tag(v___x_2980_) == 0 {
        let mut v___x_2981_: u8 = 0;
        leanh::lean_inc(v_t_2977_);
        leanh::lean_inc(v_a_2978_);
        leanh::lean_inc_ref(v_cmp_2976_);
        v___x_2981_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2976_, v_a_2978_, v_t_2977_);
        if v___x_2981_ == 0 {
            let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2982_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_2976_,
                v_a_2978_,
                v_b_2979_,
                v_t_2977_,
            );
            v___x_2983_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2983_, 0, v___x_2980_);
            leanh::lean_ctor_set(v___x_2983_, 1, v___x_2982_);
            return v___x_2983_;
        } else {
            let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_2979_);
            leanh::lean_dec(v_a_2978_);
            leanh::lean_dec_ref(v_cmp_2976_);
            v___x_2984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2984_, 0, v___x_2980_);
            leanh::lean_ctor_set(v___x_2984_, 1, v_t_2977_);
            return v___x_2984_;
        }
    } else {
        let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_2979_);
        leanh::lean_dec(v_a_2978_);
        leanh::lean_dec_ref(v_cmp_2976_);
        v___x_2985_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2985_, 0, v___x_2980_);
        leanh::lean_ctor_set(v___x_2985_, 1, v_t_2977_);
        return v___x_2985_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2986_: *mut leanh::LeanObject,
    mut v_00_u03b2_2987_: *mut leanh::LeanObject,
    mut v_cmp_2988_: *mut leanh::LeanObject,
    mut v_inst_2989_: *mut leanh::LeanObject,
    mut v_t_2990_: *mut leanh::LeanObject,
    mut v_a_2991_: *mut leanh::LeanObject,
    mut v_b_2992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2991_);
    leanh::lean_inc(v_t_2990_);
    leanh::lean_inc_ref(v_cmp_2988_);
    v___x_2993_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2988_, v_t_2990_, v_a_2991_);
    if leanh::lean_obj_tag(v___x_2993_) == 0 {
        let mut v___x_2994_: u8 = 0;
        leanh::lean_inc(v_t_2990_);
        leanh::lean_inc(v_a_2991_);
        leanh::lean_inc_ref(v_cmp_2988_);
        v___x_2994_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2988_, v_a_2991_, v_t_2990_);
        if v___x_2994_ == 0 {
            let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2995_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_2988_,
                v_a_2991_,
                v_b_2992_,
                v_t_2990_,
            );
            v___x_2996_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2996_, 0, v___x_2993_);
            leanh::lean_ctor_set(v___x_2996_, 1, v___x_2995_);
            return v___x_2996_;
        } else {
            let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_2992_);
            leanh::lean_dec(v_a_2991_);
            leanh::lean_dec_ref(v_cmp_2988_);
            v___x_2997_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2997_, 0, v___x_2993_);
            leanh::lean_ctor_set(v___x_2997_, 1, v_t_2990_);
            return v___x_2997_;
        }
    } else {
        let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_2992_);
        leanh::lean_dec(v_a_2991_);
        leanh::lean_dec_ref(v_cmp_2988_);
        v___x_2998_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2998_, 0, v___x_2993_);
        leanh::lean_ctor_set(v___x_2998_, 1, v_t_2990_);
        return v___x_2998_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_contains___redArg(
    mut v_cmp_2999_: *mut leanh::LeanObject,
    mut v_l_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3002_: u8 = 0;
    v___x_3002_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2999_, v_a_3001_, v_l_3000_);
    return v___x_3002_;
}
pub unsafe fn l_Std_ExtTreeMap_contains___redArg___boxed(
    mut v_cmp_3003_: *mut leanh::LeanObject,
    mut v_l_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3006_: u8 = 0;
    let mut v_r_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_Std_ExtTreeMap_contains___redArg(v_cmp_3003_, v_l_3004_, v_a_3005_);
    v_r_3007_ = leanh::lean_box((v_res_3006_) as usize);
    return v_r_3007_;
}
pub unsafe fn l_Std_ExtTreeMap_contains(
    mut v_00_u03b1_3008_: *mut leanh::LeanObject,
    mut v_00_u03b2_3009_: *mut leanh::LeanObject,
    mut v_cmp_3010_: *mut leanh::LeanObject,
    mut v_inst_3011_: *mut leanh::LeanObject,
    mut v_l_3012_: *mut leanh::LeanObject,
    mut v_a_3013_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3014_: u8 = 0;
    v___x_3014_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3010_, v_a_3013_, v_l_3012_);
    return v___x_3014_;
}
pub unsafe fn l_Std_ExtTreeMap_contains___boxed(
    mut v_00_u03b1_3015_: *mut leanh::LeanObject,
    mut v_00_u03b2_3016_: *mut leanh::LeanObject,
    mut v_cmp_3017_: *mut leanh::LeanObject,
    mut v_inst_3018_: *mut leanh::LeanObject,
    mut v_l_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3021_: u8 = 0;
    let mut v_r_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Std_ExtTreeMap_contains(
        v_00_u03b1_3015_,
        v_00_u03b2_3016_,
        v_cmp_3017_,
        v_inst_3018_,
        v_l_3019_,
        v_a_3020_,
    );
    v_r_3022_ = leanh::lean_box((v_res_3021_) as usize);
    return v_r_3022_;
}
pub unsafe fn l_Std_ExtTreeMap_instMembershipOfTransCmp(
    mut v_00_u03b1_3023_: *mut leanh::LeanObject,
    mut v_00_u03b2_3024_: *mut leanh::LeanObject,
    mut v_cmp_3025_: *mut leanh::LeanObject,
    mut v_inst_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = leanh::lean_box(0);
    return v___x_3027_;
}
pub unsafe fn l_Std_ExtTreeMap_instMembershipOfTransCmp___boxed(
    mut v_00_u03b1_3028_: *mut leanh::LeanObject,
    mut v_00_u03b2_3029_: *mut leanh::LeanObject,
    mut v_cmp_3030_: *mut leanh::LeanObject,
    mut v_inst_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3032_ = l_Std_ExtTreeMap_instMembershipOfTransCmp(
        v_00_u03b1_3028_,
        v_00_u03b2_3029_,
        v_cmp_3030_,
        v_inst_3031_,
    );
    leanh::lean_dec_ref(v_cmp_3030_);
    return v_res_3032_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableMem___redArg(
    mut v_cmp_3033_: *mut leanh::LeanObject,
    mut v_m_3034_: *mut leanh::LeanObject,
    mut v_a_3035_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3036_: u8 = 0;
    v___x_3036_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3033_, v_a_3035_, v_m_3034_);
    return v___x_3036_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableMem___redArg___boxed(
    mut v_cmp_3037_: *mut leanh::LeanObject,
    mut v_m_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3040_: u8 = 0;
    let mut v_r_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Std_ExtTreeMap_instDecidableMem___redArg(v_cmp_3037_, v_m_3038_, v_a_3039_);
    v_r_3041_ = leanh::lean_box((v_res_3040_) as usize);
    return v_r_3041_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableMem(
    mut v_00_u03b1_3042_: *mut leanh::LeanObject,
    mut v_00_u03b2_3043_: *mut leanh::LeanObject,
    mut v_cmp_3044_: *mut leanh::LeanObject,
    mut v_inst_3045_: *mut leanh::LeanObject,
    mut v_m_3046_: *mut leanh::LeanObject,
    mut v_a_3047_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3048_: u8 = 0;
    v___x_3048_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3044_, v_a_3047_, v_m_3046_);
    return v___x_3048_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableMem___boxed(
    mut v_00_u03b1_3049_: *mut leanh::LeanObject,
    mut v_00_u03b2_3050_: *mut leanh::LeanObject,
    mut v_cmp_3051_: *mut leanh::LeanObject,
    mut v_inst_3052_: *mut leanh::LeanObject,
    mut v_m_3053_: *mut leanh::LeanObject,
    mut v_a_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3055_: u8 = 0;
    let mut v_r_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ = l_Std_ExtTreeMap_instDecidableMem(
        v_00_u03b1_3049_,
        v_00_u03b2_3050_,
        v_cmp_3051_,
        v_inst_3052_,
        v_m_3053_,
        v_a_3054_,
    );
    v_r_3056_ = leanh::lean_box((v_res_3055_) as usize);
    return v_r_3056_;
}
pub unsafe fn l_Std_ExtTreeMap_size___redArg(
    mut v_t_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_3057_) == 0 {
        let mut v_size_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_size_3058_ = leanh::lean_ctor_get(v_t_3057_, 0);
        leanh::lean_inc(v_size_3058_);
        return v_size_3058_;
    } else {
        let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3059_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3059_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_size___redArg___boxed(
    mut v_t_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Std_ExtTreeMap_size___redArg(v_t_3060_);
    leanh::lean_dec(v_t_3060_);
    return v_res_3061_;
}
pub unsafe fn l_Std_ExtTreeMap_size(
    mut v_00_u03b1_3062_: *mut leanh::LeanObject,
    mut v_00_u03b2_3063_: *mut leanh::LeanObject,
    mut v_cmp_3064_: *mut leanh::LeanObject,
    mut v_t_3065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_3065_) == 0 {
        let mut v_size_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_size_3066_ = leanh::lean_ctor_get(v_t_3065_, 0);
        leanh::lean_inc(v_size_3066_);
        return v_size_3066_;
    } else {
        let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3067_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3067_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_size___boxed(
    mut v_00_u03b1_3068_: *mut leanh::LeanObject,
    mut v_00_u03b2_3069_: *mut leanh::LeanObject,
    mut v_cmp_3070_: *mut leanh::LeanObject,
    mut v_t_3071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3072_ = l_Std_ExtTreeMap_size(v_00_u03b1_3068_, v_00_u03b2_3069_, v_cmp_3070_, v_t_3071_);
    leanh::lean_dec(v_t_3071_);
    leanh::lean_dec_ref(v_cmp_3070_);
    return v_res_3072_;
}
pub unsafe fn l_Std_ExtTreeMap_isEmpty___redArg(
    mut v_t_3073_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_t_3073_) == 0 {
        let mut v___x_3074_: u8 = 0;
        v___x_3074_ = 0;
        return v___x_3074_;
    } else {
        let mut v___x_3075_: u8 = 0;
        v___x_3075_ = 1;
        return v___x_3075_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_isEmpty___redArg___boxed(
    mut v_t_3076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3077_: u8 = 0;
    let mut v_r_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3077_ = l_Std_ExtTreeMap_isEmpty___redArg(v_t_3076_);
    leanh::lean_dec(v_t_3076_);
    v_r_3078_ = leanh::lean_box((v_res_3077_) as usize);
    return v_r_3078_;
}
pub unsafe fn l_Std_ExtTreeMap_isEmpty(
    mut v_00_u03b1_3079_: *mut leanh::LeanObject,
    mut v_00_u03b2_3080_: *mut leanh::LeanObject,
    mut v_cmp_3081_: *mut leanh::LeanObject,
    mut v_t_3082_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_t_3082_) == 0 {
        let mut v___x_3083_: u8 = 0;
        v___x_3083_ = 0;
        return v___x_3083_;
    } else {
        let mut v___x_3084_: u8 = 0;
        v___x_3084_ = 1;
        return v___x_3084_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_isEmpty___boxed(
    mut v_00_u03b1_3085_: *mut leanh::LeanObject,
    mut v_00_u03b2_3086_: *mut leanh::LeanObject,
    mut v_cmp_3087_: *mut leanh::LeanObject,
    mut v_t_3088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3089_: u8 = 0;
    let mut v_r_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3089_ =
        l_Std_ExtTreeMap_isEmpty(v_00_u03b1_3085_, v_00_u03b2_3086_, v_cmp_3087_, v_t_3088_);
    leanh::lean_dec(v_t_3088_);
    leanh::lean_dec_ref(v_cmp_3087_);
    v_r_3090_ = leanh::lean_box((v_res_3089_) as usize);
    return v_r_3090_;
}
pub unsafe fn l_Std_ExtTreeMap_erase___redArg(
    mut v_cmp_3091_: *mut leanh::LeanObject,
    mut v_t_3092_: *mut leanh::LeanObject,
    mut v_a_3093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3094_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3091_, v_a_3093_, v_t_3092_);
    return v___x_3094_;
}
pub unsafe fn l_Std_ExtTreeMap_erase(
    mut v_00_u03b1_3095_: *mut leanh::LeanObject,
    mut v_00_u03b2_3096_: *mut leanh::LeanObject,
    mut v_cmp_3097_: *mut leanh::LeanObject,
    mut v_inst_3098_: *mut leanh::LeanObject,
    mut v_t_3099_: *mut leanh::LeanObject,
    mut v_a_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_3097_, v_a_3100_, v_t_3099_);
    return v___x_3101_;
}
pub unsafe fn l_Std_ExtTreeMap_get_x3f___redArg(
    mut v_cmp_3102_: *mut leanh::LeanObject,
    mut v_t_3103_: *mut leanh::LeanObject,
    mut v_a_3104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_3102_, v_t_3103_, v_a_3104_);
    return v___x_3105_;
}
pub unsafe fn l_Std_ExtTreeMap_get_x3f(
    mut v_00_u03b1_3106_: *mut leanh::LeanObject,
    mut v_00_u03b2_3107_: *mut leanh::LeanObject,
    mut v_cmp_3108_: *mut leanh::LeanObject,
    mut v_inst_3109_: *mut leanh::LeanObject,
    mut v_t_3110_: *mut leanh::LeanObject,
    mut v_a_3111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3112_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_3108_, v_t_3110_, v_a_3111_);
    return v___x_3112_;
}
pub unsafe fn l_Std_ExtTreeMap_get___redArg(
    mut v_cmp_3113_: *mut leanh::LeanObject,
    mut v_t_3114_: *mut leanh::LeanObject,
    mut v_a_3115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_3113_, v_t_3114_, v_a_3115_);
    return v___x_3116_;
}
pub unsafe fn l_Std_ExtTreeMap_get(
    mut v_00_u03b1_3117_: *mut leanh::LeanObject,
    mut v_00_u03b2_3118_: *mut leanh::LeanObject,
    mut v_cmp_3119_: *mut leanh::LeanObject,
    mut v_inst_3120_: *mut leanh::LeanObject,
    mut v_t_3121_: *mut leanh::LeanObject,
    mut v_a_3122_: *mut leanh::LeanObject,
    mut v_h_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3124_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_3119_, v_t_3121_, v_a_3122_);
    return v___x_3124_;
}
pub unsafe fn l_Std_ExtTreeMap_get_x21___redArg(
    mut v_cmp_3125_: *mut leanh::LeanObject,
    mut v_inst_3126_: *mut leanh::LeanObject,
    mut v_t_3127_: *mut leanh::LeanObject,
    mut v_a_3128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_3125_,
        v_inst_3126_,
        v_t_3127_,
        v_a_3128_,
    );
    return v___x_3129_;
}
pub unsafe fn l_Std_ExtTreeMap_get_x21___redArg___boxed(
    mut v_cmp_3130_: *mut leanh::LeanObject,
    mut v_inst_3131_: *mut leanh::LeanObject,
    mut v_t_3132_: *mut leanh::LeanObject,
    mut v_a_3133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3134_ =
        l_Std_ExtTreeMap_get_x21___redArg(v_cmp_3130_, v_inst_3131_, v_t_3132_, v_a_3133_);
    leanh::lean_dec(v_inst_3131_);
    return v_res_3134_;
}
pub unsafe fn l_Std_ExtTreeMap_get_x21(
    mut v_00_u03b1_3135_: *mut leanh::LeanObject,
    mut v_00_u03b2_3136_: *mut leanh::LeanObject,
    mut v_cmp_3137_: *mut leanh::LeanObject,
    mut v_inst_3138_: *mut leanh::LeanObject,
    mut v_inst_3139_: *mut leanh::LeanObject,
    mut v_t_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_3137_,
        v_inst_3139_,
        v_t_3140_,
        v_a_3141_,
    );
    return v___x_3142_;
}
pub unsafe fn l_Std_ExtTreeMap_get_x21___boxed(
    mut v_00_u03b1_3143_: *mut leanh::LeanObject,
    mut v_00_u03b2_3144_: *mut leanh::LeanObject,
    mut v_cmp_3145_: *mut leanh::LeanObject,
    mut v_inst_3146_: *mut leanh::LeanObject,
    mut v_inst_3147_: *mut leanh::LeanObject,
    mut v_t_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3150_ = l_Std_ExtTreeMap_get_x21(
        v_00_u03b1_3143_,
        v_00_u03b2_3144_,
        v_cmp_3145_,
        v_inst_3146_,
        v_inst_3147_,
        v_t_3148_,
        v_a_3149_,
    );
    leanh::lean_dec(v_inst_3147_);
    return v_res_3150_;
}
pub unsafe fn l_Std_ExtTreeMap_getD___redArg(
    mut v_cmp_3151_: *mut leanh::LeanObject,
    mut v_t_3152_: *mut leanh::LeanObject,
    mut v_a_3153_: *mut leanh::LeanObject,
    mut v_fallback_3154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_3151_,
        v_t_3152_,
        v_a_3153_,
        v_fallback_3154_,
    );
    return v___x_3155_;
}
pub unsafe fn l_Std_ExtTreeMap_getD___redArg___boxed(
    mut v_cmp_3156_: *mut leanh::LeanObject,
    mut v_t_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
    mut v_fallback_3159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3160_ =
        l_Std_ExtTreeMap_getD___redArg(v_cmp_3156_, v_t_3157_, v_a_3158_, v_fallback_3159_);
    leanh::lean_dec(v_fallback_3159_);
    return v_res_3160_;
}
pub unsafe fn l_Std_ExtTreeMap_getD(
    mut v_00_u03b1_3161_: *mut leanh::LeanObject,
    mut v_00_u03b2_3162_: *mut leanh::LeanObject,
    mut v_cmp_3163_: *mut leanh::LeanObject,
    mut v_inst_3164_: *mut leanh::LeanObject,
    mut v_t_3165_: *mut leanh::LeanObject,
    mut v_a_3166_: *mut leanh::LeanObject,
    mut v_fallback_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_3163_,
        v_t_3165_,
        v_a_3166_,
        v_fallback_3167_,
    );
    return v___x_3168_;
}
pub unsafe fn l_Std_ExtTreeMap_getD___boxed(
    mut v_00_u03b1_3169_: *mut leanh::LeanObject,
    mut v_00_u03b2_3170_: *mut leanh::LeanObject,
    mut v_cmp_3171_: *mut leanh::LeanObject,
    mut v_inst_3172_: *mut leanh::LeanObject,
    mut v_t_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
    mut v_fallback_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Std_ExtTreeMap_getD(
        v_00_u03b1_3169_,
        v_00_u03b2_3170_,
        v_cmp_3171_,
        v_inst_3172_,
        v_t_3173_,
        v_a_3174_,
        v_fallback_3175_,
    );
    leanh::lean_dec(v_fallback_3175_);
    return v_res_3176_;
}
pub unsafe fn l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0(
    mut v_cmp_3177_: *mut leanh::LeanObject,
    mut v_m_3178_: *mut leanh::LeanObject,
    mut v_a_3179_: *mut leanh::LeanObject,
    mut v_h_3180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_3177_, v_m_3178_, v_a_3179_);
    return v___x_3181_;
}
pub unsafe fn l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1(
    mut v_cmp_3182_: *mut leanh::LeanObject,
    mut v_m_3183_: *mut leanh::LeanObject,
    mut v_a_3184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3185_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_3182_, v_m_3183_, v_a_3184_);
    return v___x_3185_;
}
pub unsafe fn l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(
    mut v_cmp_3186_: *mut leanh::LeanObject,
    mut v_inst_3187_: *mut leanh::LeanObject,
    mut v_m_3188_: *mut leanh::LeanObject,
    mut v_a_3189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_3186_,
        v_inst_3187_,
        v_m_3188_,
        v_a_3189_,
    );
    return v___x_3190_;
}
pub unsafe fn l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed(
    mut v_cmp_3191_: *mut leanh::LeanObject,
    mut v_inst_3192_: *mut leanh::LeanObject,
    mut v_m_3193_: *mut leanh::LeanObject,
    mut v_a_3194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2(
        v_cmp_3191_,
        v_inst_3192_,
        v_m_3193_,
        v_a_3194_,
    );
    leanh::lean_dec(v_inst_3192_);
    return v_res_3195_;
}
pub unsafe fn l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(
    mut v_cmp_3196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_cmp_3196_, 2);
    v___f_3197_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3197_, 0, v_cmp_3196_);
    v___f_3198_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3198_, 0, v_cmp_3196_);
    v___f_3199_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instGetElem_x3fMem___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3199_, 0, v_cmp_3196_);
    v___x_3200_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3200_, 0, v___f_3197_);
    leanh::lean_ctor_set(v___x_3200_, 1, v___f_3198_);
    leanh::lean_ctor_set(v___x_3200_, 2, v___f_3199_);
    return v___x_3200_;
}
pub unsafe fn l_Std_ExtTreeMap_instGetElem_x3fMem(
    mut v_00_u03b1_3201_: *mut leanh::LeanObject,
    mut v_00_u03b2_3202_: *mut leanh::LeanObject,
    mut v_cmp_3203_: *mut leanh::LeanObject,
    mut v_inst_3204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = l_Std_ExtTreeMap_instGetElem_x3fMem___redArg(v_cmp_3203_);
    return v___x_3205_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey_x3f___redArg(
    mut v_cmp_3206_: *mut leanh::LeanObject,
    mut v_t_3207_: *mut leanh::LeanObject,
    mut v_a_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3209_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_3206_, v_t_3207_, v_a_3208_);
    return v___x_3209_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey_x3f(
    mut v_00_u03b1_3210_: *mut leanh::LeanObject,
    mut v_00_u03b2_3211_: *mut leanh::LeanObject,
    mut v_cmp_3212_: *mut leanh::LeanObject,
    mut v_inst_3213_: *mut leanh::LeanObject,
    mut v_t_3214_: *mut leanh::LeanObject,
    mut v_a_3215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3216_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_3212_, v_t_3214_, v_a_3215_);
    return v___x_3216_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey___redArg(
    mut v_cmp_3217_: *mut leanh::LeanObject,
    mut v_t_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_3217_, v_t_3218_, v_a_3219_);
    return v___x_3220_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey(
    mut v_00_u03b1_3221_: *mut leanh::LeanObject,
    mut v_00_u03b2_3222_: *mut leanh::LeanObject,
    mut v_cmp_3223_: *mut leanh::LeanObject,
    mut v_inst_3224_: *mut leanh::LeanObject,
    mut v_t_3225_: *mut leanh::LeanObject,
    mut v_a_3226_: *mut leanh::LeanObject,
    mut v_h_3227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3228_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_3223_, v_t_3225_, v_a_3226_);
    return v___x_3228_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey_x21___redArg(
    mut v_cmp_3229_: *mut leanh::LeanObject,
    mut v_inst_3230_: *mut leanh::LeanObject,
    mut v_t_3231_: *mut leanh::LeanObject,
    mut v_a_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_3229_,
        v_t_3231_,
        v_a_3232_,
        v_inst_3230_,
    );
    return v___x_3233_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey_x21___redArg___boxed(
    mut v_cmp_3234_: *mut leanh::LeanObject,
    mut v_inst_3235_: *mut leanh::LeanObject,
    mut v_t_3236_: *mut leanh::LeanObject,
    mut v_a_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ =
        l_Std_ExtTreeMap_getKey_x21___redArg(v_cmp_3234_, v_inst_3235_, v_t_3236_, v_a_3237_);
    leanh::lean_dec(v_inst_3235_);
    return v_res_3238_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey_x21(
    mut v_00_u03b1_3239_: *mut leanh::LeanObject,
    mut v_00_u03b2_3240_: *mut leanh::LeanObject,
    mut v_cmp_3241_: *mut leanh::LeanObject,
    mut v_inst_3242_: *mut leanh::LeanObject,
    mut v_inst_3243_: *mut leanh::LeanObject,
    mut v_t_3244_: *mut leanh::LeanObject,
    mut v_a_3245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_3241_,
        v_t_3244_,
        v_a_3245_,
        v_inst_3243_,
    );
    return v___x_3246_;
}
pub unsafe fn l_Std_ExtTreeMap_getKey_x21___boxed(
    mut v_00_u03b1_3247_: *mut leanh::LeanObject,
    mut v_00_u03b2_3248_: *mut leanh::LeanObject,
    mut v_cmp_3249_: *mut leanh::LeanObject,
    mut v_inst_3250_: *mut leanh::LeanObject,
    mut v_inst_3251_: *mut leanh::LeanObject,
    mut v_t_3252_: *mut leanh::LeanObject,
    mut v_a_3253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3254_ = l_Std_ExtTreeMap_getKey_x21(
        v_00_u03b1_3247_,
        v_00_u03b2_3248_,
        v_cmp_3249_,
        v_inst_3250_,
        v_inst_3251_,
        v_t_3252_,
        v_a_3253_,
    );
    leanh::lean_dec(v_inst_3251_);
    return v_res_3254_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyD___redArg(
    mut v_cmp_3255_: *mut leanh::LeanObject,
    mut v_t_3256_: *mut leanh::LeanObject,
    mut v_a_3257_: *mut leanh::LeanObject,
    mut v_fallback_3258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3259_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_3255_,
        v_t_3256_,
        v_a_3257_,
        v_fallback_3258_,
    );
    return v___x_3259_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyD___redArg___boxed(
    mut v_cmp_3260_: *mut leanh::LeanObject,
    mut v_t_3261_: *mut leanh::LeanObject,
    mut v_a_3262_: *mut leanh::LeanObject,
    mut v_fallback_3263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3264_ =
        l_Std_ExtTreeMap_getKeyD___redArg(v_cmp_3260_, v_t_3261_, v_a_3262_, v_fallback_3263_);
    leanh::lean_dec(v_fallback_3263_);
    return v_res_3264_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyD(
    mut v_00_u03b1_3265_: *mut leanh::LeanObject,
    mut v_00_u03b2_3266_: *mut leanh::LeanObject,
    mut v_cmp_3267_: *mut leanh::LeanObject,
    mut v_inst_3268_: *mut leanh::LeanObject,
    mut v_t_3269_: *mut leanh::LeanObject,
    mut v_a_3270_: *mut leanh::LeanObject,
    mut v_fallback_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3272_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_3267_,
        v_t_3269_,
        v_a_3270_,
        v_fallback_3271_,
    );
    return v___x_3272_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyD___boxed(
    mut v_00_u03b1_3273_: *mut leanh::LeanObject,
    mut v_00_u03b2_3274_: *mut leanh::LeanObject,
    mut v_cmp_3275_: *mut leanh::LeanObject,
    mut v_inst_3276_: *mut leanh::LeanObject,
    mut v_t_3277_: *mut leanh::LeanObject,
    mut v_a_3278_: *mut leanh::LeanObject,
    mut v_fallback_3279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3280_ = l_Std_ExtTreeMap_getKeyD(
        v_00_u03b1_3273_,
        v_00_u03b2_3274_,
        v_cmp_3275_,
        v_inst_3276_,
        v_t_3277_,
        v_a_3278_,
        v_fallback_3279_,
    );
    leanh::lean_dec(v_fallback_3279_);
    return v_res_3280_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x3f___redArg(
    mut v_t_3281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_3281_);
    return v___x_3282_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x3f___redArg___boxed(
    mut v_t_3283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3284_ = l_Std_ExtTreeMap_minEntry_x3f___redArg(v_t_3283_);
    leanh::lean_dec(v_t_3283_);
    return v_res_3284_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x3f(
    mut v_00_u03b1_3285_: *mut leanh::LeanObject,
    mut v_00_u03b2_3286_: *mut leanh::LeanObject,
    mut v_cmp_3287_: *mut leanh::LeanObject,
    mut v_inst_3288_: *mut leanh::LeanObject,
    mut v_t_3289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_3289_);
    return v___x_3290_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x3f___boxed(
    mut v_00_u03b1_3291_: *mut leanh::LeanObject,
    mut v_00_u03b2_3292_: *mut leanh::LeanObject,
    mut v_cmp_3293_: *mut leanh::LeanObject,
    mut v_inst_3294_: *mut leanh::LeanObject,
    mut v_t_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3296_ = l_Std_ExtTreeMap_minEntry_x3f(
        v_00_u03b1_3291_,
        v_00_u03b2_3292_,
        v_cmp_3293_,
        v_inst_3294_,
        v_t_3295_,
    );
    leanh::lean_dec(v_t_3295_);
    leanh::lean_dec_ref(v_cmp_3293_);
    return v_res_3296_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry___redArg(
    mut v_t_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3298_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_3297_);
    return v___x_3298_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry___redArg___boxed(
    mut v_t_3299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3300_ = l_Std_ExtTreeMap_minEntry___redArg(v_t_3299_);
    leanh::lean_dec(v_t_3299_);
    return v_res_3300_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry(
    mut v_00_u03b1_3301_: *mut leanh::LeanObject,
    mut v_00_u03b2_3302_: *mut leanh::LeanObject,
    mut v_cmp_3303_: *mut leanh::LeanObject,
    mut v_inst_3304_: *mut leanh::LeanObject,
    mut v_t_3305_: *mut leanh::LeanObject,
    mut v_h_3306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_3305_);
    return v___x_3307_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry___boxed(
    mut v_00_u03b1_3308_: *mut leanh::LeanObject,
    mut v_00_u03b2_3309_: *mut leanh::LeanObject,
    mut v_cmp_3310_: *mut leanh::LeanObject,
    mut v_inst_3311_: *mut leanh::LeanObject,
    mut v_t_3312_: *mut leanh::LeanObject,
    mut v_h_3313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_Std_ExtTreeMap_minEntry(
        v_00_u03b1_3308_,
        v_00_u03b2_3309_,
        v_cmp_3310_,
        v_inst_3311_,
        v_t_3312_,
        v_h_3313_,
    );
    leanh::lean_dec(v_t_3312_);
    leanh::lean_dec_ref(v_cmp_3310_);
    return v_res_3314_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x21___redArg(
    mut v_inst_3315_: *mut leanh::LeanObject,
    mut v_t_3316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3315_, v_t_3316_);
    return v___x_3317_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x21___redArg___boxed(
    mut v_inst_3318_: *mut leanh::LeanObject,
    mut v_t_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Std_ExtTreeMap_minEntry_x21___redArg(v_inst_3318_, v_t_3319_);
    leanh::lean_dec(v_t_3319_);
    leanh::lean_dec_ref(v_inst_3318_);
    return v_res_3320_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x21(
    mut v_00_u03b1_3321_: *mut leanh::LeanObject,
    mut v_00_u03b2_3322_: *mut leanh::LeanObject,
    mut v_cmp_3323_: *mut leanh::LeanObject,
    mut v_inst_3324_: *mut leanh::LeanObject,
    mut v_inst_3325_: *mut leanh::LeanObject,
    mut v_t_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3325_, v_t_3326_);
    return v___x_3327_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntry_x21___boxed(
    mut v_00_u03b1_3328_: *mut leanh::LeanObject,
    mut v_00_u03b2_3329_: *mut leanh::LeanObject,
    mut v_cmp_3330_: *mut leanh::LeanObject,
    mut v_inst_3331_: *mut leanh::LeanObject,
    mut v_inst_3332_: *mut leanh::LeanObject,
    mut v_t_3333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Std_ExtTreeMap_minEntry_x21(
        v_00_u03b1_3328_,
        v_00_u03b2_3329_,
        v_cmp_3330_,
        v_inst_3331_,
        v_inst_3332_,
        v_t_3333_,
    );
    leanh::lean_dec(v_t_3333_);
    leanh::lean_dec_ref(v_inst_3332_);
    leanh::lean_dec_ref(v_cmp_3330_);
    return v_res_3334_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntryD___redArg(
    mut v_t_3335_: *mut leanh::LeanObject,
    mut v_fallback_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3337_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_3335_, v_fallback_3336_);
    return v___x_3337_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntryD___redArg___boxed(
    mut v_t_3338_: *mut leanh::LeanObject,
    mut v_fallback_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3340_ = l_Std_ExtTreeMap_minEntryD___redArg(v_t_3338_, v_fallback_3339_);
    leanh::lean_dec_ref(v_fallback_3339_);
    leanh::lean_dec(v_t_3338_);
    return v_res_3340_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntryD(
    mut v_00_u03b1_3341_: *mut leanh::LeanObject,
    mut v_00_u03b2_3342_: *mut leanh::LeanObject,
    mut v_cmp_3343_: *mut leanh::LeanObject,
    mut v_inst_3344_: *mut leanh::LeanObject,
    mut v_t_3345_: *mut leanh::LeanObject,
    mut v_fallback_3346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3347_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_3345_, v_fallback_3346_);
    return v___x_3347_;
}
pub unsafe fn l_Std_ExtTreeMap_minEntryD___boxed(
    mut v_00_u03b1_3348_: *mut leanh::LeanObject,
    mut v_00_u03b2_3349_: *mut leanh::LeanObject,
    mut v_cmp_3350_: *mut leanh::LeanObject,
    mut v_inst_3351_: *mut leanh::LeanObject,
    mut v_t_3352_: *mut leanh::LeanObject,
    mut v_fallback_3353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3354_ = l_Std_ExtTreeMap_minEntryD(
        v_00_u03b1_3348_,
        v_00_u03b2_3349_,
        v_cmp_3350_,
        v_inst_3351_,
        v_t_3352_,
        v_fallback_3353_,
    );
    leanh::lean_dec_ref(v_fallback_3353_);
    leanh::lean_dec(v_t_3352_);
    leanh::lean_dec_ref(v_cmp_3350_);
    return v_res_3354_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x3f___redArg(
    mut v_t_3355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_3355_);
    return v___x_3356_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x3f___redArg___boxed(
    mut v_t_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3358_ = l_Std_ExtTreeMap_maxEntry_x3f___redArg(v_t_3357_);
    leanh::lean_dec(v_t_3357_);
    return v_res_3358_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x3f(
    mut v_00_u03b1_3359_: *mut leanh::LeanObject,
    mut v_00_u03b2_3360_: *mut leanh::LeanObject,
    mut v_cmp_3361_: *mut leanh::LeanObject,
    mut v_inst_3362_: *mut leanh::LeanObject,
    mut v_t_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3364_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_3363_);
    return v___x_3364_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x3f___boxed(
    mut v_00_u03b1_3365_: *mut leanh::LeanObject,
    mut v_00_u03b2_3366_: *mut leanh::LeanObject,
    mut v_cmp_3367_: *mut leanh::LeanObject,
    mut v_inst_3368_: *mut leanh::LeanObject,
    mut v_t_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3370_ = l_Std_ExtTreeMap_maxEntry_x3f(
        v_00_u03b1_3365_,
        v_00_u03b2_3366_,
        v_cmp_3367_,
        v_inst_3368_,
        v_t_3369_,
    );
    leanh::lean_dec(v_t_3369_);
    leanh::lean_dec_ref(v_cmp_3367_);
    return v_res_3370_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry___redArg(
    mut v_t_3371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3372_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_3371_);
    return v___x_3372_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry___redArg___boxed(
    mut v_t_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3374_ = l_Std_ExtTreeMap_maxEntry___redArg(v_t_3373_);
    leanh::lean_dec(v_t_3373_);
    return v_res_3374_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry(
    mut v_00_u03b1_3375_: *mut leanh::LeanObject,
    mut v_00_u03b2_3376_: *mut leanh::LeanObject,
    mut v_cmp_3377_: *mut leanh::LeanObject,
    mut v_inst_3378_: *mut leanh::LeanObject,
    mut v_t_3379_: *mut leanh::LeanObject,
    mut v_h_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3381_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_3379_);
    return v___x_3381_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry___boxed(
    mut v_00_u03b1_3382_: *mut leanh::LeanObject,
    mut v_00_u03b2_3383_: *mut leanh::LeanObject,
    mut v_cmp_3384_: *mut leanh::LeanObject,
    mut v_inst_3385_: *mut leanh::LeanObject,
    mut v_t_3386_: *mut leanh::LeanObject,
    mut v_h_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l_Std_ExtTreeMap_maxEntry(
        v_00_u03b1_3382_,
        v_00_u03b2_3383_,
        v_cmp_3384_,
        v_inst_3385_,
        v_t_3386_,
        v_h_3387_,
    );
    leanh::lean_dec(v_t_3386_);
    leanh::lean_dec_ref(v_cmp_3384_);
    return v_res_3388_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x21___redArg(
    mut v_inst_3389_: *mut leanh::LeanObject,
    mut v_t_3390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3389_, v_t_3390_);
    return v___x_3391_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x21___redArg___boxed(
    mut v_inst_3392_: *mut leanh::LeanObject,
    mut v_t_3393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3394_ = l_Std_ExtTreeMap_maxEntry_x21___redArg(v_inst_3392_, v_t_3393_);
    leanh::lean_dec(v_t_3393_);
    leanh::lean_dec_ref(v_inst_3392_);
    return v_res_3394_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x21(
    mut v_00_u03b1_3395_: *mut leanh::LeanObject,
    mut v_00_u03b2_3396_: *mut leanh::LeanObject,
    mut v_cmp_3397_: *mut leanh::LeanObject,
    mut v_inst_3398_: *mut leanh::LeanObject,
    mut v_inst_3399_: *mut leanh::LeanObject,
    mut v_t_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3399_, v_t_3400_);
    return v___x_3401_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntry_x21___boxed(
    mut v_00_u03b1_3402_: *mut leanh::LeanObject,
    mut v_00_u03b2_3403_: *mut leanh::LeanObject,
    mut v_cmp_3404_: *mut leanh::LeanObject,
    mut v_inst_3405_: *mut leanh::LeanObject,
    mut v_inst_3406_: *mut leanh::LeanObject,
    mut v_t_3407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Std_ExtTreeMap_maxEntry_x21(
        v_00_u03b1_3402_,
        v_00_u03b2_3403_,
        v_cmp_3404_,
        v_inst_3405_,
        v_inst_3406_,
        v_t_3407_,
    );
    leanh::lean_dec(v_t_3407_);
    leanh::lean_dec_ref(v_inst_3406_);
    leanh::lean_dec_ref(v_cmp_3404_);
    return v_res_3408_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntryD___redArg(
    mut v_t_3409_: *mut leanh::LeanObject,
    mut v_fallback_3410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_3409_, v_fallback_3410_);
    return v___x_3411_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntryD___redArg___boxed(
    mut v_t_3412_: *mut leanh::LeanObject,
    mut v_fallback_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3414_ = l_Std_ExtTreeMap_maxEntryD___redArg(v_t_3412_, v_fallback_3413_);
    leanh::lean_dec_ref(v_fallback_3413_);
    leanh::lean_dec(v_t_3412_);
    return v_res_3414_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntryD(
    mut v_00_u03b1_3415_: *mut leanh::LeanObject,
    mut v_00_u03b2_3416_: *mut leanh::LeanObject,
    mut v_cmp_3417_: *mut leanh::LeanObject,
    mut v_inst_3418_: *mut leanh::LeanObject,
    mut v_t_3419_: *mut leanh::LeanObject,
    mut v_fallback_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_3419_, v_fallback_3420_);
    return v___x_3421_;
}
pub unsafe fn l_Std_ExtTreeMap_maxEntryD___boxed(
    mut v_00_u03b1_3422_: *mut leanh::LeanObject,
    mut v_00_u03b2_3423_: *mut leanh::LeanObject,
    mut v_cmp_3424_: *mut leanh::LeanObject,
    mut v_inst_3425_: *mut leanh::LeanObject,
    mut v_t_3426_: *mut leanh::LeanObject,
    mut v_fallback_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Std_ExtTreeMap_maxEntryD(
        v_00_u03b1_3422_,
        v_00_u03b2_3423_,
        v_cmp_3424_,
        v_inst_3425_,
        v_t_3426_,
        v_fallback_3427_,
    );
    leanh::lean_dec_ref(v_fallback_3427_);
    leanh::lean_dec(v_t_3426_);
    leanh::lean_dec_ref(v_cmp_3424_);
    return v_res_3428_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x3f___redArg(
    mut v_t_3429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3430_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_3429_);
    return v___x_3430_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x3f___redArg___boxed(
    mut v_t_3431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Std_ExtTreeMap_minKey_x3f___redArg(v_t_3431_);
    leanh::lean_dec(v_t_3431_);
    return v_res_3432_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x3f(
    mut v_00_u03b1_3433_: *mut leanh::LeanObject,
    mut v_00_u03b2_3434_: *mut leanh::LeanObject,
    mut v_cmp_3435_: *mut leanh::LeanObject,
    mut v_inst_3436_: *mut leanh::LeanObject,
    mut v_t_3437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3438_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_3437_);
    return v___x_3438_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x3f___boxed(
    mut v_00_u03b1_3439_: *mut leanh::LeanObject,
    mut v_00_u03b2_3440_: *mut leanh::LeanObject,
    mut v_cmp_3441_: *mut leanh::LeanObject,
    mut v_inst_3442_: *mut leanh::LeanObject,
    mut v_t_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3444_ = l_Std_ExtTreeMap_minKey_x3f(
        v_00_u03b1_3439_,
        v_00_u03b2_3440_,
        v_cmp_3441_,
        v_inst_3442_,
        v_t_3443_,
    );
    leanh::lean_dec(v_t_3443_);
    leanh::lean_dec_ref(v_cmp_3441_);
    return v_res_3444_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey___redArg(
    mut v_t_3445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3446_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_3445_);
    return v___x_3446_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey___redArg___boxed(
    mut v_t_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Std_ExtTreeMap_minKey___redArg(v_t_3447_);
    leanh::lean_dec(v_t_3447_);
    return v_res_3448_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey(
    mut v_00_u03b1_3449_: *mut leanh::LeanObject,
    mut v_00_u03b2_3450_: *mut leanh::LeanObject,
    mut v_cmp_3451_: *mut leanh::LeanObject,
    mut v_inst_3452_: *mut leanh::LeanObject,
    mut v_t_3453_: *mut leanh::LeanObject,
    mut v_h_3454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3455_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_3453_);
    return v___x_3455_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey___boxed(
    mut v_00_u03b1_3456_: *mut leanh::LeanObject,
    mut v_00_u03b2_3457_: *mut leanh::LeanObject,
    mut v_cmp_3458_: *mut leanh::LeanObject,
    mut v_inst_3459_: *mut leanh::LeanObject,
    mut v_t_3460_: *mut leanh::LeanObject,
    mut v_h_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Std_ExtTreeMap_minKey(
        v_00_u03b1_3456_,
        v_00_u03b2_3457_,
        v_cmp_3458_,
        v_inst_3459_,
        v_t_3460_,
        v_h_3461_,
    );
    leanh::lean_dec(v_t_3460_);
    leanh::lean_dec_ref(v_cmp_3458_);
    return v_res_3462_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x21___redArg(
    mut v_inst_3463_: *mut leanh::LeanObject,
    mut v_t_3464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_3463_, v_t_3464_);
    return v___x_3465_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x21___redArg___boxed(
    mut v_inst_3466_: *mut leanh::LeanObject,
    mut v_t_3467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Std_ExtTreeMap_minKey_x21___redArg(v_inst_3466_, v_t_3467_);
    leanh::lean_dec(v_t_3467_);
    leanh::lean_dec(v_inst_3466_);
    return v_res_3468_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x21(
    mut v_00_u03b1_3469_: *mut leanh::LeanObject,
    mut v_00_u03b2_3470_: *mut leanh::LeanObject,
    mut v_cmp_3471_: *mut leanh::LeanObject,
    mut v_inst_3472_: *mut leanh::LeanObject,
    mut v_inst_3473_: *mut leanh::LeanObject,
    mut v_t_3474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_3473_, v_t_3474_);
    return v___x_3475_;
}
pub unsafe fn l_Std_ExtTreeMap_minKey_x21___boxed(
    mut v_00_u03b1_3476_: *mut leanh::LeanObject,
    mut v_00_u03b2_3477_: *mut leanh::LeanObject,
    mut v_cmp_3478_: *mut leanh::LeanObject,
    mut v_inst_3479_: *mut leanh::LeanObject,
    mut v_inst_3480_: *mut leanh::LeanObject,
    mut v_t_3481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Std_ExtTreeMap_minKey_x21(
        v_00_u03b1_3476_,
        v_00_u03b2_3477_,
        v_cmp_3478_,
        v_inst_3479_,
        v_inst_3480_,
        v_t_3481_,
    );
    leanh::lean_dec(v_t_3481_);
    leanh::lean_dec(v_inst_3480_);
    leanh::lean_dec_ref(v_cmp_3478_);
    return v_res_3482_;
}
pub unsafe fn l_Std_ExtTreeMap_minKeyD___redArg(
    mut v_t_3483_: *mut leanh::LeanObject,
    mut v_fallback_3484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3485_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_3483_, v_fallback_3484_);
    return v___x_3485_;
}
pub unsafe fn l_Std_ExtTreeMap_minKeyD___redArg___boxed(
    mut v_t_3486_: *mut leanh::LeanObject,
    mut v_fallback_3487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3488_ = l_Std_ExtTreeMap_minKeyD___redArg(v_t_3486_, v_fallback_3487_);
    leanh::lean_dec(v_fallback_3487_);
    leanh::lean_dec(v_t_3486_);
    return v_res_3488_;
}
pub unsafe fn l_Std_ExtTreeMap_minKeyD(
    mut v_00_u03b1_3489_: *mut leanh::LeanObject,
    mut v_00_u03b2_3490_: *mut leanh::LeanObject,
    mut v_cmp_3491_: *mut leanh::LeanObject,
    mut v_inst_3492_: *mut leanh::LeanObject,
    mut v_t_3493_: *mut leanh::LeanObject,
    mut v_fallback_3494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_3493_, v_fallback_3494_);
    return v___x_3495_;
}
pub unsafe fn l_Std_ExtTreeMap_minKeyD___boxed(
    mut v_00_u03b1_3496_: *mut leanh::LeanObject,
    mut v_00_u03b2_3497_: *mut leanh::LeanObject,
    mut v_cmp_3498_: *mut leanh::LeanObject,
    mut v_inst_3499_: *mut leanh::LeanObject,
    mut v_t_3500_: *mut leanh::LeanObject,
    mut v_fallback_3501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3502_ = l_Std_ExtTreeMap_minKeyD(
        v_00_u03b1_3496_,
        v_00_u03b2_3497_,
        v_cmp_3498_,
        v_inst_3499_,
        v_t_3500_,
        v_fallback_3501_,
    );
    leanh::lean_dec(v_fallback_3501_);
    leanh::lean_dec(v_t_3500_);
    leanh::lean_dec_ref(v_cmp_3498_);
    return v_res_3502_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x3f___redArg(
    mut v_t_3503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3504_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_3503_);
    return v___x_3504_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x3f___redArg___boxed(
    mut v_t_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Std_ExtTreeMap_maxKey_x3f___redArg(v_t_3505_);
    leanh::lean_dec(v_t_3505_);
    return v_res_3506_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x3f(
    mut v_00_u03b1_3507_: *mut leanh::LeanObject,
    mut v_00_u03b2_3508_: *mut leanh::LeanObject,
    mut v_cmp_3509_: *mut leanh::LeanObject,
    mut v_inst_3510_: *mut leanh::LeanObject,
    mut v_t_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3512_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_3511_);
    return v___x_3512_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x3f___boxed(
    mut v_00_u03b1_3513_: *mut leanh::LeanObject,
    mut v_00_u03b2_3514_: *mut leanh::LeanObject,
    mut v_cmp_3515_: *mut leanh::LeanObject,
    mut v_inst_3516_: *mut leanh::LeanObject,
    mut v_t_3517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3518_ = l_Std_ExtTreeMap_maxKey_x3f(
        v_00_u03b1_3513_,
        v_00_u03b2_3514_,
        v_cmp_3515_,
        v_inst_3516_,
        v_t_3517_,
    );
    leanh::lean_dec(v_t_3517_);
    leanh::lean_dec_ref(v_cmp_3515_);
    return v_res_3518_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey___redArg(
    mut v_t_3519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_3519_);
    return v___x_3520_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey___redArg___boxed(
    mut v_t_3521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3522_ = l_Std_ExtTreeMap_maxKey___redArg(v_t_3521_);
    leanh::lean_dec(v_t_3521_);
    return v_res_3522_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey(
    mut v_00_u03b1_3523_: *mut leanh::LeanObject,
    mut v_00_u03b2_3524_: *mut leanh::LeanObject,
    mut v_cmp_3525_: *mut leanh::LeanObject,
    mut v_inst_3526_: *mut leanh::LeanObject,
    mut v_t_3527_: *mut leanh::LeanObject,
    mut v_h_3528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3529_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_3527_);
    return v___x_3529_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey___boxed(
    mut v_00_u03b1_3530_: *mut leanh::LeanObject,
    mut v_00_u03b2_3531_: *mut leanh::LeanObject,
    mut v_cmp_3532_: *mut leanh::LeanObject,
    mut v_inst_3533_: *mut leanh::LeanObject,
    mut v_t_3534_: *mut leanh::LeanObject,
    mut v_h_3535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3536_ = l_Std_ExtTreeMap_maxKey(
        v_00_u03b1_3530_,
        v_00_u03b2_3531_,
        v_cmp_3532_,
        v_inst_3533_,
        v_t_3534_,
        v_h_3535_,
    );
    leanh::lean_dec(v_t_3534_);
    leanh::lean_dec_ref(v_cmp_3532_);
    return v_res_3536_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x21___redArg(
    mut v_inst_3537_: *mut leanh::LeanObject,
    mut v_t_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3539_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_3537_, v_t_3538_);
    return v___x_3539_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x21___redArg___boxed(
    mut v_inst_3540_: *mut leanh::LeanObject,
    mut v_t_3541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Std_ExtTreeMap_maxKey_x21___redArg(v_inst_3540_, v_t_3541_);
    leanh::lean_dec(v_t_3541_);
    leanh::lean_dec(v_inst_3540_);
    return v_res_3542_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x21(
    mut v_00_u03b1_3543_: *mut leanh::LeanObject,
    mut v_00_u03b2_3544_: *mut leanh::LeanObject,
    mut v_cmp_3545_: *mut leanh::LeanObject,
    mut v_inst_3546_: *mut leanh::LeanObject,
    mut v_inst_3547_: *mut leanh::LeanObject,
    mut v_t_3548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3549_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_3547_, v_t_3548_);
    return v___x_3549_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKey_x21___boxed(
    mut v_00_u03b1_3550_: *mut leanh::LeanObject,
    mut v_00_u03b2_3551_: *mut leanh::LeanObject,
    mut v_cmp_3552_: *mut leanh::LeanObject,
    mut v_inst_3553_: *mut leanh::LeanObject,
    mut v_inst_3554_: *mut leanh::LeanObject,
    mut v_t_3555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Std_ExtTreeMap_maxKey_x21(
        v_00_u03b1_3550_,
        v_00_u03b2_3551_,
        v_cmp_3552_,
        v_inst_3553_,
        v_inst_3554_,
        v_t_3555_,
    );
    leanh::lean_dec(v_t_3555_);
    leanh::lean_dec(v_inst_3554_);
    leanh::lean_dec_ref(v_cmp_3552_);
    return v_res_3556_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKeyD___redArg(
    mut v_t_3557_: *mut leanh::LeanObject,
    mut v_fallback_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_3557_, v_fallback_3558_);
    return v___x_3559_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKeyD___redArg___boxed(
    mut v_t_3560_: *mut leanh::LeanObject,
    mut v_fallback_3561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3562_ = l_Std_ExtTreeMap_maxKeyD___redArg(v_t_3560_, v_fallback_3561_);
    leanh::lean_dec(v_fallback_3561_);
    leanh::lean_dec(v_t_3560_);
    return v_res_3562_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKeyD(
    mut v_00_u03b1_3563_: *mut leanh::LeanObject,
    mut v_00_u03b2_3564_: *mut leanh::LeanObject,
    mut v_cmp_3565_: *mut leanh::LeanObject,
    mut v_inst_3566_: *mut leanh::LeanObject,
    mut v_t_3567_: *mut leanh::LeanObject,
    mut v_fallback_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3569_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_3567_, v_fallback_3568_);
    return v___x_3569_;
}
pub unsafe fn l_Std_ExtTreeMap_maxKeyD___boxed(
    mut v_00_u03b1_3570_: *mut leanh::LeanObject,
    mut v_00_u03b2_3571_: *mut leanh::LeanObject,
    mut v_cmp_3572_: *mut leanh::LeanObject,
    mut v_inst_3573_: *mut leanh::LeanObject,
    mut v_t_3574_: *mut leanh::LeanObject,
    mut v_fallback_3575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3576_ = l_Std_ExtTreeMap_maxKeyD(
        v_00_u03b1_3570_,
        v_00_u03b2_3571_,
        v_cmp_3572_,
        v_inst_3573_,
        v_t_3574_,
        v_fallback_3575_,
    );
    leanh::lean_dec(v_fallback_3575_);
    leanh::lean_dec(v_t_3574_);
    leanh::lean_dec_ref(v_cmp_3572_);
    return v_res_3576_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(
    mut v_t_3577_: *mut leanh::LeanObject,
    mut v_n_3578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3579_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_3577_, v_n_3578_);
    return v___x_3579_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x3f___redArg___boxed(
    mut v_t_3580_: *mut leanh::LeanObject,
    mut v_n_3581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3582_ = l_Std_ExtTreeMap_entryAtIdx_x3f___redArg(v_t_3580_, v_n_3581_);
    leanh::lean_dec(v_t_3580_);
    return v_res_3582_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x3f(
    mut v_00_u03b1_3583_: *mut leanh::LeanObject,
    mut v_00_u03b2_3584_: *mut leanh::LeanObject,
    mut v_cmp_3585_: *mut leanh::LeanObject,
    mut v_inst_3586_: *mut leanh::LeanObject,
    mut v_t_3587_: *mut leanh::LeanObject,
    mut v_n_3588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3589_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_3587_, v_n_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_3590_: *mut leanh::LeanObject,
    mut v_00_u03b2_3591_: *mut leanh::LeanObject,
    mut v_cmp_3592_: *mut leanh::LeanObject,
    mut v_inst_3593_: *mut leanh::LeanObject,
    mut v_t_3594_: *mut leanh::LeanObject,
    mut v_n_3595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3596_ = l_Std_ExtTreeMap_entryAtIdx_x3f(
        v_00_u03b1_3590_,
        v_00_u03b2_3591_,
        v_cmp_3592_,
        v_inst_3593_,
        v_t_3594_,
        v_n_3595_,
    );
    leanh::lean_dec(v_t_3594_);
    leanh::lean_dec_ref(v_cmp_3592_);
    return v_res_3596_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx___redArg(
    mut v_t_3597_: *mut leanh::LeanObject,
    mut v_n_3598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3599_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_3597_, v_n_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx___redArg___boxed(
    mut v_t_3600_: *mut leanh::LeanObject,
    mut v_n_3601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3602_ = l_Std_ExtTreeMap_entryAtIdx___redArg(v_t_3600_, v_n_3601_);
    leanh::lean_dec(v_t_3600_);
    return v_res_3602_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx(
    mut v_00_u03b1_3603_: *mut leanh::LeanObject,
    mut v_00_u03b2_3604_: *mut leanh::LeanObject,
    mut v_cmp_3605_: *mut leanh::LeanObject,
    mut v_inst_3606_: *mut leanh::LeanObject,
    mut v_t_3607_: *mut leanh::LeanObject,
    mut v_n_3608_: *mut leanh::LeanObject,
    mut v_h_3609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3610_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_3607_, v_n_3608_);
    return v___x_3610_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx___boxed(
    mut v_00_u03b1_3611_: *mut leanh::LeanObject,
    mut v_00_u03b2_3612_: *mut leanh::LeanObject,
    mut v_cmp_3613_: *mut leanh::LeanObject,
    mut v_inst_3614_: *mut leanh::LeanObject,
    mut v_t_3615_: *mut leanh::LeanObject,
    mut v_n_3616_: *mut leanh::LeanObject,
    mut v_h_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Std_ExtTreeMap_entryAtIdx(
        v_00_u03b1_3611_,
        v_00_u03b2_3612_,
        v_cmp_3613_,
        v_inst_3614_,
        v_t_3615_,
        v_n_3616_,
        v_h_3617_,
    );
    leanh::lean_dec(v_t_3615_);
    leanh::lean_dec_ref(v_cmp_3613_);
    return v_res_3618_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x21___redArg(
    mut v_inst_3619_: *mut leanh::LeanObject,
    mut v_t_3620_: *mut leanh::LeanObject,
    mut v_n_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3622_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_3619_,
        v_t_3620_,
        v_n_3621_,
    );
    return v___x_3622_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x21___redArg___boxed(
    mut v_inst_3623_: *mut leanh::LeanObject,
    mut v_t_3624_: *mut leanh::LeanObject,
    mut v_n_3625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3626_ = l_Std_ExtTreeMap_entryAtIdx_x21___redArg(v_inst_3623_, v_t_3624_, v_n_3625_);
    leanh::lean_dec(v_t_3624_);
    leanh::lean_dec_ref(v_inst_3623_);
    return v_res_3626_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x21(
    mut v_00_u03b1_3627_: *mut leanh::LeanObject,
    mut v_00_u03b2_3628_: *mut leanh::LeanObject,
    mut v_cmp_3629_: *mut leanh::LeanObject,
    mut v_inst_3630_: *mut leanh::LeanObject,
    mut v_inst_3631_: *mut leanh::LeanObject,
    mut v_t_3632_: *mut leanh::LeanObject,
    mut v_n_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3634_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_3631_,
        v_t_3632_,
        v_n_3633_,
    );
    return v___x_3634_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdx_x21___boxed(
    mut v_00_u03b1_3635_: *mut leanh::LeanObject,
    mut v_00_u03b2_3636_: *mut leanh::LeanObject,
    mut v_cmp_3637_: *mut leanh::LeanObject,
    mut v_inst_3638_: *mut leanh::LeanObject,
    mut v_inst_3639_: *mut leanh::LeanObject,
    mut v_t_3640_: *mut leanh::LeanObject,
    mut v_n_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3642_ = l_Std_ExtTreeMap_entryAtIdx_x21(
        v_00_u03b1_3635_,
        v_00_u03b2_3636_,
        v_cmp_3637_,
        v_inst_3638_,
        v_inst_3639_,
        v_t_3640_,
        v_n_3641_,
    );
    leanh::lean_dec(v_t_3640_);
    leanh::lean_dec_ref(v_inst_3639_);
    leanh::lean_dec_ref(v_cmp_3637_);
    return v_res_3642_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdxD___redArg(
    mut v_t_3643_: *mut leanh::LeanObject,
    mut v_n_3644_: *mut leanh::LeanObject,
    mut v_fallback_3645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_3643_,
        v_n_3644_,
        v_fallback_3645_,
    );
    return v___x_3646_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdxD___redArg___boxed(
    mut v_t_3647_: *mut leanh::LeanObject,
    mut v_n_3648_: *mut leanh::LeanObject,
    mut v_fallback_3649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ = l_Std_ExtTreeMap_entryAtIdxD___redArg(v_t_3647_, v_n_3648_, v_fallback_3649_);
    leanh::lean_dec_ref(v_fallback_3649_);
    leanh::lean_dec(v_t_3647_);
    return v_res_3650_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdxD(
    mut v_00_u03b1_3651_: *mut leanh::LeanObject,
    mut v_00_u03b2_3652_: *mut leanh::LeanObject,
    mut v_cmp_3653_: *mut leanh::LeanObject,
    mut v_inst_3654_: *mut leanh::LeanObject,
    mut v_t_3655_: *mut leanh::LeanObject,
    mut v_n_3656_: *mut leanh::LeanObject,
    mut v_fallback_3657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3658_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_3655_,
        v_n_3656_,
        v_fallback_3657_,
    );
    return v___x_3658_;
}
pub unsafe fn l_Std_ExtTreeMap_entryAtIdxD___boxed(
    mut v_00_u03b1_3659_: *mut leanh::LeanObject,
    mut v_00_u03b2_3660_: *mut leanh::LeanObject,
    mut v_cmp_3661_: *mut leanh::LeanObject,
    mut v_inst_3662_: *mut leanh::LeanObject,
    mut v_t_3663_: *mut leanh::LeanObject,
    mut v_n_3664_: *mut leanh::LeanObject,
    mut v_fallback_3665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3666_ = l_Std_ExtTreeMap_entryAtIdxD(
        v_00_u03b1_3659_,
        v_00_u03b2_3660_,
        v_cmp_3661_,
        v_inst_3662_,
        v_t_3663_,
        v_n_3664_,
        v_fallback_3665_,
    );
    leanh::lean_dec_ref(v_fallback_3665_);
    leanh::lean_dec(v_t_3663_);
    leanh::lean_dec_ref(v_cmp_3661_);
    return v_res_3666_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(
    mut v_t_3667_: *mut leanh::LeanObject,
    mut v_n_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3669_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_3667_, v_n_3668_);
    return v___x_3669_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x3f___redArg___boxed(
    mut v_t_3670_: *mut leanh::LeanObject,
    mut v_n_3671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3672_ = l_Std_ExtTreeMap_keyAtIdx_x3f___redArg(v_t_3670_, v_n_3671_);
    leanh::lean_dec(v_t_3670_);
    return v_res_3672_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x3f(
    mut v_00_u03b1_3673_: *mut leanh::LeanObject,
    mut v_00_u03b2_3674_: *mut leanh::LeanObject,
    mut v_cmp_3675_: *mut leanh::LeanObject,
    mut v_inst_3676_: *mut leanh::LeanObject,
    mut v_t_3677_: *mut leanh::LeanObject,
    mut v_n_3678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3679_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_3677_, v_n_3678_);
    return v___x_3679_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x3f___boxed(
    mut v_00_u03b1_3680_: *mut leanh::LeanObject,
    mut v_00_u03b2_3681_: *mut leanh::LeanObject,
    mut v_cmp_3682_: *mut leanh::LeanObject,
    mut v_inst_3683_: *mut leanh::LeanObject,
    mut v_t_3684_: *mut leanh::LeanObject,
    mut v_n_3685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Std_ExtTreeMap_keyAtIdx_x3f(
        v_00_u03b1_3680_,
        v_00_u03b2_3681_,
        v_cmp_3682_,
        v_inst_3683_,
        v_t_3684_,
        v_n_3685_,
    );
    leanh::lean_dec(v_t_3684_);
    leanh::lean_dec_ref(v_cmp_3682_);
    return v_res_3686_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx___redArg(
    mut v_t_3687_: *mut leanh::LeanObject,
    mut v_n_3688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3689_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_3687_, v_n_3688_);
    return v___x_3689_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx___redArg___boxed(
    mut v_t_3690_: *mut leanh::LeanObject,
    mut v_n_3691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3692_ = l_Std_ExtTreeMap_keyAtIdx___redArg(v_t_3690_, v_n_3691_);
    leanh::lean_dec(v_t_3690_);
    return v_res_3692_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx(
    mut v_00_u03b1_3693_: *mut leanh::LeanObject,
    mut v_00_u03b2_3694_: *mut leanh::LeanObject,
    mut v_cmp_3695_: *mut leanh::LeanObject,
    mut v_inst_3696_: *mut leanh::LeanObject,
    mut v_t_3697_: *mut leanh::LeanObject,
    mut v_n_3698_: *mut leanh::LeanObject,
    mut v_h_3699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_3697_, v_n_3698_);
    return v___x_3700_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx___boxed(
    mut v_00_u03b1_3701_: *mut leanh::LeanObject,
    mut v_00_u03b2_3702_: *mut leanh::LeanObject,
    mut v_cmp_3703_: *mut leanh::LeanObject,
    mut v_inst_3704_: *mut leanh::LeanObject,
    mut v_t_3705_: *mut leanh::LeanObject,
    mut v_n_3706_: *mut leanh::LeanObject,
    mut v_h_3707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3708_ = l_Std_ExtTreeMap_keyAtIdx(
        v_00_u03b1_3701_,
        v_00_u03b2_3702_,
        v_cmp_3703_,
        v_inst_3704_,
        v_t_3705_,
        v_n_3706_,
        v_h_3707_,
    );
    leanh::lean_dec(v_t_3705_);
    leanh::lean_dec_ref(v_cmp_3703_);
    return v_res_3708_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x21___redArg(
    mut v_inst_3709_: *mut leanh::LeanObject,
    mut v_t_3710_: *mut leanh::LeanObject,
    mut v_n_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_3709_, v_t_3710_, v_n_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x21___redArg___boxed(
    mut v_inst_3713_: *mut leanh::LeanObject,
    mut v_t_3714_: *mut leanh::LeanObject,
    mut v_n_3715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3716_ = l_Std_ExtTreeMap_keyAtIdx_x21___redArg(v_inst_3713_, v_t_3714_, v_n_3715_);
    leanh::lean_dec(v_t_3714_);
    leanh::lean_dec(v_inst_3713_);
    return v_res_3716_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x21(
    mut v_00_u03b1_3717_: *mut leanh::LeanObject,
    mut v_00_u03b2_3718_: *mut leanh::LeanObject,
    mut v_cmp_3719_: *mut leanh::LeanObject,
    mut v_inst_3720_: *mut leanh::LeanObject,
    mut v_inst_3721_: *mut leanh::LeanObject,
    mut v_t_3722_: *mut leanh::LeanObject,
    mut v_n_3723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_3721_, v_t_3722_, v_n_3723_);
    return v___x_3724_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdx_x21___boxed(
    mut v_00_u03b1_3725_: *mut leanh::LeanObject,
    mut v_00_u03b2_3726_: *mut leanh::LeanObject,
    mut v_cmp_3727_: *mut leanh::LeanObject,
    mut v_inst_3728_: *mut leanh::LeanObject,
    mut v_inst_3729_: *mut leanh::LeanObject,
    mut v_t_3730_: *mut leanh::LeanObject,
    mut v_n_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3732_ = l_Std_ExtTreeMap_keyAtIdx_x21(
        v_00_u03b1_3725_,
        v_00_u03b2_3726_,
        v_cmp_3727_,
        v_inst_3728_,
        v_inst_3729_,
        v_t_3730_,
        v_n_3731_,
    );
    leanh::lean_dec(v_t_3730_);
    leanh::lean_dec(v_inst_3729_);
    leanh::lean_dec_ref(v_cmp_3727_);
    return v_res_3732_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdxD___redArg(
    mut v_t_3733_: *mut leanh::LeanObject,
    mut v_n_3734_: *mut leanh::LeanObject,
    mut v_fallback_3735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3736_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_3733_, v_n_3734_, v_fallback_3735_);
    return v___x_3736_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdxD___redArg___boxed(
    mut v_t_3737_: *mut leanh::LeanObject,
    mut v_n_3738_: *mut leanh::LeanObject,
    mut v_fallback_3739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3740_ = l_Std_ExtTreeMap_keyAtIdxD___redArg(v_t_3737_, v_n_3738_, v_fallback_3739_);
    leanh::lean_dec(v_fallback_3739_);
    leanh::lean_dec(v_t_3737_);
    return v_res_3740_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdxD(
    mut v_00_u03b1_3741_: *mut leanh::LeanObject,
    mut v_00_u03b2_3742_: *mut leanh::LeanObject,
    mut v_cmp_3743_: *mut leanh::LeanObject,
    mut v_inst_3744_: *mut leanh::LeanObject,
    mut v_t_3745_: *mut leanh::LeanObject,
    mut v_n_3746_: *mut leanh::LeanObject,
    mut v_fallback_3747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_3745_, v_n_3746_, v_fallback_3747_);
    return v___x_3748_;
}
pub unsafe fn l_Std_ExtTreeMap_keyAtIdxD___boxed(
    mut v_00_u03b1_3749_: *mut leanh::LeanObject,
    mut v_00_u03b2_3750_: *mut leanh::LeanObject,
    mut v_cmp_3751_: *mut leanh::LeanObject,
    mut v_inst_3752_: *mut leanh::LeanObject,
    mut v_t_3753_: *mut leanh::LeanObject,
    mut v_n_3754_: *mut leanh::LeanObject,
    mut v_fallback_3755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3756_ = l_Std_ExtTreeMap_keyAtIdxD(
        v_00_u03b1_3749_,
        v_00_u03b2_3750_,
        v_cmp_3751_,
        v_inst_3752_,
        v_t_3753_,
        v_n_3754_,
        v_fallback_3755_,
    );
    leanh::lean_dec(v_fallback_3755_);
    leanh::lean_dec(v_t_3753_);
    leanh::lean_dec_ref(v_cmp_3751_);
    return v_res_3756_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE_x3f___redArg(
    mut v_cmp_3757_: *mut leanh::LeanObject,
    mut v_t_3758_: *mut leanh::LeanObject,
    mut v_k_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3760_ = leanh::lean_box(0);
    v___x_3761_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3757_,
        v_k_3759_,
        v___x_3760_,
        v_t_3758_,
    );
    return v___x_3761_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE_x3f(
    mut v_00_u03b1_3762_: *mut leanh::LeanObject,
    mut v_00_u03b2_3763_: *mut leanh::LeanObject,
    mut v_cmp_3764_: *mut leanh::LeanObject,
    mut v_inst_3765_: *mut leanh::LeanObject,
    mut v_t_3766_: *mut leanh::LeanObject,
    mut v_k_3767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3768_ = leanh::lean_box(0);
    v___x_3769_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3764_,
        v_k_3767_,
        v___x_3768_,
        v_t_3766_,
    );
    return v___x_3769_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT_x3f___redArg(
    mut v_cmp_3770_: *mut leanh::LeanObject,
    mut v_t_3771_: *mut leanh::LeanObject,
    mut v_k_3772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3773_ = leanh::lean_box(0);
    v___x_3774_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3770_,
        v_k_3772_,
        v___x_3773_,
        v_t_3771_,
    );
    return v___x_3774_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT_x3f(
    mut v_00_u03b1_3775_: *mut leanh::LeanObject,
    mut v_00_u03b2_3776_: *mut leanh::LeanObject,
    mut v_cmp_3777_: *mut leanh::LeanObject,
    mut v_inst_3778_: *mut leanh::LeanObject,
    mut v_t_3779_: *mut leanh::LeanObject,
    mut v_k_3780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3781_ = leanh::lean_box(0);
    v___x_3782_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3777_,
        v_k_3780_,
        v___x_3781_,
        v_t_3779_,
    );
    return v___x_3782_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE_x3f___redArg(
    mut v_cmp_3783_: *mut leanh::LeanObject,
    mut v_t_3784_: *mut leanh::LeanObject,
    mut v_k_3785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3786_ = leanh::lean_box(0);
    v___x_3787_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3783_,
        v_k_3785_,
        v___x_3786_,
        v_t_3784_,
    );
    return v___x_3787_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE_x3f(
    mut v_00_u03b1_3788_: *mut leanh::LeanObject,
    mut v_00_u03b2_3789_: *mut leanh::LeanObject,
    mut v_cmp_3790_: *mut leanh::LeanObject,
    mut v_inst_3791_: *mut leanh::LeanObject,
    mut v_t_3792_: *mut leanh::LeanObject,
    mut v_k_3793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = leanh::lean_box(0);
    v___x_3795_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3790_,
        v_k_3793_,
        v___x_3794_,
        v_t_3792_,
    );
    return v___x_3795_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT_x3f___redArg(
    mut v_cmp_3796_: *mut leanh::LeanObject,
    mut v_t_3797_: *mut leanh::LeanObject,
    mut v_k_3798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3799_ = leanh::lean_box(0);
    v___x_3800_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3796_,
        v_k_3798_,
        v___x_3799_,
        v_t_3797_,
    );
    return v___x_3800_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT_x3f(
    mut v_00_u03b1_3801_: *mut leanh::LeanObject,
    mut v_00_u03b2_3802_: *mut leanh::LeanObject,
    mut v_cmp_3803_: *mut leanh::LeanObject,
    mut v_inst_3804_: *mut leanh::LeanObject,
    mut v_t_3805_: *mut leanh::LeanObject,
    mut v_k_3806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3807_ = leanh::lean_box(0);
    v___x_3808_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3803_,
        v_k_3806_,
        v___x_3807_,
        v_t_3805_,
    );
    return v___x_3808_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE___redArg(
    mut v_cmp_3809_: *mut leanh::LeanObject,
    mut v_t_3810_: *mut leanh::LeanObject,
    mut v_k_3811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_3809_, v_k_3811_, v_t_3810_);
    return v___x_3812_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE(
    mut v_00_u03b1_3813_: *mut leanh::LeanObject,
    mut v_00_u03b2_3814_: *mut leanh::LeanObject,
    mut v_cmp_3815_: *mut leanh::LeanObject,
    mut v_inst_3816_: *mut leanh::LeanObject,
    mut v_t_3817_: *mut leanh::LeanObject,
    mut v_k_3818_: *mut leanh::LeanObject,
    mut v_h_3819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3820_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_3815_, v_k_3818_, v_t_3817_);
    return v___x_3820_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT___redArg(
    mut v_cmp_3821_: *mut leanh::LeanObject,
    mut v_t_3822_: *mut leanh::LeanObject,
    mut v_k_3823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3824_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_3821_, v_k_3823_, v_t_3822_);
    return v___x_3824_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT(
    mut v_00_u03b1_3825_: *mut leanh::LeanObject,
    mut v_00_u03b2_3826_: *mut leanh::LeanObject,
    mut v_cmp_3827_: *mut leanh::LeanObject,
    mut v_inst_3828_: *mut leanh::LeanObject,
    mut v_t_3829_: *mut leanh::LeanObject,
    mut v_k_3830_: *mut leanh::LeanObject,
    mut v_h_3831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3832_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_3827_, v_k_3830_, v_t_3829_);
    return v___x_3832_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE___redArg(
    mut v_cmp_3833_: *mut leanh::LeanObject,
    mut v_t_3834_: *mut leanh::LeanObject,
    mut v_k_3835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_3833_, v_k_3835_, v_t_3834_);
    return v___x_3836_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE(
    mut v_00_u03b1_3837_: *mut leanh::LeanObject,
    mut v_00_u03b2_3838_: *mut leanh::LeanObject,
    mut v_cmp_3839_: *mut leanh::LeanObject,
    mut v_inst_3840_: *mut leanh::LeanObject,
    mut v_t_3841_: *mut leanh::LeanObject,
    mut v_k_3842_: *mut leanh::LeanObject,
    mut v_h_3843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_3839_, v_k_3842_, v_t_3841_);
    return v___x_3844_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT___redArg(
    mut v_cmp_3845_: *mut leanh::LeanObject,
    mut v_t_3846_: *mut leanh::LeanObject,
    mut v_k_3847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3848_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_3845_, v_k_3847_, v_t_3846_);
    return v___x_3848_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT(
    mut v_00_u03b1_3849_: *mut leanh::LeanObject,
    mut v_00_u03b2_3850_: *mut leanh::LeanObject,
    mut v_cmp_3851_: *mut leanh::LeanObject,
    mut v_inst_3852_: *mut leanh::LeanObject,
    mut v_t_3853_: *mut leanh::LeanObject,
    mut v_k_3854_: *mut leanh::LeanObject,
    mut v_h_3855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3856_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_3851_, v_k_3854_, v_t_3853_);
    return v___x_3856_;
}
pub unsafe fn _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3860_ = l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__2;
    v___x_3861_ = leanh::lean_unsigned_to_nat(14);
    v___x_3862_ = leanh::lean_unsigned_to_nat(22);
    v___x_3863_ = l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__1;
    v___x_3864_ = l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__0;
    v___x_3865_ = l_mkPanicMessageWithDecl(
        v___x_3864_,
        v___x_3863_,
        v___x_3862_,
        v___x_3861_,
        v___x_3860_,
    );
    return v___x_3865_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE_x21___redArg(
    mut v_cmp_3866_: *mut leanh::LeanObject,
    mut v_inst_3867_: *mut leanh::LeanObject,
    mut v_t_3868_: *mut leanh::LeanObject,
    mut v_k_3869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = leanh::lean_box(0);
    v___x_3871_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3866_,
        v_k_3869_,
        v___x_3870_,
        v_t_3868_,
    );
    if leanh::lean_obj_tag(v___x_3871_) == 0 {
        let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3872_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3873_ = l_panic___redArg(v_inst_3867_, v___x_3872_);
        return v___x_3873_;
    } else {
        let mut v_val_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3874_ = leanh::lean_ctor_get(v___x_3871_, 0);
        leanh::lean_inc(v_val_3874_);
        leanh::lean_dec_ref_known(v___x_3871_, 1);
        return v_val_3874_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE_x21___redArg___boxed(
    mut v_cmp_3875_: *mut leanh::LeanObject,
    mut v_inst_3876_: *mut leanh::LeanObject,
    mut v_t_3877_: *mut leanh::LeanObject,
    mut v_k_3878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3879_ =
        l_Std_ExtTreeMap_getEntryGE_x21___redArg(v_cmp_3875_, v_inst_3876_, v_t_3877_, v_k_3878_);
    leanh::lean_dec_ref(v_inst_3876_);
    return v_res_3879_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE_x21(
    mut v_00_u03b1_3880_: *mut leanh::LeanObject,
    mut v_00_u03b2_3881_: *mut leanh::LeanObject,
    mut v_cmp_3882_: *mut leanh::LeanObject,
    mut v_inst_3883_: *mut leanh::LeanObject,
    mut v_inst_3884_: *mut leanh::LeanObject,
    mut v_t_3885_: *mut leanh::LeanObject,
    mut v_k_3886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3887_ = leanh::lean_box(0);
    v___x_3888_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3882_,
        v_k_3886_,
        v___x_3887_,
        v_t_3885_,
    );
    if leanh::lean_obj_tag(v___x_3888_) == 0 {
        let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3889_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3890_ = l_panic___redArg(v_inst_3884_, v___x_3889_);
        return v___x_3890_;
    } else {
        let mut v_val_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3891_ = leanh::lean_ctor_get(v___x_3888_, 0);
        leanh::lean_inc(v_val_3891_);
        leanh::lean_dec_ref_known(v___x_3888_, 1);
        return v_val_3891_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGE_x21___boxed(
    mut v_00_u03b1_3892_: *mut leanh::LeanObject,
    mut v_00_u03b2_3893_: *mut leanh::LeanObject,
    mut v_cmp_3894_: *mut leanh::LeanObject,
    mut v_inst_3895_: *mut leanh::LeanObject,
    mut v_inst_3896_: *mut leanh::LeanObject,
    mut v_t_3897_: *mut leanh::LeanObject,
    mut v_k_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3899_ = l_Std_ExtTreeMap_getEntryGE_x21(
        v_00_u03b1_3892_,
        v_00_u03b2_3893_,
        v_cmp_3894_,
        v_inst_3895_,
        v_inst_3896_,
        v_t_3897_,
        v_k_3898_,
    );
    leanh::lean_dec_ref(v_inst_3896_);
    return v_res_3899_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT_x21___redArg(
    mut v_cmp_3900_: *mut leanh::LeanObject,
    mut v_inst_3901_: *mut leanh::LeanObject,
    mut v_t_3902_: *mut leanh::LeanObject,
    mut v_k_3903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3904_ = leanh::lean_box(0);
    v___x_3905_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3900_,
        v_k_3903_,
        v___x_3904_,
        v_t_3902_,
    );
    if leanh::lean_obj_tag(v___x_3905_) == 0 {
        let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3906_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3907_ = l_panic___redArg(v_inst_3901_, v___x_3906_);
        return v___x_3907_;
    } else {
        let mut v_val_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3908_ = leanh::lean_ctor_get(v___x_3905_, 0);
        leanh::lean_inc(v_val_3908_);
        leanh::lean_dec_ref_known(v___x_3905_, 1);
        return v_val_3908_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT_x21___redArg___boxed(
    mut v_cmp_3909_: *mut leanh::LeanObject,
    mut v_inst_3910_: *mut leanh::LeanObject,
    mut v_t_3911_: *mut leanh::LeanObject,
    mut v_k_3912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3913_ =
        l_Std_ExtTreeMap_getEntryGT_x21___redArg(v_cmp_3909_, v_inst_3910_, v_t_3911_, v_k_3912_);
    leanh::lean_dec_ref(v_inst_3910_);
    return v_res_3913_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT_x21(
    mut v_00_u03b1_3914_: *mut leanh::LeanObject,
    mut v_00_u03b2_3915_: *mut leanh::LeanObject,
    mut v_cmp_3916_: *mut leanh::LeanObject,
    mut v_inst_3917_: *mut leanh::LeanObject,
    mut v_inst_3918_: *mut leanh::LeanObject,
    mut v_t_3919_: *mut leanh::LeanObject,
    mut v_k_3920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3921_ = leanh::lean_box(0);
    v___x_3922_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3916_,
        v_k_3920_,
        v___x_3921_,
        v_t_3919_,
    );
    if leanh::lean_obj_tag(v___x_3922_) == 0 {
        let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3923_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3924_ = l_panic___redArg(v_inst_3918_, v___x_3923_);
        return v___x_3924_;
    } else {
        let mut v_val_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3925_ = leanh::lean_ctor_get(v___x_3922_, 0);
        leanh::lean_inc(v_val_3925_);
        leanh::lean_dec_ref_known(v___x_3922_, 1);
        return v_val_3925_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGT_x21___boxed(
    mut v_00_u03b1_3926_: *mut leanh::LeanObject,
    mut v_00_u03b2_3927_: *mut leanh::LeanObject,
    mut v_cmp_3928_: *mut leanh::LeanObject,
    mut v_inst_3929_: *mut leanh::LeanObject,
    mut v_inst_3930_: *mut leanh::LeanObject,
    mut v_t_3931_: *mut leanh::LeanObject,
    mut v_k_3932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3933_ = l_Std_ExtTreeMap_getEntryGT_x21(
        v_00_u03b1_3926_,
        v_00_u03b2_3927_,
        v_cmp_3928_,
        v_inst_3929_,
        v_inst_3930_,
        v_t_3931_,
        v_k_3932_,
    );
    leanh::lean_dec_ref(v_inst_3930_);
    return v_res_3933_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE_x21___redArg(
    mut v_cmp_3934_: *mut leanh::LeanObject,
    mut v_inst_3935_: *mut leanh::LeanObject,
    mut v_t_3936_: *mut leanh::LeanObject,
    mut v_k_3937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3938_ = leanh::lean_box(0);
    v___x_3939_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3934_,
        v_k_3937_,
        v___x_3938_,
        v_t_3936_,
    );
    if leanh::lean_obj_tag(v___x_3939_) == 0 {
        let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3940_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3941_ = l_panic___redArg(v_inst_3935_, v___x_3940_);
        return v___x_3941_;
    } else {
        let mut v_val_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3942_ = leanh::lean_ctor_get(v___x_3939_, 0);
        leanh::lean_inc(v_val_3942_);
        leanh::lean_dec_ref_known(v___x_3939_, 1);
        return v_val_3942_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE_x21___redArg___boxed(
    mut v_cmp_3943_: *mut leanh::LeanObject,
    mut v_inst_3944_: *mut leanh::LeanObject,
    mut v_t_3945_: *mut leanh::LeanObject,
    mut v_k_3946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3947_ =
        l_Std_ExtTreeMap_getEntryLE_x21___redArg(v_cmp_3943_, v_inst_3944_, v_t_3945_, v_k_3946_);
    leanh::lean_dec_ref(v_inst_3944_);
    return v_res_3947_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE_x21(
    mut v_00_u03b1_3948_: *mut leanh::LeanObject,
    mut v_00_u03b2_3949_: *mut leanh::LeanObject,
    mut v_cmp_3950_: *mut leanh::LeanObject,
    mut v_inst_3951_: *mut leanh::LeanObject,
    mut v_inst_3952_: *mut leanh::LeanObject,
    mut v_t_3953_: *mut leanh::LeanObject,
    mut v_k_3954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = leanh::lean_box(0);
    v___x_3956_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3950_,
        v_k_3954_,
        v___x_3955_,
        v_t_3953_,
    );
    if leanh::lean_obj_tag(v___x_3956_) == 0 {
        let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3957_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3958_ = l_panic___redArg(v_inst_3952_, v___x_3957_);
        return v___x_3958_;
    } else {
        let mut v_val_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3959_ = leanh::lean_ctor_get(v___x_3956_, 0);
        leanh::lean_inc(v_val_3959_);
        leanh::lean_dec_ref_known(v___x_3956_, 1);
        return v_val_3959_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLE_x21___boxed(
    mut v_00_u03b1_3960_: *mut leanh::LeanObject,
    mut v_00_u03b2_3961_: *mut leanh::LeanObject,
    mut v_cmp_3962_: *mut leanh::LeanObject,
    mut v_inst_3963_: *mut leanh::LeanObject,
    mut v_inst_3964_: *mut leanh::LeanObject,
    mut v_t_3965_: *mut leanh::LeanObject,
    mut v_k_3966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3967_ = l_Std_ExtTreeMap_getEntryLE_x21(
        v_00_u03b1_3960_,
        v_00_u03b2_3961_,
        v_cmp_3962_,
        v_inst_3963_,
        v_inst_3964_,
        v_t_3965_,
        v_k_3966_,
    );
    leanh::lean_dec_ref(v_inst_3964_);
    return v_res_3967_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT_x21___redArg(
    mut v_cmp_3968_: *mut leanh::LeanObject,
    mut v_inst_3969_: *mut leanh::LeanObject,
    mut v_t_3970_: *mut leanh::LeanObject,
    mut v_k_3971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = leanh::lean_box(0);
    v___x_3973_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3968_,
        v_k_3971_,
        v___x_3972_,
        v_t_3970_,
    );
    if leanh::lean_obj_tag(v___x_3973_) == 0 {
        let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3974_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3975_ = l_panic___redArg(v_inst_3969_, v___x_3974_);
        return v___x_3975_;
    } else {
        let mut v_val_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3976_ = leanh::lean_ctor_get(v___x_3973_, 0);
        leanh::lean_inc(v_val_3976_);
        leanh::lean_dec_ref_known(v___x_3973_, 1);
        return v_val_3976_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT_x21___redArg___boxed(
    mut v_cmp_3977_: *mut leanh::LeanObject,
    mut v_inst_3978_: *mut leanh::LeanObject,
    mut v_t_3979_: *mut leanh::LeanObject,
    mut v_k_3980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3981_ =
        l_Std_ExtTreeMap_getEntryLT_x21___redArg(v_cmp_3977_, v_inst_3978_, v_t_3979_, v_k_3980_);
    leanh::lean_dec_ref(v_inst_3978_);
    return v_res_3981_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT_x21(
    mut v_00_u03b1_3982_: *mut leanh::LeanObject,
    mut v_00_u03b2_3983_: *mut leanh::LeanObject,
    mut v_cmp_3984_: *mut leanh::LeanObject,
    mut v_inst_3985_: *mut leanh::LeanObject,
    mut v_inst_3986_: *mut leanh::LeanObject,
    mut v_t_3987_: *mut leanh::LeanObject,
    mut v_k_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3989_ = leanh::lean_box(0);
    v___x_3990_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3984_,
        v_k_3988_,
        v___x_3989_,
        v_t_3987_,
    );
    if leanh::lean_obj_tag(v___x_3990_) == 0 {
        let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3991_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3992_ = l_panic___redArg(v_inst_3986_, v___x_3991_);
        return v___x_3992_;
    } else {
        let mut v_val_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3993_ = leanh::lean_ctor_get(v___x_3990_, 0);
        leanh::lean_inc(v_val_3993_);
        leanh::lean_dec_ref_known(v___x_3990_, 1);
        return v_val_3993_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLT_x21___boxed(
    mut v_00_u03b1_3994_: *mut leanh::LeanObject,
    mut v_00_u03b2_3995_: *mut leanh::LeanObject,
    mut v_cmp_3996_: *mut leanh::LeanObject,
    mut v_inst_3997_: *mut leanh::LeanObject,
    mut v_inst_3998_: *mut leanh::LeanObject,
    mut v_t_3999_: *mut leanh::LeanObject,
    mut v_k_4000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4001_ = l_Std_ExtTreeMap_getEntryLT_x21(
        v_00_u03b1_3994_,
        v_00_u03b2_3995_,
        v_cmp_3996_,
        v_inst_3997_,
        v_inst_3998_,
        v_t_3999_,
        v_k_4000_,
    );
    leanh::lean_dec_ref(v_inst_3998_);
    return v_res_4001_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGED___redArg(
    mut v_cmp_4002_: *mut leanh::LeanObject,
    mut v_t_4003_: *mut leanh::LeanObject,
    mut v_k_4004_: *mut leanh::LeanObject,
    mut v_fallback_4005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4006_ = leanh::lean_box(0);
    v___x_4007_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_4002_,
        v_k_4004_,
        v___x_4006_,
        v_t_4003_,
    );
    if leanh::lean_obj_tag(v___x_4007_) == 0 {
        leanh::lean_inc_ref(v_fallback_4005_);
        return v_fallback_4005_;
    } else {
        let mut v_val_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4008_ = leanh::lean_ctor_get(v___x_4007_, 0);
        leanh::lean_inc(v_val_4008_);
        leanh::lean_dec_ref_known(v___x_4007_, 1);
        return v_val_4008_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGED___redArg___boxed(
    mut v_cmp_4009_: *mut leanh::LeanObject,
    mut v_t_4010_: *mut leanh::LeanObject,
    mut v_k_4011_: *mut leanh::LeanObject,
    mut v_fallback_4012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4013_ =
        l_Std_ExtTreeMap_getEntryGED___redArg(v_cmp_4009_, v_t_4010_, v_k_4011_, v_fallback_4012_);
    leanh::lean_dec_ref(v_fallback_4012_);
    return v_res_4013_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGED(
    mut v_00_u03b1_4014_: *mut leanh::LeanObject,
    mut v_00_u03b2_4015_: *mut leanh::LeanObject,
    mut v_cmp_4016_: *mut leanh::LeanObject,
    mut v_inst_4017_: *mut leanh::LeanObject,
    mut v_t_4018_: *mut leanh::LeanObject,
    mut v_k_4019_: *mut leanh::LeanObject,
    mut v_fallback_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = leanh::lean_box(0);
    v___x_4022_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_4016_,
        v_k_4019_,
        v___x_4021_,
        v_t_4018_,
    );
    if leanh::lean_obj_tag(v___x_4022_) == 0 {
        leanh::lean_inc_ref(v_fallback_4020_);
        return v_fallback_4020_;
    } else {
        let mut v_val_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4023_ = leanh::lean_ctor_get(v___x_4022_, 0);
        leanh::lean_inc(v_val_4023_);
        leanh::lean_dec_ref_known(v___x_4022_, 1);
        return v_val_4023_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGED___boxed(
    mut v_00_u03b1_4024_: *mut leanh::LeanObject,
    mut v_00_u03b2_4025_: *mut leanh::LeanObject,
    mut v_cmp_4026_: *mut leanh::LeanObject,
    mut v_inst_4027_: *mut leanh::LeanObject,
    mut v_t_4028_: *mut leanh::LeanObject,
    mut v_k_4029_: *mut leanh::LeanObject,
    mut v_fallback_4030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4031_ = l_Std_ExtTreeMap_getEntryGED(
        v_00_u03b1_4024_,
        v_00_u03b2_4025_,
        v_cmp_4026_,
        v_inst_4027_,
        v_t_4028_,
        v_k_4029_,
        v_fallback_4030_,
    );
    leanh::lean_dec_ref(v_fallback_4030_);
    return v_res_4031_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGTD___redArg(
    mut v_cmp_4032_: *mut leanh::LeanObject,
    mut v_t_4033_: *mut leanh::LeanObject,
    mut v_k_4034_: *mut leanh::LeanObject,
    mut v_fallback_4035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = leanh::lean_box(0);
    v___x_4037_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_4032_,
        v_k_4034_,
        v___x_4036_,
        v_t_4033_,
    );
    if leanh::lean_obj_tag(v___x_4037_) == 0 {
        leanh::lean_inc_ref(v_fallback_4035_);
        return v_fallback_4035_;
    } else {
        let mut v_val_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4038_ = leanh::lean_ctor_get(v___x_4037_, 0);
        leanh::lean_inc(v_val_4038_);
        leanh::lean_dec_ref_known(v___x_4037_, 1);
        return v_val_4038_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGTD___redArg___boxed(
    mut v_cmp_4039_: *mut leanh::LeanObject,
    mut v_t_4040_: *mut leanh::LeanObject,
    mut v_k_4041_: *mut leanh::LeanObject,
    mut v_fallback_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4043_ =
        l_Std_ExtTreeMap_getEntryGTD___redArg(v_cmp_4039_, v_t_4040_, v_k_4041_, v_fallback_4042_);
    leanh::lean_dec_ref(v_fallback_4042_);
    return v_res_4043_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGTD(
    mut v_00_u03b1_4044_: *mut leanh::LeanObject,
    mut v_00_u03b2_4045_: *mut leanh::LeanObject,
    mut v_cmp_4046_: *mut leanh::LeanObject,
    mut v_inst_4047_: *mut leanh::LeanObject,
    mut v_t_4048_: *mut leanh::LeanObject,
    mut v_k_4049_: *mut leanh::LeanObject,
    mut v_fallback_4050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4051_ = leanh::lean_box(0);
    v___x_4052_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_4046_,
        v_k_4049_,
        v___x_4051_,
        v_t_4048_,
    );
    if leanh::lean_obj_tag(v___x_4052_) == 0 {
        leanh::lean_inc_ref(v_fallback_4050_);
        return v_fallback_4050_;
    } else {
        let mut v_val_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4053_ = leanh::lean_ctor_get(v___x_4052_, 0);
        leanh::lean_inc(v_val_4053_);
        leanh::lean_dec_ref_known(v___x_4052_, 1);
        return v_val_4053_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryGTD___boxed(
    mut v_00_u03b1_4054_: *mut leanh::LeanObject,
    mut v_00_u03b2_4055_: *mut leanh::LeanObject,
    mut v_cmp_4056_: *mut leanh::LeanObject,
    mut v_inst_4057_: *mut leanh::LeanObject,
    mut v_t_4058_: *mut leanh::LeanObject,
    mut v_k_4059_: *mut leanh::LeanObject,
    mut v_fallback_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Std_ExtTreeMap_getEntryGTD(
        v_00_u03b1_4054_,
        v_00_u03b2_4055_,
        v_cmp_4056_,
        v_inst_4057_,
        v_t_4058_,
        v_k_4059_,
        v_fallback_4060_,
    );
    leanh::lean_dec_ref(v_fallback_4060_);
    return v_res_4061_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLED___redArg(
    mut v_cmp_4062_: *mut leanh::LeanObject,
    mut v_t_4063_: *mut leanh::LeanObject,
    mut v_k_4064_: *mut leanh::LeanObject,
    mut v_fallback_4065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4066_ = leanh::lean_box(0);
    v___x_4067_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_4062_,
        v_k_4064_,
        v___x_4066_,
        v_t_4063_,
    );
    if leanh::lean_obj_tag(v___x_4067_) == 0 {
        leanh::lean_inc_ref(v_fallback_4065_);
        return v_fallback_4065_;
    } else {
        let mut v_val_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4068_ = leanh::lean_ctor_get(v___x_4067_, 0);
        leanh::lean_inc(v_val_4068_);
        leanh::lean_dec_ref_known(v___x_4067_, 1);
        return v_val_4068_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLED___redArg___boxed(
    mut v_cmp_4069_: *mut leanh::LeanObject,
    mut v_t_4070_: *mut leanh::LeanObject,
    mut v_k_4071_: *mut leanh::LeanObject,
    mut v_fallback_4072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ =
        l_Std_ExtTreeMap_getEntryLED___redArg(v_cmp_4069_, v_t_4070_, v_k_4071_, v_fallback_4072_);
    leanh::lean_dec_ref(v_fallback_4072_);
    return v_res_4073_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLED(
    mut v_00_u03b1_4074_: *mut leanh::LeanObject,
    mut v_00_u03b2_4075_: *mut leanh::LeanObject,
    mut v_cmp_4076_: *mut leanh::LeanObject,
    mut v_inst_4077_: *mut leanh::LeanObject,
    mut v_t_4078_: *mut leanh::LeanObject,
    mut v_k_4079_: *mut leanh::LeanObject,
    mut v_fallback_4080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4081_ = leanh::lean_box(0);
    v___x_4082_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_4076_,
        v_k_4079_,
        v___x_4081_,
        v_t_4078_,
    );
    if leanh::lean_obj_tag(v___x_4082_) == 0 {
        leanh::lean_inc_ref(v_fallback_4080_);
        return v_fallback_4080_;
    } else {
        let mut v_val_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4083_ = leanh::lean_ctor_get(v___x_4082_, 0);
        leanh::lean_inc(v_val_4083_);
        leanh::lean_dec_ref_known(v___x_4082_, 1);
        return v_val_4083_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLED___boxed(
    mut v_00_u03b1_4084_: *mut leanh::LeanObject,
    mut v_00_u03b2_4085_: *mut leanh::LeanObject,
    mut v_cmp_4086_: *mut leanh::LeanObject,
    mut v_inst_4087_: *mut leanh::LeanObject,
    mut v_t_4088_: *mut leanh::LeanObject,
    mut v_k_4089_: *mut leanh::LeanObject,
    mut v_fallback_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_Std_ExtTreeMap_getEntryLED(
        v_00_u03b1_4084_,
        v_00_u03b2_4085_,
        v_cmp_4086_,
        v_inst_4087_,
        v_t_4088_,
        v_k_4089_,
        v_fallback_4090_,
    );
    leanh::lean_dec_ref(v_fallback_4090_);
    return v_res_4091_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLTD___redArg(
    mut v_cmp_4092_: *mut leanh::LeanObject,
    mut v_t_4093_: *mut leanh::LeanObject,
    mut v_k_4094_: *mut leanh::LeanObject,
    mut v_fallback_4095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4096_ = leanh::lean_box(0);
    v___x_4097_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_4092_,
        v_k_4094_,
        v___x_4096_,
        v_t_4093_,
    );
    if leanh::lean_obj_tag(v___x_4097_) == 0 {
        leanh::lean_inc_ref(v_fallback_4095_);
        return v_fallback_4095_;
    } else {
        let mut v_val_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4098_ = leanh::lean_ctor_get(v___x_4097_, 0);
        leanh::lean_inc(v_val_4098_);
        leanh::lean_dec_ref_known(v___x_4097_, 1);
        return v_val_4098_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLTD___redArg___boxed(
    mut v_cmp_4099_: *mut leanh::LeanObject,
    mut v_t_4100_: *mut leanh::LeanObject,
    mut v_k_4101_: *mut leanh::LeanObject,
    mut v_fallback_4102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4103_ =
        l_Std_ExtTreeMap_getEntryLTD___redArg(v_cmp_4099_, v_t_4100_, v_k_4101_, v_fallback_4102_);
    leanh::lean_dec_ref(v_fallback_4102_);
    return v_res_4103_;
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLTD(
    mut v_00_u03b1_4104_: *mut leanh::LeanObject,
    mut v_00_u03b2_4105_: *mut leanh::LeanObject,
    mut v_cmp_4106_: *mut leanh::LeanObject,
    mut v_inst_4107_: *mut leanh::LeanObject,
    mut v_t_4108_: *mut leanh::LeanObject,
    mut v_k_4109_: *mut leanh::LeanObject,
    mut v_fallback_4110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4111_ = leanh::lean_box(0);
    v___x_4112_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_4106_,
        v_k_4109_,
        v___x_4111_,
        v_t_4108_,
    );
    if leanh::lean_obj_tag(v___x_4112_) == 0 {
        leanh::lean_inc_ref(v_fallback_4110_);
        return v_fallback_4110_;
    } else {
        let mut v_val_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4113_ = leanh::lean_ctor_get(v___x_4112_, 0);
        leanh::lean_inc(v_val_4113_);
        leanh::lean_dec_ref_known(v___x_4112_, 1);
        return v_val_4113_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getEntryLTD___boxed(
    mut v_00_u03b1_4114_: *mut leanh::LeanObject,
    mut v_00_u03b2_4115_: *mut leanh::LeanObject,
    mut v_cmp_4116_: *mut leanh::LeanObject,
    mut v_inst_4117_: *mut leanh::LeanObject,
    mut v_t_4118_: *mut leanh::LeanObject,
    mut v_k_4119_: *mut leanh::LeanObject,
    mut v_fallback_4120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Std_ExtTreeMap_getEntryLTD(
        v_00_u03b1_4114_,
        v_00_u03b2_4115_,
        v_cmp_4116_,
        v_inst_4117_,
        v_t_4118_,
        v_k_4119_,
        v_fallback_4120_,
    );
    leanh::lean_dec_ref(v_fallback_4120_);
    return v_res_4121_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE_x3f___redArg(
    mut v_cmp_4122_: *mut leanh::LeanObject,
    mut v_t_4123_: *mut leanh::LeanObject,
    mut v_k_4124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4125_ = leanh::lean_box(0);
    v___x_4126_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4122_,
        v_k_4124_,
        v___x_4125_,
        v_t_4123_,
    );
    return v___x_4126_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE_x3f(
    mut v_00_u03b1_4127_: *mut leanh::LeanObject,
    mut v_00_u03b2_4128_: *mut leanh::LeanObject,
    mut v_cmp_4129_: *mut leanh::LeanObject,
    mut v_inst_4130_: *mut leanh::LeanObject,
    mut v_t_4131_: *mut leanh::LeanObject,
    mut v_k_4132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ = leanh::lean_box(0);
    v___x_4134_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4129_,
        v_k_4132_,
        v___x_4133_,
        v_t_4131_,
    );
    return v___x_4134_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT_x3f___redArg(
    mut v_cmp_4135_: *mut leanh::LeanObject,
    mut v_t_4136_: *mut leanh::LeanObject,
    mut v_k_4137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = leanh::lean_box(0);
    v___x_4139_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4135_,
        v_k_4137_,
        v___x_4138_,
        v_t_4136_,
    );
    return v___x_4139_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT_x3f(
    mut v_00_u03b1_4140_: *mut leanh::LeanObject,
    mut v_00_u03b2_4141_: *mut leanh::LeanObject,
    mut v_cmp_4142_: *mut leanh::LeanObject,
    mut v_inst_4143_: *mut leanh::LeanObject,
    mut v_t_4144_: *mut leanh::LeanObject,
    mut v_k_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = leanh::lean_box(0);
    v___x_4147_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4142_,
        v_k_4145_,
        v___x_4146_,
        v_t_4144_,
    );
    return v___x_4147_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE_x3f___redArg(
    mut v_cmp_4148_: *mut leanh::LeanObject,
    mut v_t_4149_: *mut leanh::LeanObject,
    mut v_k_4150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4151_ = leanh::lean_box(0);
    v___x_4152_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4148_,
        v_k_4150_,
        v___x_4151_,
        v_t_4149_,
    );
    return v___x_4152_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE_x3f(
    mut v_00_u03b1_4153_: *mut leanh::LeanObject,
    mut v_00_u03b2_4154_: *mut leanh::LeanObject,
    mut v_cmp_4155_: *mut leanh::LeanObject,
    mut v_inst_4156_: *mut leanh::LeanObject,
    mut v_t_4157_: *mut leanh::LeanObject,
    mut v_k_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = leanh::lean_box(0);
    v___x_4160_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4155_,
        v_k_4158_,
        v___x_4159_,
        v_t_4157_,
    );
    return v___x_4160_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT_x3f___redArg(
    mut v_cmp_4161_: *mut leanh::LeanObject,
    mut v_t_4162_: *mut leanh::LeanObject,
    mut v_k_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4164_ = leanh::lean_box(0);
    v___x_4165_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4161_,
        v_k_4163_,
        v___x_4164_,
        v_t_4162_,
    );
    return v___x_4165_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT_x3f(
    mut v_00_u03b1_4166_: *mut leanh::LeanObject,
    mut v_00_u03b2_4167_: *mut leanh::LeanObject,
    mut v_cmp_4168_: *mut leanh::LeanObject,
    mut v_inst_4169_: *mut leanh::LeanObject,
    mut v_t_4170_: *mut leanh::LeanObject,
    mut v_k_4171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4172_ = leanh::lean_box(0);
    v___x_4173_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4168_,
        v_k_4171_,
        v___x_4172_,
        v_t_4170_,
    );
    return v___x_4173_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE___redArg(
    mut v_cmp_4174_: *mut leanh::LeanObject,
    mut v_t_4175_: *mut leanh::LeanObject,
    mut v_k_4176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4177_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_4174_, v_k_4176_, v_t_4175_);
    return v___x_4177_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE(
    mut v_00_u03b1_4178_: *mut leanh::LeanObject,
    mut v_00_u03b2_4179_: *mut leanh::LeanObject,
    mut v_cmp_4180_: *mut leanh::LeanObject,
    mut v_inst_4181_: *mut leanh::LeanObject,
    mut v_t_4182_: *mut leanh::LeanObject,
    mut v_k_4183_: *mut leanh::LeanObject,
    mut v_h_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4185_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_4180_, v_k_4183_, v_t_4182_);
    return v___x_4185_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT___redArg(
    mut v_cmp_4186_: *mut leanh::LeanObject,
    mut v_t_4187_: *mut leanh::LeanObject,
    mut v_k_4188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4189_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_4186_, v_k_4188_, v_t_4187_);
    return v___x_4189_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT(
    mut v_00_u03b1_4190_: *mut leanh::LeanObject,
    mut v_00_u03b2_4191_: *mut leanh::LeanObject,
    mut v_cmp_4192_: *mut leanh::LeanObject,
    mut v_inst_4193_: *mut leanh::LeanObject,
    mut v_t_4194_: *mut leanh::LeanObject,
    mut v_k_4195_: *mut leanh::LeanObject,
    mut v_h_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_4192_, v_k_4195_, v_t_4194_);
    return v___x_4197_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE___redArg(
    mut v_cmp_4198_: *mut leanh::LeanObject,
    mut v_t_4199_: *mut leanh::LeanObject,
    mut v_k_4200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4201_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_4198_, v_k_4200_, v_t_4199_);
    return v___x_4201_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE(
    mut v_00_u03b1_4202_: *mut leanh::LeanObject,
    mut v_00_u03b2_4203_: *mut leanh::LeanObject,
    mut v_cmp_4204_: *mut leanh::LeanObject,
    mut v_inst_4205_: *mut leanh::LeanObject,
    mut v_t_4206_: *mut leanh::LeanObject,
    mut v_k_4207_: *mut leanh::LeanObject,
    mut v_h_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_4204_, v_k_4207_, v_t_4206_);
    return v___x_4209_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT___redArg(
    mut v_cmp_4210_: *mut leanh::LeanObject,
    mut v_t_4211_: *mut leanh::LeanObject,
    mut v_k_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4213_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_4210_, v_k_4212_, v_t_4211_);
    return v___x_4213_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT(
    mut v_00_u03b1_4214_: *mut leanh::LeanObject,
    mut v_00_u03b2_4215_: *mut leanh::LeanObject,
    mut v_cmp_4216_: *mut leanh::LeanObject,
    mut v_inst_4217_: *mut leanh::LeanObject,
    mut v_t_4218_: *mut leanh::LeanObject,
    mut v_k_4219_: *mut leanh::LeanObject,
    mut v_h_4220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4221_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_4216_, v_k_4219_, v_t_4218_);
    return v___x_4221_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE_x21___redArg(
    mut v_cmp_4222_: *mut leanh::LeanObject,
    mut v_inst_4223_: *mut leanh::LeanObject,
    mut v_t_4224_: *mut leanh::LeanObject,
    mut v_k_4225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4226_ = leanh::lean_box(0);
    v___x_4227_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4222_,
        v_k_4225_,
        v___x_4226_,
        v_t_4224_,
    );
    if leanh::lean_obj_tag(v___x_4227_) == 0 {
        let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4228_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4229_ = l_panic___redArg(v_inst_4223_, v___x_4228_);
        return v___x_4229_;
    } else {
        let mut v_val_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4230_ = leanh::lean_ctor_get(v___x_4227_, 0);
        leanh::lean_inc(v_val_4230_);
        leanh::lean_dec_ref_known(v___x_4227_, 1);
        return v_val_4230_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE_x21___redArg___boxed(
    mut v_cmp_4231_: *mut leanh::LeanObject,
    mut v_inst_4232_: *mut leanh::LeanObject,
    mut v_t_4233_: *mut leanh::LeanObject,
    mut v_k_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4235_ =
        l_Std_ExtTreeMap_getKeyGE_x21___redArg(v_cmp_4231_, v_inst_4232_, v_t_4233_, v_k_4234_);
    leanh::lean_dec(v_inst_4232_);
    return v_res_4235_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE_x21(
    mut v_00_u03b1_4236_: *mut leanh::LeanObject,
    mut v_00_u03b2_4237_: *mut leanh::LeanObject,
    mut v_cmp_4238_: *mut leanh::LeanObject,
    mut v_inst_4239_: *mut leanh::LeanObject,
    mut v_inst_4240_: *mut leanh::LeanObject,
    mut v_t_4241_: *mut leanh::LeanObject,
    mut v_k_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4243_ = leanh::lean_box(0);
    v___x_4244_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4238_,
        v_k_4242_,
        v___x_4243_,
        v_t_4241_,
    );
    if leanh::lean_obj_tag(v___x_4244_) == 0 {
        let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4245_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4246_ = l_panic___redArg(v_inst_4240_, v___x_4245_);
        return v___x_4246_;
    } else {
        let mut v_val_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4247_ = leanh::lean_ctor_get(v___x_4244_, 0);
        leanh::lean_inc(v_val_4247_);
        leanh::lean_dec_ref_known(v___x_4244_, 1);
        return v_val_4247_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGE_x21___boxed(
    mut v_00_u03b1_4248_: *mut leanh::LeanObject,
    mut v_00_u03b2_4249_: *mut leanh::LeanObject,
    mut v_cmp_4250_: *mut leanh::LeanObject,
    mut v_inst_4251_: *mut leanh::LeanObject,
    mut v_inst_4252_: *mut leanh::LeanObject,
    mut v_t_4253_: *mut leanh::LeanObject,
    mut v_k_4254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Std_ExtTreeMap_getKeyGE_x21(
        v_00_u03b1_4248_,
        v_00_u03b2_4249_,
        v_cmp_4250_,
        v_inst_4251_,
        v_inst_4252_,
        v_t_4253_,
        v_k_4254_,
    );
    leanh::lean_dec(v_inst_4252_);
    return v_res_4255_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT_x21___redArg(
    mut v_cmp_4256_: *mut leanh::LeanObject,
    mut v_inst_4257_: *mut leanh::LeanObject,
    mut v_t_4258_: *mut leanh::LeanObject,
    mut v_k_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4260_ = leanh::lean_box(0);
    v___x_4261_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4256_,
        v_k_4259_,
        v___x_4260_,
        v_t_4258_,
    );
    if leanh::lean_obj_tag(v___x_4261_) == 0 {
        let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4262_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4263_ = l_panic___redArg(v_inst_4257_, v___x_4262_);
        return v___x_4263_;
    } else {
        let mut v_val_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4264_ = leanh::lean_ctor_get(v___x_4261_, 0);
        leanh::lean_inc(v_val_4264_);
        leanh::lean_dec_ref_known(v___x_4261_, 1);
        return v_val_4264_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT_x21___redArg___boxed(
    mut v_cmp_4265_: *mut leanh::LeanObject,
    mut v_inst_4266_: *mut leanh::LeanObject,
    mut v_t_4267_: *mut leanh::LeanObject,
    mut v_k_4268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4269_ =
        l_Std_ExtTreeMap_getKeyGT_x21___redArg(v_cmp_4265_, v_inst_4266_, v_t_4267_, v_k_4268_);
    leanh::lean_dec(v_inst_4266_);
    return v_res_4269_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT_x21(
    mut v_00_u03b1_4270_: *mut leanh::LeanObject,
    mut v_00_u03b2_4271_: *mut leanh::LeanObject,
    mut v_cmp_4272_: *mut leanh::LeanObject,
    mut v_inst_4273_: *mut leanh::LeanObject,
    mut v_inst_4274_: *mut leanh::LeanObject,
    mut v_t_4275_: *mut leanh::LeanObject,
    mut v_k_4276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4277_ = leanh::lean_box(0);
    v___x_4278_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4272_,
        v_k_4276_,
        v___x_4277_,
        v_t_4275_,
    );
    if leanh::lean_obj_tag(v___x_4278_) == 0 {
        let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4279_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4280_ = l_panic___redArg(v_inst_4274_, v___x_4279_);
        return v___x_4280_;
    } else {
        let mut v_val_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4281_ = leanh::lean_ctor_get(v___x_4278_, 0);
        leanh::lean_inc(v_val_4281_);
        leanh::lean_dec_ref_known(v___x_4278_, 1);
        return v_val_4281_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGT_x21___boxed(
    mut v_00_u03b1_4282_: *mut leanh::LeanObject,
    mut v_00_u03b2_4283_: *mut leanh::LeanObject,
    mut v_cmp_4284_: *mut leanh::LeanObject,
    mut v_inst_4285_: *mut leanh::LeanObject,
    mut v_inst_4286_: *mut leanh::LeanObject,
    mut v_t_4287_: *mut leanh::LeanObject,
    mut v_k_4288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4289_ = l_Std_ExtTreeMap_getKeyGT_x21(
        v_00_u03b1_4282_,
        v_00_u03b2_4283_,
        v_cmp_4284_,
        v_inst_4285_,
        v_inst_4286_,
        v_t_4287_,
        v_k_4288_,
    );
    leanh::lean_dec(v_inst_4286_);
    return v_res_4289_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE_x21___redArg(
    mut v_cmp_4290_: *mut leanh::LeanObject,
    mut v_inst_4291_: *mut leanh::LeanObject,
    mut v_t_4292_: *mut leanh::LeanObject,
    mut v_k_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = leanh::lean_box(0);
    v___x_4295_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4290_,
        v_k_4293_,
        v___x_4294_,
        v_t_4292_,
    );
    if leanh::lean_obj_tag(v___x_4295_) == 0 {
        let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4296_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4297_ = l_panic___redArg(v_inst_4291_, v___x_4296_);
        return v___x_4297_;
    } else {
        let mut v_val_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4298_ = leanh::lean_ctor_get(v___x_4295_, 0);
        leanh::lean_inc(v_val_4298_);
        leanh::lean_dec_ref_known(v___x_4295_, 1);
        return v_val_4298_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE_x21___redArg___boxed(
    mut v_cmp_4299_: *mut leanh::LeanObject,
    mut v_inst_4300_: *mut leanh::LeanObject,
    mut v_t_4301_: *mut leanh::LeanObject,
    mut v_k_4302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4303_ =
        l_Std_ExtTreeMap_getKeyLE_x21___redArg(v_cmp_4299_, v_inst_4300_, v_t_4301_, v_k_4302_);
    leanh::lean_dec(v_inst_4300_);
    return v_res_4303_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE_x21(
    mut v_00_u03b1_4304_: *mut leanh::LeanObject,
    mut v_00_u03b2_4305_: *mut leanh::LeanObject,
    mut v_cmp_4306_: *mut leanh::LeanObject,
    mut v_inst_4307_: *mut leanh::LeanObject,
    mut v_inst_4308_: *mut leanh::LeanObject,
    mut v_t_4309_: *mut leanh::LeanObject,
    mut v_k_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4311_ = leanh::lean_box(0);
    v___x_4312_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4306_,
        v_k_4310_,
        v___x_4311_,
        v_t_4309_,
    );
    if leanh::lean_obj_tag(v___x_4312_) == 0 {
        let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4313_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4314_ = l_panic___redArg(v_inst_4308_, v___x_4313_);
        return v___x_4314_;
    } else {
        let mut v_val_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4315_ = leanh::lean_ctor_get(v___x_4312_, 0);
        leanh::lean_inc(v_val_4315_);
        leanh::lean_dec_ref_known(v___x_4312_, 1);
        return v_val_4315_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLE_x21___boxed(
    mut v_00_u03b1_4316_: *mut leanh::LeanObject,
    mut v_00_u03b2_4317_: *mut leanh::LeanObject,
    mut v_cmp_4318_: *mut leanh::LeanObject,
    mut v_inst_4319_: *mut leanh::LeanObject,
    mut v_inst_4320_: *mut leanh::LeanObject,
    mut v_t_4321_: *mut leanh::LeanObject,
    mut v_k_4322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4323_ = l_Std_ExtTreeMap_getKeyLE_x21(
        v_00_u03b1_4316_,
        v_00_u03b2_4317_,
        v_cmp_4318_,
        v_inst_4319_,
        v_inst_4320_,
        v_t_4321_,
        v_k_4322_,
    );
    leanh::lean_dec(v_inst_4320_);
    return v_res_4323_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT_x21___redArg(
    mut v_cmp_4324_: *mut leanh::LeanObject,
    mut v_inst_4325_: *mut leanh::LeanObject,
    mut v_t_4326_: *mut leanh::LeanObject,
    mut v_k_4327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4328_ = leanh::lean_box(0);
    v___x_4329_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4324_,
        v_k_4327_,
        v___x_4328_,
        v_t_4326_,
    );
    if leanh::lean_obj_tag(v___x_4329_) == 0 {
        let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4330_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4331_ = l_panic___redArg(v_inst_4325_, v___x_4330_);
        return v___x_4331_;
    } else {
        let mut v_val_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4332_ = leanh::lean_ctor_get(v___x_4329_, 0);
        leanh::lean_inc(v_val_4332_);
        leanh::lean_dec_ref_known(v___x_4329_, 1);
        return v_val_4332_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT_x21___redArg___boxed(
    mut v_cmp_4333_: *mut leanh::LeanObject,
    mut v_inst_4334_: *mut leanh::LeanObject,
    mut v_t_4335_: *mut leanh::LeanObject,
    mut v_k_4336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4337_ =
        l_Std_ExtTreeMap_getKeyLT_x21___redArg(v_cmp_4333_, v_inst_4334_, v_t_4335_, v_k_4336_);
    leanh::lean_dec(v_inst_4334_);
    return v_res_4337_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT_x21(
    mut v_00_u03b1_4338_: *mut leanh::LeanObject,
    mut v_00_u03b2_4339_: *mut leanh::LeanObject,
    mut v_cmp_4340_: *mut leanh::LeanObject,
    mut v_inst_4341_: *mut leanh::LeanObject,
    mut v_inst_4342_: *mut leanh::LeanObject,
    mut v_t_4343_: *mut leanh::LeanObject,
    mut v_k_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ = leanh::lean_box(0);
    v___x_4346_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4340_,
        v_k_4344_,
        v___x_4345_,
        v_t_4343_,
    );
    if leanh::lean_obj_tag(v___x_4346_) == 0 {
        let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4347_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4348_ = l_panic___redArg(v_inst_4342_, v___x_4347_);
        return v___x_4348_;
    } else {
        let mut v_val_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4349_ = leanh::lean_ctor_get(v___x_4346_, 0);
        leanh::lean_inc(v_val_4349_);
        leanh::lean_dec_ref_known(v___x_4346_, 1);
        return v_val_4349_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLT_x21___boxed(
    mut v_00_u03b1_4350_: *mut leanh::LeanObject,
    mut v_00_u03b2_4351_: *mut leanh::LeanObject,
    mut v_cmp_4352_: *mut leanh::LeanObject,
    mut v_inst_4353_: *mut leanh::LeanObject,
    mut v_inst_4354_: *mut leanh::LeanObject,
    mut v_t_4355_: *mut leanh::LeanObject,
    mut v_k_4356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4357_ = l_Std_ExtTreeMap_getKeyLT_x21(
        v_00_u03b1_4350_,
        v_00_u03b2_4351_,
        v_cmp_4352_,
        v_inst_4353_,
        v_inst_4354_,
        v_t_4355_,
        v_k_4356_,
    );
    leanh::lean_dec(v_inst_4354_);
    return v_res_4357_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGED___redArg(
    mut v_cmp_4358_: *mut leanh::LeanObject,
    mut v_t_4359_: *mut leanh::LeanObject,
    mut v_k_4360_: *mut leanh::LeanObject,
    mut v_fallback_4361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = leanh::lean_box(0);
    v___x_4363_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4358_,
        v_k_4360_,
        v___x_4362_,
        v_t_4359_,
    );
    if leanh::lean_obj_tag(v___x_4363_) == 0 {
        leanh::lean_inc(v_fallback_4361_);
        return v_fallback_4361_;
    } else {
        let mut v_val_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4364_ = leanh::lean_ctor_get(v___x_4363_, 0);
        leanh::lean_inc(v_val_4364_);
        leanh::lean_dec_ref_known(v___x_4363_, 1);
        return v_val_4364_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGED___redArg___boxed(
    mut v_cmp_4365_: *mut leanh::LeanObject,
    mut v_t_4366_: *mut leanh::LeanObject,
    mut v_k_4367_: *mut leanh::LeanObject,
    mut v_fallback_4368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4369_ =
        l_Std_ExtTreeMap_getKeyGED___redArg(v_cmp_4365_, v_t_4366_, v_k_4367_, v_fallback_4368_);
    leanh::lean_dec(v_fallback_4368_);
    return v_res_4369_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGED(
    mut v_00_u03b1_4370_: *mut leanh::LeanObject,
    mut v_00_u03b2_4371_: *mut leanh::LeanObject,
    mut v_cmp_4372_: *mut leanh::LeanObject,
    mut v_inst_4373_: *mut leanh::LeanObject,
    mut v_t_4374_: *mut leanh::LeanObject,
    mut v_k_4375_: *mut leanh::LeanObject,
    mut v_fallback_4376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = leanh::lean_box(0);
    v___x_4378_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_4372_,
        v_k_4375_,
        v___x_4377_,
        v_t_4374_,
    );
    if leanh::lean_obj_tag(v___x_4378_) == 0 {
        leanh::lean_inc(v_fallback_4376_);
        return v_fallback_4376_;
    } else {
        let mut v_val_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4379_ = leanh::lean_ctor_get(v___x_4378_, 0);
        leanh::lean_inc(v_val_4379_);
        leanh::lean_dec_ref_known(v___x_4378_, 1);
        return v_val_4379_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGED___boxed(
    mut v_00_u03b1_4380_: *mut leanh::LeanObject,
    mut v_00_u03b2_4381_: *mut leanh::LeanObject,
    mut v_cmp_4382_: *mut leanh::LeanObject,
    mut v_inst_4383_: *mut leanh::LeanObject,
    mut v_t_4384_: *mut leanh::LeanObject,
    mut v_k_4385_: *mut leanh::LeanObject,
    mut v_fallback_4386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4387_ = l_Std_ExtTreeMap_getKeyGED(
        v_00_u03b1_4380_,
        v_00_u03b2_4381_,
        v_cmp_4382_,
        v_inst_4383_,
        v_t_4384_,
        v_k_4385_,
        v_fallback_4386_,
    );
    leanh::lean_dec(v_fallback_4386_);
    return v_res_4387_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGTD___redArg(
    mut v_cmp_4388_: *mut leanh::LeanObject,
    mut v_t_4389_: *mut leanh::LeanObject,
    mut v_k_4390_: *mut leanh::LeanObject,
    mut v_fallback_4391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4392_ = leanh::lean_box(0);
    v___x_4393_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4388_,
        v_k_4390_,
        v___x_4392_,
        v_t_4389_,
    );
    if leanh::lean_obj_tag(v___x_4393_) == 0 {
        leanh::lean_inc(v_fallback_4391_);
        return v_fallback_4391_;
    } else {
        let mut v_val_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4394_ = leanh::lean_ctor_get(v___x_4393_, 0);
        leanh::lean_inc(v_val_4394_);
        leanh::lean_dec_ref_known(v___x_4393_, 1);
        return v_val_4394_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGTD___redArg___boxed(
    mut v_cmp_4395_: *mut leanh::LeanObject,
    mut v_t_4396_: *mut leanh::LeanObject,
    mut v_k_4397_: *mut leanh::LeanObject,
    mut v_fallback_4398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4399_ =
        l_Std_ExtTreeMap_getKeyGTD___redArg(v_cmp_4395_, v_t_4396_, v_k_4397_, v_fallback_4398_);
    leanh::lean_dec(v_fallback_4398_);
    return v_res_4399_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGTD(
    mut v_00_u03b1_4400_: *mut leanh::LeanObject,
    mut v_00_u03b2_4401_: *mut leanh::LeanObject,
    mut v_cmp_4402_: *mut leanh::LeanObject,
    mut v_inst_4403_: *mut leanh::LeanObject,
    mut v_t_4404_: *mut leanh::LeanObject,
    mut v_k_4405_: *mut leanh::LeanObject,
    mut v_fallback_4406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4407_ = leanh::lean_box(0);
    v___x_4408_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_4402_,
        v_k_4405_,
        v___x_4407_,
        v_t_4404_,
    );
    if leanh::lean_obj_tag(v___x_4408_) == 0 {
        leanh::lean_inc(v_fallback_4406_);
        return v_fallback_4406_;
    } else {
        let mut v_val_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4409_ = leanh::lean_ctor_get(v___x_4408_, 0);
        leanh::lean_inc(v_val_4409_);
        leanh::lean_dec_ref_known(v___x_4408_, 1);
        return v_val_4409_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyGTD___boxed(
    mut v_00_u03b1_4410_: *mut leanh::LeanObject,
    mut v_00_u03b2_4411_: *mut leanh::LeanObject,
    mut v_cmp_4412_: *mut leanh::LeanObject,
    mut v_inst_4413_: *mut leanh::LeanObject,
    mut v_t_4414_: *mut leanh::LeanObject,
    mut v_k_4415_: *mut leanh::LeanObject,
    mut v_fallback_4416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4417_ = l_Std_ExtTreeMap_getKeyGTD(
        v_00_u03b1_4410_,
        v_00_u03b2_4411_,
        v_cmp_4412_,
        v_inst_4413_,
        v_t_4414_,
        v_k_4415_,
        v_fallback_4416_,
    );
    leanh::lean_dec(v_fallback_4416_);
    return v_res_4417_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLED___redArg(
    mut v_cmp_4418_: *mut leanh::LeanObject,
    mut v_t_4419_: *mut leanh::LeanObject,
    mut v_k_4420_: *mut leanh::LeanObject,
    mut v_fallback_4421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4422_ = leanh::lean_box(0);
    v___x_4423_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4418_,
        v_k_4420_,
        v___x_4422_,
        v_t_4419_,
    );
    if leanh::lean_obj_tag(v___x_4423_) == 0 {
        leanh::lean_inc(v_fallback_4421_);
        return v_fallback_4421_;
    } else {
        let mut v_val_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4424_ = leanh::lean_ctor_get(v___x_4423_, 0);
        leanh::lean_inc(v_val_4424_);
        leanh::lean_dec_ref_known(v___x_4423_, 1);
        return v_val_4424_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLED___redArg___boxed(
    mut v_cmp_4425_: *mut leanh::LeanObject,
    mut v_t_4426_: *mut leanh::LeanObject,
    mut v_k_4427_: *mut leanh::LeanObject,
    mut v_fallback_4428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4429_ =
        l_Std_ExtTreeMap_getKeyLED___redArg(v_cmp_4425_, v_t_4426_, v_k_4427_, v_fallback_4428_);
    leanh::lean_dec(v_fallback_4428_);
    return v_res_4429_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLED(
    mut v_00_u03b1_4430_: *mut leanh::LeanObject,
    mut v_00_u03b2_4431_: *mut leanh::LeanObject,
    mut v_cmp_4432_: *mut leanh::LeanObject,
    mut v_inst_4433_: *mut leanh::LeanObject,
    mut v_t_4434_: *mut leanh::LeanObject,
    mut v_k_4435_: *mut leanh::LeanObject,
    mut v_fallback_4436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4437_ = leanh::lean_box(0);
    v___x_4438_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_4432_,
        v_k_4435_,
        v___x_4437_,
        v_t_4434_,
    );
    if leanh::lean_obj_tag(v___x_4438_) == 0 {
        leanh::lean_inc(v_fallback_4436_);
        return v_fallback_4436_;
    } else {
        let mut v_val_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4439_ = leanh::lean_ctor_get(v___x_4438_, 0);
        leanh::lean_inc(v_val_4439_);
        leanh::lean_dec_ref_known(v___x_4438_, 1);
        return v_val_4439_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLED___boxed(
    mut v_00_u03b1_4440_: *mut leanh::LeanObject,
    mut v_00_u03b2_4441_: *mut leanh::LeanObject,
    mut v_cmp_4442_: *mut leanh::LeanObject,
    mut v_inst_4443_: *mut leanh::LeanObject,
    mut v_t_4444_: *mut leanh::LeanObject,
    mut v_k_4445_: *mut leanh::LeanObject,
    mut v_fallback_4446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4447_ = l_Std_ExtTreeMap_getKeyLED(
        v_00_u03b1_4440_,
        v_00_u03b2_4441_,
        v_cmp_4442_,
        v_inst_4443_,
        v_t_4444_,
        v_k_4445_,
        v_fallback_4446_,
    );
    leanh::lean_dec(v_fallback_4446_);
    return v_res_4447_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLTD___redArg(
    mut v_cmp_4448_: *mut leanh::LeanObject,
    mut v_t_4449_: *mut leanh::LeanObject,
    mut v_k_4450_: *mut leanh::LeanObject,
    mut v_fallback_4451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4452_ = leanh::lean_box(0);
    v___x_4453_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4448_,
        v_k_4450_,
        v___x_4452_,
        v_t_4449_,
    );
    if leanh::lean_obj_tag(v___x_4453_) == 0 {
        leanh::lean_inc(v_fallback_4451_);
        return v_fallback_4451_;
    } else {
        let mut v_val_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4454_ = leanh::lean_ctor_get(v___x_4453_, 0);
        leanh::lean_inc(v_val_4454_);
        leanh::lean_dec_ref_known(v___x_4453_, 1);
        return v_val_4454_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLTD___redArg___boxed(
    mut v_cmp_4455_: *mut leanh::LeanObject,
    mut v_t_4456_: *mut leanh::LeanObject,
    mut v_k_4457_: *mut leanh::LeanObject,
    mut v_fallback_4458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4459_ =
        l_Std_ExtTreeMap_getKeyLTD___redArg(v_cmp_4455_, v_t_4456_, v_k_4457_, v_fallback_4458_);
    leanh::lean_dec(v_fallback_4458_);
    return v_res_4459_;
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLTD(
    mut v_00_u03b1_4460_: *mut leanh::LeanObject,
    mut v_00_u03b2_4461_: *mut leanh::LeanObject,
    mut v_cmp_4462_: *mut leanh::LeanObject,
    mut v_inst_4463_: *mut leanh::LeanObject,
    mut v_t_4464_: *mut leanh::LeanObject,
    mut v_k_4465_: *mut leanh::LeanObject,
    mut v_fallback_4466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4467_ = leanh::lean_box(0);
    v___x_4468_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_4462_,
        v_k_4465_,
        v___x_4467_,
        v_t_4464_,
    );
    if leanh::lean_obj_tag(v___x_4468_) == 0 {
        leanh::lean_inc(v_fallback_4466_);
        return v_fallback_4466_;
    } else {
        let mut v_val_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4469_ = leanh::lean_ctor_get(v___x_4468_, 0);
        leanh::lean_inc(v_val_4469_);
        leanh::lean_dec_ref_known(v___x_4468_, 1);
        return v_val_4469_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_getKeyLTD___boxed(
    mut v_00_u03b1_4470_: *mut leanh::LeanObject,
    mut v_00_u03b2_4471_: *mut leanh::LeanObject,
    mut v_cmp_4472_: *mut leanh::LeanObject,
    mut v_inst_4473_: *mut leanh::LeanObject,
    mut v_t_4474_: *mut leanh::LeanObject,
    mut v_k_4475_: *mut leanh::LeanObject,
    mut v_fallback_4476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Std_ExtTreeMap_getKeyLTD(
        v_00_u03b1_4470_,
        v_00_u03b2_4471_,
        v_cmp_4472_,
        v_inst_4473_,
        v_t_4474_,
        v_k_4475_,
        v_fallback_4476_,
    );
    leanh::lean_dec(v_fallback_4476_);
    return v_res_4477_;
}
pub unsafe fn l_Std_ExtTreeMap_filter___redArg(
    mut v_f_4478_: *mut leanh::LeanObject,
    mut v_m_4479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4480_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_4478_, v_m_4479_);
    return v___x_4480_;
}
pub unsafe fn l_Std_ExtTreeMap_filter(
    mut v_00_u03b1_4481_: *mut leanh::LeanObject,
    mut v_00_u03b2_4482_: *mut leanh::LeanObject,
    mut v_cmp_4483_: *mut leanh::LeanObject,
    mut v_f_4484_: *mut leanh::LeanObject,
    mut v_m_4485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_4484_, v_m_4485_);
    return v___x_4486_;
}
pub unsafe fn l_Std_ExtTreeMap_filter___boxed(
    mut v_00_u03b1_4487_: *mut leanh::LeanObject,
    mut v_00_u03b2_4488_: *mut leanh::LeanObject,
    mut v_cmp_4489_: *mut leanh::LeanObject,
    mut v_f_4490_: *mut leanh::LeanObject,
    mut v_m_4491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Std_ExtTreeMap_filter(
        v_00_u03b1_4487_,
        v_00_u03b2_4488_,
        v_cmp_4489_,
        v_f_4490_,
        v_m_4491_,
    );
    leanh::lean_dec_ref(v_cmp_4489_);
    return v_res_4492_;
}
pub unsafe fn l_Std_ExtTreeMap_filterMap___redArg(
    mut v_f_4493_: *mut leanh::LeanObject,
    mut v_m_4494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4495_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_4493_, v_m_4494_);
    return v___x_4495_;
}
pub unsafe fn l_Std_ExtTreeMap_filterMap(
    mut v_00_u03b1_4496_: *mut leanh::LeanObject,
    mut v_00_u03b2_4497_: *mut leanh::LeanObject,
    mut v_00_u03b3_4498_: *mut leanh::LeanObject,
    mut v_cmp_4499_: *mut leanh::LeanObject,
    mut v_f_4500_: *mut leanh::LeanObject,
    mut v_m_4501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4502_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_4500_, v_m_4501_);
    return v___x_4502_;
}
pub unsafe fn l_Std_ExtTreeMap_filterMap___boxed(
    mut v_00_u03b1_4503_: *mut leanh::LeanObject,
    mut v_00_u03b2_4504_: *mut leanh::LeanObject,
    mut v_00_u03b3_4505_: *mut leanh::LeanObject,
    mut v_cmp_4506_: *mut leanh::LeanObject,
    mut v_f_4507_: *mut leanh::LeanObject,
    mut v_m_4508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4509_ = l_Std_ExtTreeMap_filterMap(
        v_00_u03b1_4503_,
        v_00_u03b2_4504_,
        v_00_u03b3_4505_,
        v_cmp_4506_,
        v_f_4507_,
        v_m_4508_,
    );
    leanh::lean_dec_ref(v_cmp_4506_);
    return v_res_4509_;
}
pub unsafe fn l_Std_ExtTreeMap_map___redArg(
    mut v_f_4510_: *mut leanh::LeanObject,
    mut v_t_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_4510_, v_t_4511_);
    return v___x_4512_;
}
pub unsafe fn l_Std_ExtTreeMap_map(
    mut v_00_u03b1_4513_: *mut leanh::LeanObject,
    mut v_00_u03b2_4514_: *mut leanh::LeanObject,
    mut v_00_u03b3_4515_: *mut leanh::LeanObject,
    mut v_cmp_4516_: *mut leanh::LeanObject,
    mut v_f_4517_: *mut leanh::LeanObject,
    mut v_t_4518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_4517_, v_t_4518_);
    return v___x_4519_;
}
pub unsafe fn l_Std_ExtTreeMap_map___boxed(
    mut v_00_u03b1_4520_: *mut leanh::LeanObject,
    mut v_00_u03b2_4521_: *mut leanh::LeanObject,
    mut v_00_u03b3_4522_: *mut leanh::LeanObject,
    mut v_cmp_4523_: *mut leanh::LeanObject,
    mut v_f_4524_: *mut leanh::LeanObject,
    mut v_t_4525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4526_ = l_Std_ExtTreeMap_map(
        v_00_u03b1_4520_,
        v_00_u03b2_4521_,
        v_00_u03b3_4522_,
        v_cmp_4523_,
        v_f_4524_,
        v_t_4525_,
    );
    leanh::lean_dec_ref(v_cmp_4523_);
    return v_res_4526_;
}
pub unsafe fn l_Std_ExtTreeMap_foldlM___redArg(
    mut v_inst_4527_: *mut leanh::LeanObject,
    mut v_f_4528_: *mut leanh::LeanObject,
    mut v_init_4529_: *mut leanh::LeanObject,
    mut v_t_4530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4527_,
        v_f_4528_,
        v_init_4529_,
        v_t_4530_,
    );
    return v___x_4531_;
}
pub unsafe fn l_Std_ExtTreeMap_foldlM(
    mut v_00_u03b1_4532_: *mut leanh::LeanObject,
    mut v_00_u03b2_4533_: *mut leanh::LeanObject,
    mut v_cmp_4534_: *mut leanh::LeanObject,
    mut v_00_u03b4_4535_: *mut leanh::LeanObject,
    mut v_m_4536_: *mut leanh::LeanObject,
    mut v_inst_4537_: *mut leanh::LeanObject,
    mut v_inst_4538_: *mut leanh::LeanObject,
    mut v_inst_4539_: *mut leanh::LeanObject,
    mut v_f_4540_: *mut leanh::LeanObject,
    mut v_init_4541_: *mut leanh::LeanObject,
    mut v_t_4542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4543_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4537_,
        v_f_4540_,
        v_init_4541_,
        v_t_4542_,
    );
    return v___x_4543_;
}
pub unsafe fn l_Std_ExtTreeMap_foldlM___boxed(
    mut v_00_u03b1_4544_: *mut leanh::LeanObject,
    mut v_00_u03b2_4545_: *mut leanh::LeanObject,
    mut v_cmp_4546_: *mut leanh::LeanObject,
    mut v_00_u03b4_4547_: *mut leanh::LeanObject,
    mut v_m_4548_: *mut leanh::LeanObject,
    mut v_inst_4549_: *mut leanh::LeanObject,
    mut v_inst_4550_: *mut leanh::LeanObject,
    mut v_inst_4551_: *mut leanh::LeanObject,
    mut v_f_4552_: *mut leanh::LeanObject,
    mut v_init_4553_: *mut leanh::LeanObject,
    mut v_t_4554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4555_ = l_Std_ExtTreeMap_foldlM(
        v_00_u03b1_4544_,
        v_00_u03b2_4545_,
        v_cmp_4546_,
        v_00_u03b4_4547_,
        v_m_4548_,
        v_inst_4549_,
        v_inst_4550_,
        v_inst_4551_,
        v_f_4552_,
        v_init_4553_,
        v_t_4554_,
    );
    leanh::lean_dec_ref(v_cmp_4546_);
    return v_res_4555_;
}
pub unsafe fn l_Std_ExtTreeMap_foldl___redArg(
    mut v_f_4556_: *mut leanh::LeanObject,
    mut v_init_4557_: *mut leanh::LeanObject,
    mut v_t_4558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4559_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_4556_, v_init_4557_, v_t_4558_);
    return v___x_4559_;
}
pub unsafe fn l_Std_ExtTreeMap_foldl(
    mut v_00_u03b1_4560_: *mut leanh::LeanObject,
    mut v_00_u03b2_4561_: *mut leanh::LeanObject,
    mut v_cmp_4562_: *mut leanh::LeanObject,
    mut v_00_u03b4_4563_: *mut leanh::LeanObject,
    mut v_inst_4564_: *mut leanh::LeanObject,
    mut v_f_4565_: *mut leanh::LeanObject,
    mut v_init_4566_: *mut leanh::LeanObject,
    mut v_t_4567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4568_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_4565_, v_init_4566_, v_t_4567_);
    return v___x_4568_;
}
pub unsafe fn l_Std_ExtTreeMap_foldl___boxed(
    mut v_00_u03b1_4569_: *mut leanh::LeanObject,
    mut v_00_u03b2_4570_: *mut leanh::LeanObject,
    mut v_cmp_4571_: *mut leanh::LeanObject,
    mut v_00_u03b4_4572_: *mut leanh::LeanObject,
    mut v_inst_4573_: *mut leanh::LeanObject,
    mut v_f_4574_: *mut leanh::LeanObject,
    mut v_init_4575_: *mut leanh::LeanObject,
    mut v_t_4576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4577_ = l_Std_ExtTreeMap_foldl(
        v_00_u03b1_4569_,
        v_00_u03b2_4570_,
        v_cmp_4571_,
        v_00_u03b4_4572_,
        v_inst_4573_,
        v_f_4574_,
        v_init_4575_,
        v_t_4576_,
    );
    leanh::lean_dec_ref(v_cmp_4571_);
    return v_res_4577_;
}
pub unsafe fn l_Std_ExtTreeMap_foldrM___redArg(
    mut v_inst_4578_: *mut leanh::LeanObject,
    mut v_f_4579_: *mut leanh::LeanObject,
    mut v_init_4580_: *mut leanh::LeanObject,
    mut v_t_4581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_4578_,
        v_f_4579_,
        v_init_4580_,
        v_t_4581_,
    );
    return v___x_4582_;
}
pub unsafe fn l_Std_ExtTreeMap_foldrM(
    mut v_00_u03b1_4583_: *mut leanh::LeanObject,
    mut v_00_u03b2_4584_: *mut leanh::LeanObject,
    mut v_cmp_4585_: *mut leanh::LeanObject,
    mut v_00_u03b4_4586_: *mut leanh::LeanObject,
    mut v_m_4587_: *mut leanh::LeanObject,
    mut v_inst_4588_: *mut leanh::LeanObject,
    mut v_inst_4589_: *mut leanh::LeanObject,
    mut v_inst_4590_: *mut leanh::LeanObject,
    mut v_f_4591_: *mut leanh::LeanObject,
    mut v_init_4592_: *mut leanh::LeanObject,
    mut v_t_4593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4594_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_4588_,
        v_f_4591_,
        v_init_4592_,
        v_t_4593_,
    );
    return v___x_4594_;
}
pub unsafe fn l_Std_ExtTreeMap_foldrM___boxed(
    mut v_00_u03b1_4595_: *mut leanh::LeanObject,
    mut v_00_u03b2_4596_: *mut leanh::LeanObject,
    mut v_cmp_4597_: *mut leanh::LeanObject,
    mut v_00_u03b4_4598_: *mut leanh::LeanObject,
    mut v_m_4599_: *mut leanh::LeanObject,
    mut v_inst_4600_: *mut leanh::LeanObject,
    mut v_inst_4601_: *mut leanh::LeanObject,
    mut v_inst_4602_: *mut leanh::LeanObject,
    mut v_f_4603_: *mut leanh::LeanObject,
    mut v_init_4604_: *mut leanh::LeanObject,
    mut v_t_4605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_Std_ExtTreeMap_foldrM(
        v_00_u03b1_4595_,
        v_00_u03b2_4596_,
        v_cmp_4597_,
        v_00_u03b4_4598_,
        v_m_4599_,
        v_inst_4600_,
        v_inst_4601_,
        v_inst_4602_,
        v_f_4603_,
        v_init_4604_,
        v_t_4605_,
    );
    leanh::lean_dec_ref(v_cmp_4597_);
    return v_res_4606_;
}
pub unsafe fn l_Std_ExtTreeMap_foldr___redArg___lam__0(
    mut v_f_4607_: *mut leanh::LeanObject,
    mut v_x1_4608_: *mut leanh::LeanObject,
    mut v_x2_4609_: *mut leanh::LeanObject,
    mut v_x3_4610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4611_ = leanh::lean_apply_3(v_f_4607_, v_x1_4608_, v_x2_4609_, v_x3_4610_);
    return v___x_4611_;
}
pub unsafe fn l_Std_ExtTreeMap_foldr___redArg(
    mut v_f_4631_: *mut leanh::LeanObject,
    mut v_init_4632_: *mut leanh::LeanObject,
    mut v_t_4633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4634_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4634_, 0, v_f_4631_);
    v___x_4635_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_4636_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4635_,
        v___f_4634_,
        v_init_4632_,
        v_t_4633_,
    );
    return v___x_4636_;
}
pub unsafe fn l_Std_ExtTreeMap_foldr(
    mut v_00_u03b1_4637_: *mut leanh::LeanObject,
    mut v_00_u03b2_4638_: *mut leanh::LeanObject,
    mut v_cmp_4639_: *mut leanh::LeanObject,
    mut v_00_u03b4_4640_: *mut leanh::LeanObject,
    mut v_inst_4641_: *mut leanh::LeanObject,
    mut v_f_4642_: *mut leanh::LeanObject,
    mut v_init_4643_: *mut leanh::LeanObject,
    mut v_t_4644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4645_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4645_, 0, v_f_4642_);
    v___x_4646_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_4647_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4646_,
        v___f_4645_,
        v_init_4643_,
        v_t_4644_,
    );
    return v___x_4647_;
}
pub unsafe fn l_Std_ExtTreeMap_foldr___boxed(
    mut v_00_u03b1_4648_: *mut leanh::LeanObject,
    mut v_00_u03b2_4649_: *mut leanh::LeanObject,
    mut v_cmp_4650_: *mut leanh::LeanObject,
    mut v_00_u03b4_4651_: *mut leanh::LeanObject,
    mut v_inst_4652_: *mut leanh::LeanObject,
    mut v_f_4653_: *mut leanh::LeanObject,
    mut v_init_4654_: *mut leanh::LeanObject,
    mut v_t_4655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4656_ = l_Std_ExtTreeMap_foldr(
        v_00_u03b1_4648_,
        v_00_u03b2_4649_,
        v_cmp_4650_,
        v_00_u03b4_4651_,
        v_inst_4652_,
        v_f_4653_,
        v_init_4654_,
        v_t_4655_,
    );
    leanh::lean_dec_ref(v_cmp_4650_);
    return v_res_4656_;
}
pub unsafe fn l_Std_ExtTreeMap_partition___redArg___lam__0(
    mut v_f_4657_: *mut leanh::LeanObject,
    mut v_cmp_4658_: *mut leanh::LeanObject,
    mut v_x_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
    mut v_b_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: u8 = 0;
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4662_ = leanh::lean_ctor_get(v_x_4659_, 0);
                v_snd_4663_ = leanh::lean_ctor_get(v_x_4659_, 1);
                v_isSharedCheck_4677_ = (!leanh::lean_is_exclusive(v_x_4659_)) as u8;
                if v_isSharedCheck_4677_ == 0 {
                    v___x_4665_ = v_x_4659_;
                    v_isShared_4666_ = v_isSharedCheck_4677_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4663_);
                    leanh::lean_inc(v_fst_4662_);
                    leanh::lean_dec(v_x_4659_);
                    v___x_4665_ = leanh::lean_box(0);
                    v_isShared_4666_ = v_isSharedCheck_4677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_b_4661_);
                leanh::lean_inc(v_a_4660_);
                v___x_4667_ = leanh::lean_apply_2(v_f_4657_, v_a_4660_, v_b_4661_);
                v___x_4668_ = (leanh::lean_unbox(v___x_4667_) as u8);
                if v___x_4668_ == 0 {
                    v___x_4669_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_4658_,
                        v_a_4660_,
                        v_b_4661_,
                        v_snd_4663_,
                    );
                    if v_isShared_4666_ == 0 {
                        leanh::lean_ctor_set(v___x_4665_, 1, v___x_4669_);
                        v___x_4671_ = v___x_4665_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4672_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_fst_4662_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 1, v___x_4669_);
                        v___x_4671_ = v_reuseFailAlloc_4672_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4673_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_4658_,
                        v_a_4660_,
                        v_b_4661_,
                        v_fst_4662_,
                    );
                    if v_isShared_4666_ == 0 {
                        leanh::lean_ctor_set(v___x_4665_, 0, v___x_4673_);
                        v___x_4675_ = v___x_4665_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4673_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_snd_4663_);
                        v___x_4675_ = v_reuseFailAlloc_4676_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4671_;
            }
            3 => {
                return v___x_4675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_partition___redArg(
    mut v_cmp_4680_: *mut leanh::LeanObject,
    mut v_f_4681_: *mut leanh::LeanObject,
    mut v_t_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4690_: u8 = 0;
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4683_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_4683_, 0, v_f_4681_);
                leanh::lean_closure_set(v___f_4683_, 1, v_cmp_4680_);
                v___x_4684_ = l_Std_ExtTreeMap_partition___redArg___closed__0;
                v_p_4685_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4683_,
                    v___x_4684_,
                    v_t_4682_,
                );
                v_fst_4686_ = leanh::lean_ctor_get(v_p_4685_, 0);
                v_snd_4687_ = leanh::lean_ctor_get(v_p_4685_, 1);
                v_isSharedCheck_4694_ = (!leanh::lean_is_exclusive(v_p_4685_)) as u8;
                if v_isSharedCheck_4694_ == 0 {
                    v___x_4689_ = v_p_4685_;
                    v_isShared_4690_ = v_isSharedCheck_4694_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4687_);
                    leanh::lean_inc(v_fst_4686_);
                    leanh::lean_dec(v_p_4685_);
                    v___x_4689_ = leanh::lean_box(0);
                    v_isShared_4690_ = v_isSharedCheck_4694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4690_ == 0 {
                    v___x_4692_ = v___x_4689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_fst_4686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_snd_4687_);
                    v___x_4692_ = v_reuseFailAlloc_4693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_partition(
    mut v_00_u03b1_4695_: *mut leanh::LeanObject,
    mut v_00_u03b2_4696_: *mut leanh::LeanObject,
    mut v_cmp_4697_: *mut leanh::LeanObject,
    mut v_inst_4698_: *mut leanh::LeanObject,
    mut v_f_4699_: *mut leanh::LeanObject,
    mut v_t_4700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4708_: u8 = 0;
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4712_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4701_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_4701_, 0, v_f_4699_);
                leanh::lean_closure_set(v___f_4701_, 1, v_cmp_4697_);
                v___x_4702_ = l_Std_ExtTreeMap_partition___redArg___closed__0;
                v_p_4703_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4701_,
                    v___x_4702_,
                    v_t_4700_,
                );
                v_fst_4704_ = leanh::lean_ctor_get(v_p_4703_, 0);
                v_snd_4705_ = leanh::lean_ctor_get(v_p_4703_, 1);
                v_isSharedCheck_4712_ = (!leanh::lean_is_exclusive(v_p_4703_)) as u8;
                if v_isSharedCheck_4712_ == 0 {
                    v___x_4707_ = v_p_4703_;
                    v_isShared_4708_ = v_isSharedCheck_4712_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4705_);
                    leanh::lean_inc(v_fst_4704_);
                    leanh::lean_dec(v_p_4703_);
                    v___x_4707_ = leanh::lean_box(0);
                    v_isShared_4708_ = v_isSharedCheck_4712_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4708_ == 0 {
                    v___x_4710_ = v___x_4707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4711_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_fst_4704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4711_, 1, v_snd_4705_);
                    v___x_4710_ = v_reuseFailAlloc_4711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_forM___redArg___lam__0(
    mut v_f_4713_: *mut leanh::LeanObject,
    mut v_x_4714_: *mut leanh::LeanObject,
    mut v_k_4715_: *mut leanh::LeanObject,
    mut v_v_4716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4717_ = leanh::lean_apply_2(v_f_4713_, v_k_4715_, v_v_4716_);
    return v___x_4717_;
}
pub unsafe fn l_Std_ExtTreeMap_forM___redArg(
    mut v_inst_4718_: *mut leanh::LeanObject,
    mut v_f_4719_: *mut leanh::LeanObject,
    mut v_t_4720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4721_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4721_, 0, v_f_4719_);
    v___x_4722_ = leanh::lean_box(0);
    v___x_4723_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4718_,
        v___f_4721_,
        v___x_4722_,
        v_t_4720_,
    );
    return v___x_4723_;
}
pub unsafe fn l_Std_ExtTreeMap_forM(
    mut v_00_u03b1_4724_: *mut leanh::LeanObject,
    mut v_00_u03b2_4725_: *mut leanh::LeanObject,
    mut v_cmp_4726_: *mut leanh::LeanObject,
    mut v_m_4727_: *mut leanh::LeanObject,
    mut v_inst_4728_: *mut leanh::LeanObject,
    mut v_inst_4729_: *mut leanh::LeanObject,
    mut v_inst_4730_: *mut leanh::LeanObject,
    mut v_f_4731_: *mut leanh::LeanObject,
    mut v_t_4732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4733_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4733_, 0, v_f_4731_);
    v___x_4734_ = leanh::lean_box(0);
    v___x_4735_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4728_,
        v___f_4733_,
        v___x_4734_,
        v_t_4732_,
    );
    return v___x_4735_;
}
pub unsafe fn l_Std_ExtTreeMap_forM___boxed(
    mut v_00_u03b1_4736_: *mut leanh::LeanObject,
    mut v_00_u03b2_4737_: *mut leanh::LeanObject,
    mut v_cmp_4738_: *mut leanh::LeanObject,
    mut v_m_4739_: *mut leanh::LeanObject,
    mut v_inst_4740_: *mut leanh::LeanObject,
    mut v_inst_4741_: *mut leanh::LeanObject,
    mut v_inst_4742_: *mut leanh::LeanObject,
    mut v_f_4743_: *mut leanh::LeanObject,
    mut v_t_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4745_ = l_Std_ExtTreeMap_forM(
        v_00_u03b1_4736_,
        v_00_u03b2_4737_,
        v_cmp_4738_,
        v_m_4739_,
        v_inst_4740_,
        v_inst_4741_,
        v_inst_4742_,
        v_f_4743_,
        v_t_4744_,
    );
    leanh::lean_dec_ref(v_cmp_4738_);
    return v_res_4745_;
}
pub unsafe fn l_Std_ExtTreeMap_forIn___redArg___lam__0(
    mut v_f_4746_: *mut leanh::LeanObject,
    mut v_a_4747_: *mut leanh::LeanObject,
    mut v_b_4748_: *mut leanh::LeanObject,
    mut v_c_4749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4750_ = leanh::lean_apply_3(v_f_4746_, v_a_4747_, v_b_4748_, v_c_4749_);
    return v___x_4750_;
}
pub unsafe fn l_Std_ExtTreeMap_forIn___redArg___lam__1(
    mut v_toPure_4751_: *mut leanh::LeanObject,
    mut v_____do__lift_4752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_4753_ = leanh::lean_ctor_get(v_____do__lift_4752_, 0);
    leanh::lean_inc(v_a_4753_);
    leanh::lean_dec_ref(v_____do__lift_4752_);
    v___x_4754_ = leanh::lean_apply_2(v_toPure_4751_, leanh::lean_box(0), v_a_4753_);
    return v___x_4754_;
}
pub unsafe fn l_Std_ExtTreeMap_forIn___redArg(
    mut v_inst_4755_: *mut leanh::LeanObject,
    mut v_f_4756_: *mut leanh::LeanObject,
    mut v_init_4757_: *mut leanh::LeanObject,
    mut v_t_4758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4759_ = leanh::lean_ctor_get(v_inst_4755_, 0);
    v_toBind_4760_ = leanh::lean_ctor_get(v_inst_4755_, 1);
    leanh::lean_inc(v_toBind_4760_);
    v_toPure_4761_ = leanh::lean_ctor_get(v_toApplicative_4759_, 1);
    leanh::lean_inc(v_toPure_4761_);
    v___f_4762_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4762_, 0, v_f_4756_);
    v___x_4763_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4755_,
        v___f_4762_,
        v_init_4757_,
        v_t_4758_,
    );
    v___f_4764_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4764_, 0, v_toPure_4761_);
    v___x_4765_ = leanh::lean_apply_4(
        v_toBind_4760_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4763_,
        v___f_4764_,
    );
    return v___x_4765_;
}
pub unsafe fn l_Std_ExtTreeMap_forIn(
    mut v_00_u03b1_4766_: *mut leanh::LeanObject,
    mut v_00_u03b2_4767_: *mut leanh::LeanObject,
    mut v_cmp_4768_: *mut leanh::LeanObject,
    mut v_00_u03b4_4769_: *mut leanh::LeanObject,
    mut v_m_4770_: *mut leanh::LeanObject,
    mut v_inst_4771_: *mut leanh::LeanObject,
    mut v_inst_4772_: *mut leanh::LeanObject,
    mut v_inst_4773_: *mut leanh::LeanObject,
    mut v_f_4774_: *mut leanh::LeanObject,
    mut v_init_4775_: *mut leanh::LeanObject,
    mut v_t_4776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4777_ = leanh::lean_ctor_get(v_inst_4771_, 0);
    v_toBind_4778_ = leanh::lean_ctor_get(v_inst_4771_, 1);
    leanh::lean_inc(v_toBind_4778_);
    v_toPure_4779_ = leanh::lean_ctor_get(v_toApplicative_4777_, 1);
    leanh::lean_inc(v_toPure_4779_);
    v___f_4780_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4780_, 0, v_f_4774_);
    v___x_4781_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4771_,
        v___f_4780_,
        v_init_4775_,
        v_t_4776_,
    );
    v___f_4782_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4782_, 0, v_toPure_4779_);
    v___x_4783_ = leanh::lean_apply_4(
        v_toBind_4778_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4781_,
        v___f_4782_,
    );
    return v___x_4783_;
}
pub unsafe fn l_Std_ExtTreeMap_forIn___boxed(
    mut v_00_u03b1_4784_: *mut leanh::LeanObject,
    mut v_00_u03b2_4785_: *mut leanh::LeanObject,
    mut v_cmp_4786_: *mut leanh::LeanObject,
    mut v_00_u03b4_4787_: *mut leanh::LeanObject,
    mut v_m_4788_: *mut leanh::LeanObject,
    mut v_inst_4789_: *mut leanh::LeanObject,
    mut v_inst_4790_: *mut leanh::LeanObject,
    mut v_inst_4791_: *mut leanh::LeanObject,
    mut v_f_4792_: *mut leanh::LeanObject,
    mut v_init_4793_: *mut leanh::LeanObject,
    mut v_t_4794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4795_ = l_Std_ExtTreeMap_forIn(
        v_00_u03b1_4784_,
        v_00_u03b2_4785_,
        v_cmp_4786_,
        v_00_u03b4_4787_,
        v_m_4788_,
        v_inst_4789_,
        v_inst_4790_,
        v_inst_4791_,
        v_f_4792_,
        v_init_4793_,
        v_t_4794_,
    );
    leanh::lean_dec_ref(v_cmp_4786_);
    return v_res_4795_;
}
pub unsafe fn l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0(
    mut v_f_4796_: *mut leanh::LeanObject,
    mut v_x_4797_: *mut leanh::LeanObject,
    mut v_k_4798_: *mut leanh::LeanObject,
    mut v_v_4799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4800_, 0, v_k_4798_);
    leanh::lean_ctor_set(v___x_4800_, 1, v_v_4799_);
    v___x_4801_ = leanh::lean_apply_1(v_f_4796_, v___x_4800_);
    return v___x_4801_;
}
pub unsafe fn l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1(
    mut v_inst_4802_: *mut leanh::LeanObject,
    mut v_t_4803_: *mut leanh::LeanObject,
    mut v_f_4804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4805_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4805_, 0, v_f_4804_);
    v___x_4806_ = leanh::lean_box(0);
    v___x_4807_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4802_,
        v___f_4805_,
        v___x_4806_,
        v_t_4803_,
    );
    return v___x_4807_;
}
pub unsafe fn l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_4808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4809_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4809_, 0, v_inst_4808_);
    return v___f_4809_;
}
pub unsafe fn l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_4810_: *mut leanh::LeanObject,
    mut v_00_u03b2_4811_: *mut leanh::LeanObject,
    mut v_cmp_4812_: *mut leanh::LeanObject,
    mut v_m_4813_: *mut leanh::LeanObject,
    mut v_inst_4814_: *mut leanh::LeanObject,
    mut v_inst_4815_: *mut leanh::LeanObject,
    mut v_inst_4816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4817_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4817_, 0, v_inst_4815_);
    return v___f_4817_;
}
pub unsafe fn l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_4818_: *mut leanh::LeanObject,
    mut v_00_u03b2_4819_: *mut leanh::LeanObject,
    mut v_cmp_4820_: *mut leanh::LeanObject,
    mut v_m_4821_: *mut leanh::LeanObject,
    mut v_inst_4822_: *mut leanh::LeanObject,
    mut v_inst_4823_: *mut leanh::LeanObject,
    mut v_inst_4824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4825_ = l_Std_ExtTreeMap_instForMProdOfTransCmpOfLawfulMonad(
        v_00_u03b1_4818_,
        v_00_u03b2_4819_,
        v_cmp_4820_,
        v_m_4821_,
        v_inst_4822_,
        v_inst_4823_,
        v_inst_4824_,
    );
    leanh::lean_dec_ref(v_cmp_4820_);
    return v_res_4825_;
}
pub unsafe fn l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0(
    mut v_f_4826_: *mut leanh::LeanObject,
    mut v_a_4827_: *mut leanh::LeanObject,
    mut v_b_4828_: *mut leanh::LeanObject,
    mut v_c_4829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4830_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4830_, 0, v_a_4827_);
    leanh::lean_ctor_set(v___x_4830_, 1, v_b_4828_);
    v___x_4831_ = leanh::lean_apply_2(v_f_4826_, v___x_4830_, v_c_4829_);
    return v___x_4831_;
}
pub unsafe fn l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2(
    mut v_inst_4832_: *mut leanh::LeanObject,
    mut v_00_u03b2_4833_: *mut leanh::LeanObject,
    mut v_m_4834_: *mut leanh::LeanObject,
    mut v_init_4835_: *mut leanh::LeanObject,
    mut v_f_4836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4837_ = leanh::lean_ctor_get(v_inst_4832_, 0);
    v_toBind_4838_ = leanh::lean_ctor_get(v_inst_4832_, 1);
    leanh::lean_inc(v_toBind_4838_);
    v_toPure_4839_ = leanh::lean_ctor_get(v_toApplicative_4837_, 1);
    leanh::lean_inc(v_toPure_4839_);
    v___f_4840_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4840_, 0, v_f_4836_);
    v___x_4841_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4832_,
        v___f_4840_,
        v_init_4835_,
        v_m_4834_,
    );
    v___f_4842_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4842_, 0, v_toPure_4839_);
    v___x_4843_ = leanh::lean_apply_4(
        v_toBind_4838_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4841_,
        v___f_4842_,
    );
    return v___x_4843_;
}
pub unsafe fn l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_4844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4845_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_4845_, 0, v_inst_4844_);
    return v___f_4845_;
}
pub unsafe fn l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_4846_: *mut leanh::LeanObject,
    mut v_00_u03b2_4847_: *mut leanh::LeanObject,
    mut v_cmp_4848_: *mut leanh::LeanObject,
    mut v_m_4849_: *mut leanh::LeanObject,
    mut v_inst_4850_: *mut leanh::LeanObject,
    mut v_inst_4851_: *mut leanh::LeanObject,
    mut v_inst_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4853_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_4853_, 0, v_inst_4851_);
    return v___f_4853_;
}
pub unsafe fn l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_4854_: *mut leanh::LeanObject,
    mut v_00_u03b2_4855_: *mut leanh::LeanObject,
    mut v_cmp_4856_: *mut leanh::LeanObject,
    mut v_m_4857_: *mut leanh::LeanObject,
    mut v_inst_4858_: *mut leanh::LeanObject,
    mut v_inst_4859_: *mut leanh::LeanObject,
    mut v_inst_4860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4861_ = l_Std_ExtTreeMap_instForInProdOfTransCmpOfLawfulMonad(
        v_00_u03b1_4854_,
        v_00_u03b2_4855_,
        v_cmp_4856_,
        v_m_4857_,
        v_inst_4858_,
        v_inst_4859_,
        v_inst_4860_,
    );
    leanh::lean_dec_ref(v_cmp_4856_);
    return v_res_4861_;
}
pub unsafe fn l_Std_ExtTreeMap_any___redArg___lam__0(
    mut v_p_4862_: *mut leanh::LeanObject,
    mut v___x_4863_: *mut leanh::LeanObject,
    mut v___x_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_b_4866_: *mut leanh::LeanObject,
    mut v_acc_4867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: u8 = 0;
    v___x_4868_ = leanh::lean_apply_2(v_p_4862_, v_a_4865_, v_b_4866_);
    v___x_4869_ = (leanh::lean_unbox(v___x_4868_) as u8);
    if v___x_4869_ == 0 {
        let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4870_, 0, v___x_4863_);
        return v___x_4870_;
    } else {
        let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4863_);
        v___x_4871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4871_, 0, v___x_4868_);
        v___x_4872_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4872_, 0, v___x_4871_);
        leanh::lean_ctor_set(v___x_4872_, 1, v___x_4864_);
        v___x_4873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4873_, 0, v___x_4872_);
        return v___x_4873_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_any___redArg___lam__0___boxed(
    mut v_p_4874_: *mut leanh::LeanObject,
    mut v___x_4875_: *mut leanh::LeanObject,
    mut v___x_4876_: *mut leanh::LeanObject,
    mut v_a_4877_: *mut leanh::LeanObject,
    mut v_b_4878_: *mut leanh::LeanObject,
    mut v_acc_4879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4880_ = l_Std_ExtTreeMap_any___redArg___lam__0(
        v_p_4874_,
        v___x_4875_,
        v___x_4876_,
        v_a_4877_,
        v_b_4878_,
        v_acc_4879_,
    );
    leanh::lean_dec_ref(v_acc_4879_);
    return v_res_4880_;
}
pub unsafe fn l_Std_ExtTreeMap_any___redArg(
    mut v_t_4884_: *mut leanh::LeanObject,
    mut v_p_4885_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: u8 = 0;
    let mut v_val_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4892_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
                v___x_4893_ = leanh::lean_box(0);
                v___x_4894_ = l_Std_ExtTreeMap_any___redArg___closed__0;
                v___f_4895_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_4895_, 0, v_p_4885_);
                leanh::lean_closure_set(v___f_4895_, 1, v___x_4894_);
                leanh::lean_closure_set(v___f_4895_, 2, v___x_4893_);
                v___x_4896_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4892_,
                    v___f_4895_,
                    v___x_4894_,
                    v_t_4884_,
                );
                v_a_4897_ = leanh::lean_ctor_get(v___x_4896_, 0);
                leanh::lean_inc(v_a_4897_);
                leanh::lean_dec(v___x_4896_);
                v___y_4887_ = v_a_4897_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4888_ = leanh::lean_ctor_get(v___y_4887_, 0);
                leanh::lean_inc(v_fst_4888_);
                leanh::lean_dec_ref(v___y_4887_);
                if leanh::lean_obj_tag(v_fst_4888_) == 0 {
                    v___x_4889_ = 0;
                    return v___x_4889_;
                } else {
                    v_val_4890_ = leanh::lean_ctor_get(v_fst_4888_, 0);
                    leanh::lean_inc(v_val_4890_);
                    leanh::lean_dec_ref_known(v_fst_4888_, 1);
                    v___x_4891_ = (leanh::lean_unbox(v_val_4890_) as u8);
                    leanh::lean_dec(v_val_4890_);
                    return v___x_4891_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_any___redArg___boxed(
    mut v_t_4898_: *mut leanh::LeanObject,
    mut v_p_4899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4900_: u8 = 0;
    let mut v_r_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4900_ = l_Std_ExtTreeMap_any___redArg(v_t_4898_, v_p_4899_);
    v_r_4901_ = leanh::lean_box((v_res_4900_) as usize);
    return v_r_4901_;
}
pub unsafe fn l_Std_ExtTreeMap_any(
    mut v_00_u03b1_4902_: *mut leanh::LeanObject,
    mut v_00_u03b2_4903_: *mut leanh::LeanObject,
    mut v_cmp_4904_: *mut leanh::LeanObject,
    mut v_inst_4905_: *mut leanh::LeanObject,
    mut v_t_4906_: *mut leanh::LeanObject,
    mut v_p_4907_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: u8 = 0;
    let mut v_val_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: u8 = 0;
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4914_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
                v___x_4915_ = leanh::lean_box(0);
                v___x_4916_ = l_Std_ExtTreeMap_any___redArg___closed__0;
                v___f_4917_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_4917_, 0, v_p_4907_);
                leanh::lean_closure_set(v___f_4917_, 1, v___x_4916_);
                leanh::lean_closure_set(v___f_4917_, 2, v___x_4915_);
                v___x_4918_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4914_,
                    v___f_4917_,
                    v___x_4916_,
                    v_t_4906_,
                );
                v_a_4919_ = leanh::lean_ctor_get(v___x_4918_, 0);
                leanh::lean_inc(v_a_4919_);
                leanh::lean_dec(v___x_4918_);
                v___y_4909_ = v_a_4919_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4910_ = leanh::lean_ctor_get(v___y_4909_, 0);
                leanh::lean_inc(v_fst_4910_);
                leanh::lean_dec_ref(v___y_4909_);
                if leanh::lean_obj_tag(v_fst_4910_) == 0 {
                    v___x_4911_ = 0;
                    return v___x_4911_;
                } else {
                    v_val_4912_ = leanh::lean_ctor_get(v_fst_4910_, 0);
                    leanh::lean_inc(v_val_4912_);
                    leanh::lean_dec_ref_known(v_fst_4910_, 1);
                    v___x_4913_ = (leanh::lean_unbox(v_val_4912_) as u8);
                    leanh::lean_dec(v_val_4912_);
                    return v___x_4913_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_any___boxed(
    mut v_00_u03b1_4920_: *mut leanh::LeanObject,
    mut v_00_u03b2_4921_: *mut leanh::LeanObject,
    mut v_cmp_4922_: *mut leanh::LeanObject,
    mut v_inst_4923_: *mut leanh::LeanObject,
    mut v_t_4924_: *mut leanh::LeanObject,
    mut v_p_4925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4926_: u8 = 0;
    let mut v_r_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4926_ = l_Std_ExtTreeMap_any(
        v_00_u03b1_4920_,
        v_00_u03b2_4921_,
        v_cmp_4922_,
        v_inst_4923_,
        v_t_4924_,
        v_p_4925_,
    );
    leanh::lean_dec_ref(v_cmp_4922_);
    v_r_4927_ = leanh::lean_box((v_res_4926_) as usize);
    return v_r_4927_;
}
pub unsafe fn l_Std_ExtTreeMap_all___redArg___lam__0(
    mut v_p_4928_: *mut leanh::LeanObject,
    mut v___x_4929_: *mut leanh::LeanObject,
    mut v___x_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_b_4932_: *mut leanh::LeanObject,
    mut v_acc_4933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: u8 = 0;
    v___x_4934_ = leanh::lean_apply_2(v_p_4928_, v_a_4931_, v_b_4932_);
    v___x_4935_ = (leanh::lean_unbox(v___x_4934_) as u8);
    if v___x_4935_ == 0 {
        let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4930_);
        v___x_4936_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4936_, 0, v___x_4934_);
        v___x_4937_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4937_, 0, v___x_4936_);
        leanh::lean_ctor_set(v___x_4937_, 1, v___x_4929_);
        v___x_4938_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4938_, 0, v___x_4937_);
        return v___x_4938_;
    } else {
        let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4939_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4939_, 0, v___x_4930_);
        return v___x_4939_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_all___redArg___lam__0___boxed(
    mut v_p_4940_: *mut leanh::LeanObject,
    mut v___x_4941_: *mut leanh::LeanObject,
    mut v___x_4942_: *mut leanh::LeanObject,
    mut v_a_4943_: *mut leanh::LeanObject,
    mut v_b_4944_: *mut leanh::LeanObject,
    mut v_acc_4945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4946_ = l_Std_ExtTreeMap_all___redArg___lam__0(
        v_p_4940_,
        v___x_4941_,
        v___x_4942_,
        v_a_4943_,
        v_b_4944_,
        v_acc_4945_,
    );
    leanh::lean_dec_ref(v_acc_4945_);
    return v_res_4946_;
}
pub unsafe fn l_Std_ExtTreeMap_all___redArg(
    mut v_t_4947_: *mut leanh::LeanObject,
    mut v_p_4948_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: u8 = 0;
    let mut v_val_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: u8 = 0;
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4955_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
                v___x_4956_ = leanh::lean_box(0);
                v___x_4957_ = l_Std_ExtTreeMap_any___redArg___closed__0;
                v___f_4958_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_4958_, 0, v_p_4948_);
                leanh::lean_closure_set(v___f_4958_, 1, v___x_4956_);
                leanh::lean_closure_set(v___f_4958_, 2, v___x_4957_);
                v___x_4959_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4955_,
                    v___f_4958_,
                    v___x_4957_,
                    v_t_4947_,
                );
                v_a_4960_ = leanh::lean_ctor_get(v___x_4959_, 0);
                leanh::lean_inc(v_a_4960_);
                leanh::lean_dec(v___x_4959_);
                v___y_4950_ = v_a_4960_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4951_ = leanh::lean_ctor_get(v___y_4950_, 0);
                leanh::lean_inc(v_fst_4951_);
                leanh::lean_dec_ref(v___y_4950_);
                if leanh::lean_obj_tag(v_fst_4951_) == 0 {
                    v___x_4952_ = 1;
                    return v___x_4952_;
                } else {
                    v_val_4953_ = leanh::lean_ctor_get(v_fst_4951_, 0);
                    leanh::lean_inc(v_val_4953_);
                    leanh::lean_dec_ref_known(v_fst_4951_, 1);
                    v___x_4954_ = (leanh::lean_unbox(v_val_4953_) as u8);
                    leanh::lean_dec(v_val_4953_);
                    return v___x_4954_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_all___redArg___boxed(
    mut v_t_4961_: *mut leanh::LeanObject,
    mut v_p_4962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4963_: u8 = 0;
    let mut v_r_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4963_ = l_Std_ExtTreeMap_all___redArg(v_t_4961_, v_p_4962_);
    v_r_4964_ = leanh::lean_box((v_res_4963_) as usize);
    return v_r_4964_;
}
pub unsafe fn l_Std_ExtTreeMap_all(
    mut v_00_u03b1_4965_: *mut leanh::LeanObject,
    mut v_00_u03b2_4966_: *mut leanh::LeanObject,
    mut v_cmp_4967_: *mut leanh::LeanObject,
    mut v_inst_4968_: *mut leanh::LeanObject,
    mut v_t_4969_: *mut leanh::LeanObject,
    mut v_p_4970_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: u8 = 0;
    let mut v_val_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: u8 = 0;
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4977_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
                v___x_4978_ = leanh::lean_box(0);
                v___x_4979_ = l_Std_ExtTreeMap_any___redArg___closed__0;
                v___f_4980_ = leanh::lean_alloc_closure(
                    l_Std_ExtTreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_4980_, 0, v_p_4970_);
                leanh::lean_closure_set(v___f_4980_, 1, v___x_4978_);
                leanh::lean_closure_set(v___f_4980_, 2, v___x_4979_);
                v___x_4981_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4977_,
                    v___f_4980_,
                    v___x_4979_,
                    v_t_4969_,
                );
                v_a_4982_ = leanh::lean_ctor_get(v___x_4981_, 0);
                leanh::lean_inc(v_a_4982_);
                leanh::lean_dec(v___x_4981_);
                v___y_4972_ = v_a_4982_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4973_ = leanh::lean_ctor_get(v___y_4972_, 0);
                leanh::lean_inc(v_fst_4973_);
                leanh::lean_dec_ref(v___y_4972_);
                if leanh::lean_obj_tag(v_fst_4973_) == 0 {
                    v___x_4974_ = 1;
                    return v___x_4974_;
                } else {
                    v_val_4975_ = leanh::lean_ctor_get(v_fst_4973_, 0);
                    leanh::lean_inc(v_val_4975_);
                    leanh::lean_dec_ref_known(v_fst_4973_, 1);
                    v___x_4976_ = (leanh::lean_unbox(v_val_4975_) as u8);
                    leanh::lean_dec(v_val_4975_);
                    return v___x_4976_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_all___boxed(
    mut v_00_u03b1_4983_: *mut leanh::LeanObject,
    mut v_00_u03b2_4984_: *mut leanh::LeanObject,
    mut v_cmp_4985_: *mut leanh::LeanObject,
    mut v_inst_4986_: *mut leanh::LeanObject,
    mut v_t_4987_: *mut leanh::LeanObject,
    mut v_p_4988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4989_: u8 = 0;
    let mut v_r_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4989_ = l_Std_ExtTreeMap_all(
        v_00_u03b1_4983_,
        v_00_u03b2_4984_,
        v_cmp_4985_,
        v_inst_4986_,
        v_t_4987_,
        v_p_4988_,
    );
    leanh::lean_dec_ref(v_cmp_4985_);
    v_r_4990_ = leanh::lean_box((v_res_4989_) as usize);
    return v_r_4990_;
}
pub unsafe fn l_Std_ExtTreeMap_keys___redArg___lam__0(
    mut v_x1_4991_: *mut leanh::LeanObject,
    mut v_x2_4992_: *mut leanh::LeanObject,
    mut v_x3_4993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4994_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4994_, 0, v_x1_4991_);
    leanh::lean_ctor_set(v___x_4994_, 1, v_x3_4993_);
    return v___x_4994_;
}
pub unsafe fn l_Std_ExtTreeMap_keys___redArg___lam__0___boxed(
    mut v_x1_4995_: *mut leanh::LeanObject,
    mut v_x2_4996_: *mut leanh::LeanObject,
    mut v_x3_4997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4998_ = l_Std_ExtTreeMap_keys___redArg___lam__0(v_x1_4995_, v_x2_4996_, v_x3_4997_);
    leanh::lean_dec(v_x2_4996_);
    return v_res_4998_;
}
pub unsafe fn l_Std_ExtTreeMap_keys___redArg(
    mut v_t_5000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5001_ = l_Std_ExtTreeMap_keys___redArg___closed__0;
    v___x_5002_ = leanh::lean_box(0);
    v___x_5003_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_5004_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5003_,
        v___f_5001_,
        v___x_5002_,
        v_t_5000_,
    );
    return v___x_5004_;
}
pub unsafe fn l_Std_ExtTreeMap_keys(
    mut v_00_u03b1_5005_: *mut leanh::LeanObject,
    mut v_00_u03b2_5006_: *mut leanh::LeanObject,
    mut v_cmp_5007_: *mut leanh::LeanObject,
    mut v_inst_5008_: *mut leanh::LeanObject,
    mut v_t_5009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5010_ = l_Std_ExtTreeMap_keys___redArg___closed__0;
    v___x_5011_ = leanh::lean_box(0);
    v___x_5012_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_5013_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5012_,
        v___f_5010_,
        v___x_5011_,
        v_t_5009_,
    );
    return v___x_5013_;
}
pub unsafe fn l_Std_ExtTreeMap_keys___boxed(
    mut v_00_u03b1_5014_: *mut leanh::LeanObject,
    mut v_00_u03b2_5015_: *mut leanh::LeanObject,
    mut v_cmp_5016_: *mut leanh::LeanObject,
    mut v_inst_5017_: *mut leanh::LeanObject,
    mut v_t_5018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5019_ = l_Std_ExtTreeMap_keys(
        v_00_u03b1_5014_,
        v_00_u03b2_5015_,
        v_cmp_5016_,
        v_inst_5017_,
        v_t_5018_,
    );
    leanh::lean_dec_ref(v_cmp_5016_);
    return v_res_5019_;
}
pub unsafe fn l_Std_ExtTreeMap_keysArray___redArg___lam__0(
    mut v_l_5020_: *mut leanh::LeanObject,
    mut v_k_5021_: *mut leanh::LeanObject,
    mut v_x_5022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5023_ = lean_array_push(v_l_5020_, v_k_5021_);
    return v___x_5023_;
}
pub unsafe fn l_Std_ExtTreeMap_keysArray___redArg___lam__0___boxed(
    mut v_l_5024_: *mut leanh::LeanObject,
    mut v_k_5025_: *mut leanh::LeanObject,
    mut v_x_5026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Std_ExtTreeMap_keysArray___redArg___lam__0(v_l_5024_, v_k_5025_, v_x_5026_);
    leanh::lean_dec(v_x_5026_);
    return v_res_5027_;
}
pub unsafe fn l_Std_ExtTreeMap_keysArray___redArg(
    mut v_t_5029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5030_ = l_Std_ExtTreeMap_keysArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_5029_) == 0 {
                    v_size_5035_ = leanh::lean_ctor_get(v_t_5029_, 0);
                    leanh::lean_inc(v_size_5035_);
                    v___y_5032_ = v_size_5035_;
                    state = 1;
                    continue;
                } else {
                    v___x_5036_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5032_ = v___x_5036_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5033_ = lean_mk_empty_array_with_capacity(v___y_5032_);
                leanh::lean_dec(v___y_5032_);
                v___x_5034_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5030_,
                    v___x_5033_,
                    v_t_5029_,
                );
                return v___x_5034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_keysArray(
    mut v_00_u03b1_5037_: *mut leanh::LeanObject,
    mut v_00_u03b2_5038_: *mut leanh::LeanObject,
    mut v_cmp_5039_: *mut leanh::LeanObject,
    mut v_inst_5040_: *mut leanh::LeanObject,
    mut v_t_5041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5042_ = l_Std_ExtTreeMap_keysArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_5041_) == 0 {
                    v_size_5047_ = leanh::lean_ctor_get(v_t_5041_, 0);
                    leanh::lean_inc(v_size_5047_);
                    v___y_5044_ = v_size_5047_;
                    state = 1;
                    continue;
                } else {
                    v___x_5048_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5044_ = v___x_5048_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5045_ = lean_mk_empty_array_with_capacity(v___y_5044_);
                leanh::lean_dec(v___y_5044_);
                v___x_5046_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5042_,
                    v___x_5045_,
                    v_t_5041_,
                );
                return v___x_5046_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_keysArray___boxed(
    mut v_00_u03b1_5049_: *mut leanh::LeanObject,
    mut v_00_u03b2_5050_: *mut leanh::LeanObject,
    mut v_cmp_5051_: *mut leanh::LeanObject,
    mut v_inst_5052_: *mut leanh::LeanObject,
    mut v_t_5053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5054_ = l_Std_ExtTreeMap_keysArray(
        v_00_u03b1_5049_,
        v_00_u03b2_5050_,
        v_cmp_5051_,
        v_inst_5052_,
        v_t_5053_,
    );
    leanh::lean_dec_ref(v_cmp_5051_);
    return v_res_5054_;
}
pub unsafe fn l_Std_ExtTreeMap_values___redArg___lam__0(
    mut v_x1_5055_: *mut leanh::LeanObject,
    mut v_x2_5056_: *mut leanh::LeanObject,
    mut v_x3_5057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5058_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5058_, 0, v_x2_5056_);
    leanh::lean_ctor_set(v___x_5058_, 1, v_x3_5057_);
    return v___x_5058_;
}
pub unsafe fn l_Std_ExtTreeMap_values___redArg___lam__0___boxed(
    mut v_x1_5059_: *mut leanh::LeanObject,
    mut v_x2_5060_: *mut leanh::LeanObject,
    mut v_x3_5061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5062_ = l_Std_ExtTreeMap_values___redArg___lam__0(v_x1_5059_, v_x2_5060_, v_x3_5061_);
    leanh::lean_dec(v_x1_5059_);
    return v_res_5062_;
}
pub unsafe fn l_Std_ExtTreeMap_values___redArg(
    mut v_t_5064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5065_ = l_Std_ExtTreeMap_values___redArg___closed__0;
    v___x_5066_ = leanh::lean_box(0);
    v___x_5067_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_5068_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5067_,
        v___f_5065_,
        v___x_5066_,
        v_t_5064_,
    );
    return v___x_5068_;
}
pub unsafe fn l_Std_ExtTreeMap_values(
    mut v_00_u03b1_5069_: *mut leanh::LeanObject,
    mut v_00_u03b2_5070_: *mut leanh::LeanObject,
    mut v_cmp_5071_: *mut leanh::LeanObject,
    mut v_inst_5072_: *mut leanh::LeanObject,
    mut v_t_5073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5074_ = l_Std_ExtTreeMap_values___redArg___closed__0;
    v___x_5075_ = leanh::lean_box(0);
    v___x_5076_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_5077_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5076_,
        v___f_5074_,
        v___x_5075_,
        v_t_5073_,
    );
    return v___x_5077_;
}
pub unsafe fn l_Std_ExtTreeMap_values___boxed(
    mut v_00_u03b1_5078_: *mut leanh::LeanObject,
    mut v_00_u03b2_5079_: *mut leanh::LeanObject,
    mut v_cmp_5080_: *mut leanh::LeanObject,
    mut v_inst_5081_: *mut leanh::LeanObject,
    mut v_t_5082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5083_ = l_Std_ExtTreeMap_values(
        v_00_u03b1_5078_,
        v_00_u03b2_5079_,
        v_cmp_5080_,
        v_inst_5081_,
        v_t_5082_,
    );
    leanh::lean_dec_ref(v_cmp_5080_);
    return v_res_5083_;
}
pub unsafe fn l_Std_ExtTreeMap_valuesArray___redArg___lam__0(
    mut v_l_5084_: *mut leanh::LeanObject,
    mut v_x_5085_: *mut leanh::LeanObject,
    mut v_v_5086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5087_ = lean_array_push(v_l_5084_, v_v_5086_);
    return v___x_5087_;
}
pub unsafe fn l_Std_ExtTreeMap_valuesArray___redArg___lam__0___boxed(
    mut v_l_5088_: *mut leanh::LeanObject,
    mut v_x_5089_: *mut leanh::LeanObject,
    mut v_v_5090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5091_ = l_Std_ExtTreeMap_valuesArray___redArg___lam__0(v_l_5088_, v_x_5089_, v_v_5090_);
    leanh::lean_dec(v_x_5089_);
    return v_res_5091_;
}
pub unsafe fn l_Std_ExtTreeMap_valuesArray___redArg(
    mut v_t_5093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5094_ = l_Std_ExtTreeMap_valuesArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_5093_) == 0 {
                    v_size_5099_ = leanh::lean_ctor_get(v_t_5093_, 0);
                    leanh::lean_inc(v_size_5099_);
                    v___y_5096_ = v_size_5099_;
                    state = 1;
                    continue;
                } else {
                    v___x_5100_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5096_ = v___x_5100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5097_ = lean_mk_empty_array_with_capacity(v___y_5096_);
                leanh::lean_dec(v___y_5096_);
                v___x_5098_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5094_,
                    v___x_5097_,
                    v_t_5093_,
                );
                return v___x_5098_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_valuesArray(
    mut v_00_u03b1_5101_: *mut leanh::LeanObject,
    mut v_00_u03b2_5102_: *mut leanh::LeanObject,
    mut v_cmp_5103_: *mut leanh::LeanObject,
    mut v_inst_5104_: *mut leanh::LeanObject,
    mut v_t_5105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5106_ = l_Std_ExtTreeMap_valuesArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_5105_) == 0 {
                    v_size_5111_ = leanh::lean_ctor_get(v_t_5105_, 0);
                    leanh::lean_inc(v_size_5111_);
                    v___y_5108_ = v_size_5111_;
                    state = 1;
                    continue;
                } else {
                    v___x_5112_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5108_ = v___x_5112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5109_ = lean_mk_empty_array_with_capacity(v___y_5108_);
                leanh::lean_dec(v___y_5108_);
                v___x_5110_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5106_,
                    v___x_5109_,
                    v_t_5105_,
                );
                return v___x_5110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_valuesArray___boxed(
    mut v_00_u03b1_5113_: *mut leanh::LeanObject,
    mut v_00_u03b2_5114_: *mut leanh::LeanObject,
    mut v_cmp_5115_: *mut leanh::LeanObject,
    mut v_inst_5116_: *mut leanh::LeanObject,
    mut v_t_5117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5118_ = l_Std_ExtTreeMap_valuesArray(
        v_00_u03b1_5113_,
        v_00_u03b2_5114_,
        v_cmp_5115_,
        v_inst_5116_,
        v_t_5117_,
    );
    leanh::lean_dec_ref(v_cmp_5115_);
    return v_res_5118_;
}
pub unsafe fn l_Std_ExtTreeMap_toList___redArg___lam__0(
    mut v_x1_5119_: *mut leanh::LeanObject,
    mut v_x2_5120_: *mut leanh::LeanObject,
    mut v_x3_5121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5122_, 0, v_x1_5119_);
    leanh::lean_ctor_set(v___x_5122_, 1, v_x2_5120_);
    v___x_5123_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5123_, 0, v___x_5122_);
    leanh::lean_ctor_set(v___x_5123_, 1, v_x3_5121_);
    return v___x_5123_;
}
pub unsafe fn l_Std_ExtTreeMap_toList___redArg(
    mut v_t_5125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5126_ = l_Std_ExtTreeMap_toList___redArg___closed__0;
    v___x_5127_ = leanh::lean_box(0);
    v___x_5128_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_5129_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5128_,
        v___f_5126_,
        v___x_5127_,
        v_t_5125_,
    );
    return v___x_5129_;
}
pub unsafe fn l_Std_ExtTreeMap_toList(
    mut v_00_u03b1_5130_: *mut leanh::LeanObject,
    mut v_00_u03b2_5131_: *mut leanh::LeanObject,
    mut v_cmp_5132_: *mut leanh::LeanObject,
    mut v_inst_5133_: *mut leanh::LeanObject,
    mut v_t_5134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5135_ = l_Std_ExtTreeMap_toList___redArg___closed__0;
    v___x_5136_ = leanh::lean_box(0);
    v___x_5137_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_5138_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5137_,
        v___f_5135_,
        v___x_5136_,
        v_t_5134_,
    );
    return v___x_5138_;
}
pub unsafe fn l_Std_ExtTreeMap_toList___boxed(
    mut v_00_u03b1_5139_: *mut leanh::LeanObject,
    mut v_00_u03b2_5140_: *mut leanh::LeanObject,
    mut v_cmp_5141_: *mut leanh::LeanObject,
    mut v_inst_5142_: *mut leanh::LeanObject,
    mut v_t_5143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5144_ = l_Std_ExtTreeMap_toList(
        v_00_u03b1_5139_,
        v_00_u03b2_5140_,
        v_cmp_5141_,
        v_inst_5142_,
        v_t_5143_,
    );
    leanh::lean_dec_ref(v_cmp_5141_);
    return v_res_5144_;
}
pub unsafe fn _init_l_Std_ExtTreeMap_ofList___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5145_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__26,
    );
    return v___x_5145_;
}
pub unsafe fn l_Std_ExtTreeMap_ofList___redArg___lam__0(
    mut v_cmp_5146_: *mut leanh::LeanObject,
    mut v_a_5147_: *mut leanh::LeanObject,
    mut v_x_5148_: *mut leanh::LeanObject,
    mut v___y_5149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5150_ = leanh::lean_ctor_get(v_a_5147_, 0);
    leanh::lean_inc(v_fst_5150_);
    v_snd_5151_ = leanh::lean_ctor_get(v_a_5147_, 1);
    leanh::lean_inc(v_snd_5151_);
    leanh::lean_dec_ref(v_a_5147_);
    v_r_5152_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_5146_,
        v_fst_5150_,
        v_snd_5151_,
        v___y_5149_,
    );
    v___x_5153_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5153_, 0, v_r_5152_);
    return v___x_5153_;
}
pub unsafe fn l_Std_ExtTreeMap_ofList___redArg(
    mut v_l_5154_: *mut leanh::LeanObject,
    mut v_cmp_5155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5156_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5156_, 0, v_cmp_5155_);
    v___x_5157_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5158_ = leanh::lean_box(1);
    v___x_5159_ = l_List_forIn_x27_loop___redArg(v___x_5157_, v___f_5156_, v_l_5154_, v_r_5158_);
    return v___x_5159_;
}
pub unsafe fn l_Std_ExtTreeMap_ofList___redArg___boxed(
    mut v_l_5160_: *mut leanh::LeanObject,
    mut v_cmp_5161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5162_ = l_Std_ExtTreeMap_ofList___redArg(v_l_5160_, v_cmp_5161_);
    leanh::lean_dec(v_l_5160_);
    return v_res_5162_;
}
pub unsafe fn l_Std_ExtTreeMap_ofList(
    mut v_00_u03b1_5163_: *mut leanh::LeanObject,
    mut v_00_u03b2_5164_: *mut leanh::LeanObject,
    mut v_l_5165_: *mut leanh::LeanObject,
    mut v_cmp_5166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5167_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5167_, 0, v_cmp_5166_);
    v___x_5168_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5169_ = leanh::lean_box(1);
    v___x_5170_ = l_List_forIn_x27_loop___redArg(v___x_5168_, v___f_5167_, v_l_5165_, v_r_5169_);
    return v___x_5170_;
}
pub unsafe fn l_Std_ExtTreeMap_ofList___boxed(
    mut v_00_u03b1_5171_: *mut leanh::LeanObject,
    mut v_00_u03b2_5172_: *mut leanh::LeanObject,
    mut v_l_5173_: *mut leanh::LeanObject,
    mut v_cmp_5174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5175_ =
        l_Std_ExtTreeMap_ofList(v_00_u03b1_5171_, v_00_u03b2_5172_, v_l_5173_, v_cmp_5174_);
    leanh::lean_dec(v_l_5173_);
    return v_res_5175_;
}
pub unsafe fn _init_l_Std_ExtTreeMap_unitOfList___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5176_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__26,
    );
    return v___x_5176_;
}
pub unsafe fn l_Std_ExtTreeMap_unitOfList___redArg___lam__0(
    mut v_cmp_5177_: *mut leanh::LeanObject,
    mut v_a_5178_: *mut leanh::LeanObject,
    mut v_x_5179_: *mut leanh::LeanObject,
    mut v___y_5180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5181_: u8 = 0;
    leanh::lean_inc(v___y_5180_);
    leanh::lean_inc(v_a_5178_);
    leanh::lean_inc_ref(v_cmp_5177_);
    v___x_5181_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5177_, v_a_5178_, v___y_5180_);
    if v___x_5181_ == 0 {
        let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5182_ = leanh::lean_box(0);
        v___x_5183_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_5177_,
            v_a_5178_,
            v___x_5182_,
            v___y_5180_,
        );
        v___x_5184_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5184_, 0, v___x_5183_);
        return v___x_5184_;
    } else {
        let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_5178_);
        leanh::lean_dec_ref(v_cmp_5177_);
        v___x_5185_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5185_, 0, v___y_5180_);
        return v___x_5185_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_unitOfList___redArg(
    mut v_l_5186_: *mut leanh::LeanObject,
    mut v_cmp_5187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5188_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5188_, 0, v_cmp_5187_);
    v___x_5189_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5190_ = leanh::lean_box(1);
    v___x_5191_ = l_List_forIn_x27_loop___redArg(v___x_5189_, v___f_5188_, v_l_5186_, v_r_5190_);
    return v___x_5191_;
}
pub unsafe fn l_Std_ExtTreeMap_unitOfList___redArg___boxed(
    mut v_l_5192_: *mut leanh::LeanObject,
    mut v_cmp_5193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5194_ = l_Std_ExtTreeMap_unitOfList___redArg(v_l_5192_, v_cmp_5193_);
    leanh::lean_dec(v_l_5192_);
    return v_res_5194_;
}
pub unsafe fn l_Std_ExtTreeMap_unitOfList(
    mut v_00_u03b1_5195_: *mut leanh::LeanObject,
    mut v_l_5196_: *mut leanh::LeanObject,
    mut v_cmp_5197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5198_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5198_, 0, v_cmp_5197_);
    v___x_5199_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5200_ = leanh::lean_box(1);
    v___x_5201_ = l_List_forIn_x27_loop___redArg(v___x_5199_, v___f_5198_, v_l_5196_, v_r_5200_);
    return v___x_5201_;
}
pub unsafe fn l_Std_ExtTreeMap_unitOfList___boxed(
    mut v_00_u03b1_5202_: *mut leanh::LeanObject,
    mut v_l_5203_: *mut leanh::LeanObject,
    mut v_cmp_5204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5205_ = l_Std_ExtTreeMap_unitOfList(v_00_u03b1_5202_, v_l_5203_, v_cmp_5204_);
    leanh::lean_dec(v_l_5203_);
    return v_res_5205_;
}
pub unsafe fn l_Std_ExtTreeMap_toArray___redArg___lam__0(
    mut v_acc_5206_: *mut leanh::LeanObject,
    mut v_k_5207_: *mut leanh::LeanObject,
    mut v_v_5208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5209_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5209_, 0, v_k_5207_);
    leanh::lean_ctor_set(v___x_5209_, 1, v_v_5208_);
    v___x_5210_ = lean_array_push(v_acc_5206_, v___x_5209_);
    return v___x_5210_;
}
pub unsafe fn l_Std_ExtTreeMap_toArray___redArg(
    mut v_t_5214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5215_ = l_Std_ExtTreeMap_toArray___redArg___closed__0;
    v___x_5216_ = l_Std_ExtTreeMap_toArray___redArg___closed__1;
    v___x_5217_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_5215_, v___x_5216_, v_t_5214_);
    return v___x_5217_;
}
pub unsafe fn l_Std_ExtTreeMap_toArray(
    mut v_00_u03b1_5218_: *mut leanh::LeanObject,
    mut v_00_u03b2_5219_: *mut leanh::LeanObject,
    mut v_cmp_5220_: *mut leanh::LeanObject,
    mut v_inst_5221_: *mut leanh::LeanObject,
    mut v_t_5222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5223_ = l_Std_ExtTreeMap_toArray___redArg___closed__0;
    v___x_5224_ = l_Std_ExtTreeMap_toArray___redArg___closed__1;
    v___x_5225_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_5223_, v___x_5224_, v_t_5222_);
    return v___x_5225_;
}
pub unsafe fn l_Std_ExtTreeMap_toArray___boxed(
    mut v_00_u03b1_5226_: *mut leanh::LeanObject,
    mut v_00_u03b2_5227_: *mut leanh::LeanObject,
    mut v_cmp_5228_: *mut leanh::LeanObject,
    mut v_inst_5229_: *mut leanh::LeanObject,
    mut v_t_5230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5231_ = l_Std_ExtTreeMap_toArray(
        v_00_u03b1_5226_,
        v_00_u03b2_5227_,
        v_cmp_5228_,
        v_inst_5229_,
        v_t_5230_,
    );
    leanh::lean_dec_ref(v_cmp_5228_);
    return v_res_5231_;
}
pub unsafe fn _init_l_Std_ExtTreeMap_ofArray___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5232_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__26,
    );
    return v___x_5232_;
}
pub unsafe fn l_Std_ExtTreeMap_ofArray___redArg(
    mut v_a_5233_: *mut leanh::LeanObject,
    mut v_cmp_5234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5238_: usize = 0;
    let mut v___x_5239_: usize = 0;
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5235_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5235_, 0, v_cmp_5234_);
    v___x_5236_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5237_ = leanh::lean_box(1);
    v_sz_5238_ = lean_array_size(v_a_5233_);
    v___x_5239_ = 0usize;
    v___x_5240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5236_,
        v_a_5233_,
        v___f_5235_,
        v_sz_5238_,
        v___x_5239_,
        v_r_5237_,
    );
    return v___x_5240_;
}
pub unsafe fn l_Std_ExtTreeMap_ofArray(
    mut v_00_u03b1_5241_: *mut leanh::LeanObject,
    mut v_00_u03b2_5242_: *mut leanh::LeanObject,
    mut v_a_5243_: *mut leanh::LeanObject,
    mut v_cmp_5244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5248_: usize = 0;
    let mut v___x_5249_: usize = 0;
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5245_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5245_, 0, v_cmp_5244_);
    v___x_5246_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5247_ = leanh::lean_box(1);
    v_sz_5248_ = lean_array_size(v_a_5243_);
    v___x_5249_ = 0usize;
    v___x_5250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5246_,
        v_a_5243_,
        v___f_5245_,
        v_sz_5248_,
        v___x_5249_,
        v_r_5247_,
    );
    return v___x_5250_;
}
pub unsafe fn _init_l_Std_ExtTreeMap_unitOfArray___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5251_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtTreeMap___auto__1___closed__26,
    );
    return v___x_5251_;
}
pub unsafe fn l_Std_ExtTreeMap_unitOfArray___redArg(
    mut v_a_5252_: *mut leanh::LeanObject,
    mut v_cmp_5253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5257_: usize = 0;
    let mut v___x_5258_: usize = 0;
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5254_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5254_, 0, v_cmp_5253_);
    v___x_5255_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5256_ = leanh::lean_box(1);
    v_sz_5257_ = lean_array_size(v_a_5252_);
    v___x_5258_ = 0usize;
    v___x_5259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5255_,
        v_a_5252_,
        v___f_5254_,
        v_sz_5257_,
        v___x_5258_,
        v_r_5256_,
    );
    return v___x_5259_;
}
pub unsafe fn l_Std_ExtTreeMap_unitOfArray(
    mut v_00_u03b1_5260_: *mut leanh::LeanObject,
    mut v_a_5261_: *mut leanh::LeanObject,
    mut v_cmp_5262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5266_: usize = 0;
    let mut v___x_5267_: usize = 0;
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5263_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_5263_, 0, v_cmp_5262_);
    v___x_5264_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v_r_5265_ = leanh::lean_box(1);
    v_sz_5266_ = lean_array_size(v_a_5261_);
    v___x_5267_ = 0usize;
    v___x_5268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5264_,
        v_a_5261_,
        v___f_5263_,
        v_sz_5266_,
        v___x_5267_,
        v_r_5265_,
    );
    return v___x_5268_;
}
pub unsafe fn l_Std_ExtTreeMap_modify___redArg(
    mut v_cmp_5269_: *mut leanh::LeanObject,
    mut v_t_5270_: *mut leanh::LeanObject,
    mut v_a_5271_: *mut leanh::LeanObject,
    mut v_f_5272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5273_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_5269_,
        v_a_5271_,
        v_f_5272_,
        v_t_5270_,
    );
    return v___x_5273_;
}
pub unsafe fn l_Std_ExtTreeMap_modify(
    mut v_00_u03b1_5274_: *mut leanh::LeanObject,
    mut v_00_u03b2_5275_: *mut leanh::LeanObject,
    mut v_cmp_5276_: *mut leanh::LeanObject,
    mut v_inst_5277_: *mut leanh::LeanObject,
    mut v_t_5278_: *mut leanh::LeanObject,
    mut v_a_5279_: *mut leanh::LeanObject,
    mut v_f_5280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5281_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_5276_,
        v_a_5279_,
        v_f_5280_,
        v_t_5278_,
    );
    return v___x_5281_;
}
pub unsafe fn l_Std_ExtTreeMap_alter___redArg(
    mut v_cmp_5282_: *mut leanh::LeanObject,
    mut v_t_5283_: *mut leanh::LeanObject,
    mut v_a_5284_: *mut leanh::LeanObject,
    mut v_f_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5286_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_5282_,
        v_a_5284_,
        v_f_5285_,
        v_t_5283_,
    );
    return v___x_5286_;
}
pub unsafe fn l_Std_ExtTreeMap_alter(
    mut v_00_u03b1_5287_: *mut leanh::LeanObject,
    mut v_00_u03b2_5288_: *mut leanh::LeanObject,
    mut v_cmp_5289_: *mut leanh::LeanObject,
    mut v_inst_5290_: *mut leanh::LeanObject,
    mut v_t_5291_: *mut leanh::LeanObject,
    mut v_a_5292_: *mut leanh::LeanObject,
    mut v_f_5293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5294_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_5289_,
        v_a_5292_,
        v_f_5293_,
        v_t_5291_,
    );
    return v___x_5294_;
}
pub unsafe fn l_Std_ExtTreeMap_mergeWith___redArg___lam__0(
    mut v_b_u2082_5295_: *mut leanh::LeanObject,
    mut v_mergeFn_5296_: *mut leanh::LeanObject,
    mut v_a_5297_: *mut leanh::LeanObject,
    mut v_x_5298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5303_: u8 = 0;
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5298_) == 0 {
                    leanh::lean_dec(v_a_5297_);
                    leanh::lean_dec(v_mergeFn_5296_);
                    v___x_5299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5299_, 0, v_b_u2082_5295_);
                    return v___x_5299_;
                } else {
                    v_val_5300_ = leanh::lean_ctor_get(v_x_5298_, 0);
                    v_isSharedCheck_5308_ = (!leanh::lean_is_exclusive(v_x_5298_)) as u8;
                    if v_isSharedCheck_5308_ == 0 {
                        v___x_5302_ = v_x_5298_;
                        v_isShared_5303_ = v_isSharedCheck_5308_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5300_);
                        leanh::lean_dec(v_x_5298_);
                        v___x_5302_ = leanh::lean_box(0);
                        v_isShared_5303_ = v_isSharedCheck_5308_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5304_ = leanh::lean_apply_3(
                    v_mergeFn_5296_,
                    v_a_5297_,
                    v_val_5300_,
                    v_b_u2082_5295_,
                );
                if v_isShared_5303_ == 0 {
                    leanh::lean_ctor_set(v___x_5302_, 0, v___x_5304_);
                    v___x_5306_ = v___x_5302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5307_, 0, v___x_5304_);
                    v___x_5306_ = v_reuseFailAlloc_5307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtTreeMap_mergeWith___redArg___lam__1(
    mut v_mergeFn_5309_: *mut leanh::LeanObject,
    mut v_cmp_5310_: *mut leanh::LeanObject,
    mut v_t_5311_: *mut leanh::LeanObject,
    mut v_a_5312_: *mut leanh::LeanObject,
    mut v_b_u2082_5313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_5312_);
    v___f_5314_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_mergeWith___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_5314_, 0, v_b_u2082_5313_);
    leanh::lean_closure_set(v___f_5314_, 1, v_mergeFn_5309_);
    leanh::lean_closure_set(v___f_5314_, 2, v_a_5312_);
    v___x_5315_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_5310_,
        v_a_5312_,
        v___f_5314_,
        v_t_5311_,
    );
    return v___x_5315_;
}
pub unsafe fn l_Std_ExtTreeMap_mergeWith___redArg(
    mut v_cmp_5316_: *mut leanh::LeanObject,
    mut v_mergeFn_5317_: *mut leanh::LeanObject,
    mut v_t_u2081_5318_: *mut leanh::LeanObject,
    mut v_t_u2082_5319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5320_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_5320_, 0, v_mergeFn_5317_);
    leanh::lean_closure_set(v___f_5320_, 1, v_cmp_5316_);
    v___x_5321_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_5320_, v_t_u2081_5318_, v_t_u2082_5319_);
    return v___x_5321_;
}
pub unsafe fn l_Std_ExtTreeMap_mergeWith(
    mut v_00_u03b1_5322_: *mut leanh::LeanObject,
    mut v_00_u03b2_5323_: *mut leanh::LeanObject,
    mut v_cmp_5324_: *mut leanh::LeanObject,
    mut v_inst_5325_: *mut leanh::LeanObject,
    mut v_mergeFn_5326_: *mut leanh::LeanObject,
    mut v_t_u2081_5327_: *mut leanh::LeanObject,
    mut v_t_u2082_5328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5329_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_5329_, 0, v_mergeFn_5326_);
    leanh::lean_closure_set(v___f_5329_, 1, v_cmp_5324_);
    v___x_5330_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_5329_, v_t_u2081_5327_, v_t_u2082_5328_);
    return v___x_5330_;
}
pub unsafe fn l_Std_ExtTreeMap_insertMany___redArg___lam__0(
    mut v_cmp_5331_: *mut leanh::LeanObject,
    mut v_x_5332_: *mut leanh::LeanObject,
    mut v_____s_5333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5334_ = leanh::lean_ctor_get(v_x_5332_, 0);
    leanh::lean_inc(v_fst_5334_);
    v_snd_5335_ = leanh::lean_ctor_get(v_x_5332_, 1);
    leanh::lean_inc(v_snd_5335_);
    leanh::lean_dec_ref(v_x_5332_);
    v_acc_5336_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_5331_,
        v_fst_5334_,
        v_snd_5335_,
        v_____s_5333_,
    );
    v___x_5337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5337_, 0, v_acc_5336_);
    return v___x_5337_;
}
pub unsafe fn l_Std_ExtTreeMap_insertMany___redArg(
    mut v_cmp_5338_: *mut leanh::LeanObject,
    mut v_inst_5339_: *mut leanh::LeanObject,
    mut v_t_5340_: *mut leanh::LeanObject,
    mut v_l_5341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5342_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5342_, 0, v_cmp_5338_);
    v___x_5343_ = leanh::lean_apply_4(
        v_inst_5339_,
        leanh::lean_box(0),
        v_l_5341_,
        v_t_5340_,
        v___f_5342_,
    );
    return v___x_5343_;
}
pub unsafe fn l_Std_ExtTreeMap_insertMany(
    mut v_00_u03b1_5344_: *mut leanh::LeanObject,
    mut v_00_u03b2_5345_: *mut leanh::LeanObject,
    mut v_cmp_5346_: *mut leanh::LeanObject,
    mut v_inst_5347_: *mut leanh::LeanObject,
    mut v_00_u03c1_5348_: *mut leanh::LeanObject,
    mut v_inst_5349_: *mut leanh::LeanObject,
    mut v_t_5350_: *mut leanh::LeanObject,
    mut v_l_5351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5352_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5352_, 0, v_cmp_5346_);
    v___x_5353_ = leanh::lean_apply_4(
        v_inst_5349_,
        leanh::lean_box(0),
        v_l_5351_,
        v_t_5350_,
        v___f_5352_,
    );
    return v___x_5353_;
}
pub unsafe fn l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0(
    mut v_cmp_5354_: *mut leanh::LeanObject,
    mut v_a_5355_: *mut leanh::LeanObject,
    mut v_____s_5356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5357_: u8 = 0;
    leanh::lean_inc(v_____s_5356_);
    leanh::lean_inc(v_a_5355_);
    leanh::lean_inc_ref(v_cmp_5354_);
    v___x_5357_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5354_, v_a_5355_, v_____s_5356_);
    if v___x_5357_ == 0 {
        let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5358_ = leanh::lean_box(0);
        v___x_5359_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_5354_,
            v_a_5355_,
            v___x_5358_,
            v_____s_5356_,
        );
        v___x_5360_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5360_, 0, v___x_5359_);
        return v___x_5360_;
    } else {
        let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_5355_);
        leanh::lean_dec_ref(v_cmp_5354_);
        v___x_5361_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5361_, 0, v_____s_5356_);
        return v___x_5361_;
    }
}
pub unsafe fn l_Std_ExtTreeMap_insertManyIfNewUnit___redArg(
    mut v_cmp_5362_: *mut leanh::LeanObject,
    mut v_inst_5363_: *mut leanh::LeanObject,
    mut v_t_5364_: *mut leanh::LeanObject,
    mut v_l_5365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5366_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5366_, 0, v_cmp_5362_);
    v___x_5367_ = leanh::lean_apply_4(
        v_inst_5363_,
        leanh::lean_box(0),
        v_l_5365_,
        v_t_5364_,
        v___f_5366_,
    );
    return v___x_5367_;
}
pub unsafe fn l_Std_ExtTreeMap_insertManyIfNewUnit(
    mut v_00_u03b1_5368_: *mut leanh::LeanObject,
    mut v_cmp_5369_: *mut leanh::LeanObject,
    mut v_inst_5370_: *mut leanh::LeanObject,
    mut v_00_u03c1_5371_: *mut leanh::LeanObject,
    mut v_inst_5372_: *mut leanh::LeanObject,
    mut v_t_5373_: *mut leanh::LeanObject,
    mut v_l_5374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5375_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5375_, 0, v_cmp_5369_);
    v___x_5376_ = leanh::lean_apply_4(
        v_inst_5372_,
        leanh::lean_box(0),
        v_l_5374_,
        v_t_5373_,
        v___f_5375_,
    );
    return v___x_5376_;
}
pub unsafe fn l_Std_ExtTreeMap_union___redArg(
    mut v_cmp_5377_: *mut leanh::LeanObject,
    mut v_t_u2081_5378_: *mut leanh::LeanObject,
    mut v_t_u2082_5379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5380_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_5377_,
        v_t_u2081_5378_,
        v_t_u2082_5379_,
    );
    return v___x_5380_;
}
pub unsafe fn l_Std_ExtTreeMap_union(
    mut v_00_u03b1_5381_: *mut leanh::LeanObject,
    mut v_00_u03b2_5382_: *mut leanh::LeanObject,
    mut v_cmp_5383_: *mut leanh::LeanObject,
    mut v_inst_5384_: *mut leanh::LeanObject,
    mut v_t_u2081_5385_: *mut leanh::LeanObject,
    mut v_t_u2082_5386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5387_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_5383_,
        v_t_u2081_5385_,
        v_t_u2082_5386_,
    );
    return v___x_5387_;
}
pub unsafe fn l_Std_ExtTreeMap_instUnionOfTransCmp___redArg(
    mut v_cmp_5388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5389_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeMap_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5389_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5389_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5389_, 2, v_cmp_5388_);
    leanh::lean_closure_set(v___x_5389_, 3, leanh::lean_box(0));
    return v___x_5389_;
}
pub unsafe fn l_Std_ExtTreeMap_instUnionOfTransCmp(
    mut v_00_u03b1_5390_: *mut leanh::LeanObject,
    mut v_00_u03b2_5391_: *mut leanh::LeanObject,
    mut v_cmp_5392_: *mut leanh::LeanObject,
    mut v_inst_5393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeMap_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5394_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5394_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5394_, 2, v_cmp_5392_);
    leanh::lean_closure_set(v___x_5394_, 3, leanh::lean_box(0));
    return v___x_5394_;
}
pub unsafe fn l_Std_ExtTreeMap_inter___redArg(
    mut v_cmp_5395_: *mut leanh::LeanObject,
    mut v_t_u2081_5396_: *mut leanh::LeanObject,
    mut v_t_u2082_5397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5398_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_5395_,
        v_t_u2081_5396_,
        v_t_u2082_5397_,
    );
    return v___x_5398_;
}
pub unsafe fn l_Std_ExtTreeMap_inter(
    mut v_00_u03b1_5399_: *mut leanh::LeanObject,
    mut v_00_u03b2_5400_: *mut leanh::LeanObject,
    mut v_cmp_5401_: *mut leanh::LeanObject,
    mut v_inst_5402_: *mut leanh::LeanObject,
    mut v_t_u2081_5403_: *mut leanh::LeanObject,
    mut v_t_u2082_5404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5405_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_5401_,
        v_t_u2081_5403_,
        v_t_u2082_5404_,
    );
    return v___x_5405_;
}
pub unsafe fn l_Std_ExtTreeMap_instInterOfTransCmp___redArg(
    mut v_cmp_5406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5407_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeMap_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5407_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5407_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5407_, 2, v_cmp_5406_);
    leanh::lean_closure_set(v___x_5407_, 3, leanh::lean_box(0));
    return v___x_5407_;
}
pub unsafe fn l_Std_ExtTreeMap_instInterOfTransCmp(
    mut v_00_u03b1_5408_: *mut leanh::LeanObject,
    mut v_00_u03b2_5409_: *mut leanh::LeanObject,
    mut v_cmp_5410_: *mut leanh::LeanObject,
    mut v_inst_5411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5412_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeMap_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5412_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5412_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5412_, 2, v_cmp_5410_);
    leanh::lean_closure_set(v___x_5412_, 3, leanh::lean_box(0));
    return v___x_5412_;
}
pub unsafe fn l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(
    mut v_cmp_5413_: *mut leanh::LeanObject,
    mut v_inst_5414_: *mut leanh::LeanObject,
    mut v_m_u2081_5415_: *mut leanh::LeanObject,
    mut v_m_u2082_5416_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5417_: u8 = 0;
    v___x_5417_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_5413_,
        v_inst_5414_,
        v_m_u2081_5415_,
        v_m_u2082_5416_,
    );
    return v___x_5417_;
}
pub unsafe fn l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed(
    mut v_cmp_5418_: *mut leanh::LeanObject,
    mut v_inst_5419_: *mut leanh::LeanObject,
    mut v_m_u2081_5420_: *mut leanh::LeanObject,
    mut v_m_u2082_5421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5422_: u8 = 0;
    let mut v_r_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5422_ = l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0(
        v_cmp_5418_,
        v_inst_5419_,
        v_m_u2081_5420_,
        v_m_u2082_5421_,
    );
    v_r_5423_ = leanh::lean_box((v_res_5422_) as usize);
    return v_r_5423_;
}
pub unsafe fn l_Std_ExtTreeMap_instBEqOfTransCmp___redArg(
    mut v_cmp_5424_: *mut leanh::LeanObject,
    mut v_inst_5425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5426_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_5426_, 0, v_cmp_5424_);
    leanh::lean_closure_set(v___f_5426_, 1, v_inst_5425_);
    return v___f_5426_;
}
pub unsafe fn l_Std_ExtTreeMap_instBEqOfTransCmp(
    mut v_00_u03b1_5427_: *mut leanh::LeanObject,
    mut v_00_u03b2_5428_: *mut leanh::LeanObject,
    mut v_cmp_5429_: *mut leanh::LeanObject,
    mut v_inst_5430_: *mut leanh::LeanObject,
    mut v_inst_5431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5432_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instBEqOfTransCmp___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_5432_, 0, v_cmp_5429_);
    leanh::lean_closure_set(v___f_5432_, 1, v_inst_5431_);
    return v___f_5432_;
}
pub unsafe fn l_Std_ExtTreeMap_diff___redArg(
    mut v_cmp_5433_: *mut leanh::LeanObject,
    mut v_t_u2081_5434_: *mut leanh::LeanObject,
    mut v_t_u2082_5435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5436_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_5433_,
        v_t_u2081_5434_,
        v_t_u2082_5435_,
    );
    return v___x_5436_;
}
pub unsafe fn l_Std_ExtTreeMap_diff(
    mut v_00_u03b1_5437_: *mut leanh::LeanObject,
    mut v_00_u03b2_5438_: *mut leanh::LeanObject,
    mut v_cmp_5439_: *mut leanh::LeanObject,
    mut v_inst_5440_: *mut leanh::LeanObject,
    mut v_t_u2081_5441_: *mut leanh::LeanObject,
    mut v_t_u2082_5442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5443_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_5439_,
        v_t_u2081_5441_,
        v_t_u2082_5442_,
    );
    return v___x_5443_;
}
pub unsafe fn l_Std_ExtTreeMap_instSDiffOfTransCmp___redArg(
    mut v_cmp_5444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5445_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeMap_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5445_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5445_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5445_, 2, v_cmp_5444_);
    leanh::lean_closure_set(v___x_5445_, 3, leanh::lean_box(0));
    return v___x_5445_;
}
pub unsafe fn l_Std_ExtTreeMap_instSDiffOfTransCmp(
    mut v_00_u03b1_5446_: *mut leanh::LeanObject,
    mut v_00_u03b2_5447_: *mut leanh::LeanObject,
    mut v_cmp_5448_: *mut leanh::LeanObject,
    mut v_inst_5449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5450_ =
        leanh::lean_alloc_closure(l_Std_ExtTreeMap_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5450_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5450_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5450_, 2, v_cmp_5448_);
    leanh::lean_closure_set(v___x_5450_, 3, leanh::lean_box(0));
    return v___x_5450_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(
    mut v_cmp_5451_: *mut leanh::LeanObject,
    mut v_inst_5452_: *mut leanh::LeanObject,
    mut v_x_5453_: *mut leanh::LeanObject,
    mut v_x_5454_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5455_: u8 = 0;
    v___x_5455_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_5451_,
        v_inst_5452_,
        v_x_5453_,
        v_x_5454_,
    );
    return v___x_5455_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg___boxed(
    mut v_cmp_5456_: *mut leanh::LeanObject,
    mut v_inst_5457_: *mut leanh::LeanObject,
    mut v_x_5458_: *mut leanh::LeanObject,
    mut v_x_5459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5460_: u8 = 0;
    let mut v_r_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5460_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___redArg(
        v_cmp_5456_,
        v_inst_5457_,
        v_x_5458_,
        v_x_5459_,
    );
    v_r_5461_ = leanh::lean_box((v_res_5460_) as usize);
    return v_r_5461_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(
    mut v_00_u03b1_5462_: *mut leanh::LeanObject,
    mut v_00_u03b2_5463_: *mut leanh::LeanObject,
    mut v_cmp_5464_: *mut leanh::LeanObject,
    mut v_inst_5465_: *mut leanh::LeanObject,
    mut v_inst_5466_: *mut leanh::LeanObject,
    mut v_inst_5467_: *mut leanh::LeanObject,
    mut v_inst_5468_: *mut leanh::LeanObject,
    mut v_x_5469_: *mut leanh::LeanObject,
    mut v_x_5470_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5471_: u8 = 0;
    v___x_5471_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_5464_,
        v_inst_5467_,
        v_x_5469_,
        v_x_5470_,
    );
    return v___x_5471_;
}
pub unsafe fn l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq___boxed(
    mut v_00_u03b1_5472_: *mut leanh::LeanObject,
    mut v_00_u03b2_5473_: *mut leanh::LeanObject,
    mut v_cmp_5474_: *mut leanh::LeanObject,
    mut v_inst_5475_: *mut leanh::LeanObject,
    mut v_inst_5476_: *mut leanh::LeanObject,
    mut v_inst_5477_: *mut leanh::LeanObject,
    mut v_inst_5478_: *mut leanh::LeanObject,
    mut v_x_5479_: *mut leanh::LeanObject,
    mut v_x_5480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5481_: u8 = 0;
    let mut v_r_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5481_ = l_Std_ExtTreeMap_instDecidableEqOfLawfulEqCmpOfTransCmpOfLawfulBEq(
        v_00_u03b1_5472_,
        v_00_u03b2_5473_,
        v_cmp_5474_,
        v_inst_5475_,
        v_inst_5476_,
        v_inst_5477_,
        v_inst_5478_,
        v_x_5479_,
        v_x_5480_,
    );
    v_r_5482_ = leanh::lean_box((v_res_5481_) as usize);
    return v_r_5482_;
}
pub unsafe fn l_Std_ExtTreeMap_eraseMany___redArg___lam__0(
    mut v_cmp_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
    mut v_____s_5485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_acc_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_acc_5486_ =
        l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_5483_, v_a_5484_, v_____s_5485_);
    v___x_5487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5487_, 0, v_acc_5486_);
    return v___x_5487_;
}
pub unsafe fn l_Std_ExtTreeMap_eraseMany___redArg(
    mut v_cmp_5488_: *mut leanh::LeanObject,
    mut v_inst_5489_: *mut leanh::LeanObject,
    mut v_t_5490_: *mut leanh::LeanObject,
    mut v_l_5491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5492_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5492_, 0, v_cmp_5488_);
    v___x_5493_ = leanh::lean_apply_4(
        v_inst_5489_,
        leanh::lean_box(0),
        v_l_5491_,
        v_t_5490_,
        v___f_5492_,
    );
    return v___x_5493_;
}
pub unsafe fn l_Std_ExtTreeMap_eraseMany(
    mut v_00_u03b1_5494_: *mut leanh::LeanObject,
    mut v_00_u03b2_5495_: *mut leanh::LeanObject,
    mut v_cmp_5496_: *mut leanh::LeanObject,
    mut v_inst_5497_: *mut leanh::LeanObject,
    mut v_00_u03c1_5498_: *mut leanh::LeanObject,
    mut v_inst_5499_: *mut leanh::LeanObject,
    mut v_t_5500_: *mut leanh::LeanObject,
    mut v_l_5501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5502_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5502_, 0, v_cmp_5496_);
    v___x_5503_ = leanh::lean_apply_4(
        v_inst_5499_,
        leanh::lean_box(0),
        v_l_5501_,
        v_t_5500_,
        v___f_5502_,
    );
    return v___x_5503_;
}
pub unsafe fn l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(
    mut v___f_5507_: *mut leanh::LeanObject,
    mut v___x_5508_: *mut leanh::LeanObject,
    mut v_m_5509_: *mut leanh::LeanObject,
    mut v_prec_5510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5511_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1;
    v___x_5512_ = leanh::lean_box(0);
    v___x_5513_ = l_Std_ExtTreeMap_foldr___redArg___closed__9;
    v___x_5514_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5513_,
        v___f_5507_,
        v___x_5512_,
        v_m_5509_,
    );
    v___x_5515_ = l_List_repr___redArg(v___x_5508_, v___x_5514_);
    v___x_5516_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5516_, 0, v___x_5511_);
    leanh::lean_ctor_set(v___x_5516_, 1, v___x_5515_);
    v___x_5517_ = l_Repr_addAppParen(v___x_5516_, v_prec_5510_);
    return v___x_5517_;
}
pub unsafe fn l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(
    mut v___f_5518_: *mut leanh::LeanObject,
    mut v___x_5519_: *mut leanh::LeanObject,
    mut v_m_5520_: *mut leanh::LeanObject,
    mut v_prec_5521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5522_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1(
        v___f_5518_,
        v___x_5519_,
        v_m_5520_,
        v_prec_5521_,
    );
    leanh::lean_dec(v_prec_5521_);
    return v_res_5522_;
}
pub unsafe fn l_Std_ExtTreeMap_instReprOfTransCmp___redArg(
    mut v_inst_5523_: *mut leanh::LeanObject,
    mut v_inst_5524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5525_ = l_Std_ExtTreeMap_toList___redArg___closed__0;
    v___f_5526_ = leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5526_, 0, v_inst_5524_);
    v___x_5527_ =
        leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5527_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5527_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5527_, 2, v_inst_5523_);
    leanh::lean_closure_set(v___x_5527_, 3, v___f_5526_);
    v___f_5528_ = leanh::lean_alloc_closure(
        l_Std_ExtTreeMap_instReprOfTransCmp___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_5528_, 0, v___f_5525_);
    leanh::lean_closure_set(v___f_5528_, 1, v___x_5527_);
    return v___f_5528_;
}
pub unsafe fn l_Std_ExtTreeMap_instReprOfTransCmp(
    mut v_00_u03b1_5529_: *mut leanh::LeanObject,
    mut v_00_u03b2_5530_: *mut leanh::LeanObject,
    mut v_cmp_5531_: *mut leanh::LeanObject,
    mut v_inst_5532_: *mut leanh::LeanObject,
    mut v_inst_5533_: *mut leanh::LeanObject,
    mut v_inst_5534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5535_ = l_Std_ExtTreeMap_instReprOfTransCmp___redArg(v_inst_5533_, v_inst_5534_);
    return v___x_5535_;
}
pub unsafe fn l_Std_ExtTreeMap_instReprOfTransCmp___boxed(
    mut v_00_u03b1_5536_: *mut leanh::LeanObject,
    mut v_00_u03b2_5537_: *mut leanh::LeanObject,
    mut v_cmp_5538_: *mut leanh::LeanObject,
    mut v_inst_5539_: *mut leanh::LeanObject,
    mut v_inst_5540_: *mut leanh::LeanObject,
    mut v_inst_5541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5542_ = l_Std_ExtTreeMap_instReprOfTransCmp(
        v_00_u03b1_5536_,
        v_00_u03b2_5537_,
        v_cmp_5538_,
        v_inst_5539_,
        v_inst_5540_,
        v_inst_5541_,
    );
    leanh::lean_dec_ref(v_cmp_5538_);
    return v_res_5542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtTreeMap_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_ExtDTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtTreeMap_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_ExtTreeMap___auto__1 = _init_l_Std_ExtTreeMap___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeMap___auto__1);
    l_Std_ExtTreeMap_ofList___auto__1 = _init_l_Std_ExtTreeMap_ofList___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeMap_ofList___auto__1);
    l_Std_ExtTreeMap_unitOfList___auto__1 = _init_l_Std_ExtTreeMap_unitOfList___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeMap_unitOfList___auto__1);
    l_Std_ExtTreeMap_ofArray___auto__1 = _init_l_Std_ExtTreeMap_ofArray___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeMap_ofArray___auto__1);
    l_Std_ExtTreeMap_unitOfArray___auto__1 = _init_l_Std_ExtTreeMap_unitOfArray___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtTreeMap_unitOfArray___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ExtTreeMap_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_ExtDTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_ExtTreeMap_Basic(builtin);
}