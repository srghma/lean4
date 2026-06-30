// Lean compiler output
// Module: Std.Data.ExtDTreeMap.Basic
// Imports: Std.Data.DTreeMap.Lemmas
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
    l_List_repr___redArg, l_Repr_addAppParen, l_Sigma_repr___boxed,
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
    l_Std_DTreeMap_Internal_Impl_alter___redArg, l_Std_DTreeMap_Internal_Impl_beq___redArg,
    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg,
    l_Std_DTreeMap_Internal_Impl_erase___redArg, l_Std_DTreeMap_Internal_Impl_filter___redArg,
    l_Std_DTreeMap_Internal_Impl_filterMap___redArg, l_Std_DTreeMap_Internal_Impl_insert___redArg,
    l_Std_DTreeMap_Internal_Impl_map___redArg, l_Std_DTreeMap_Internal_Impl_modify___redArg,
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
    l_Std_DTreeMap_Internal_Impl_contains___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg, l_Std_DTreeMap_Internal_Impl_foldl___redArg,
    l_Std_DTreeMap_Internal_Impl_foldlM___redArg, l_Std_DTreeMap_Internal_Impl_foldrM___redArg,
    l_Std_DTreeMap_Internal_Impl_forInStep___redArg, l_Std_DTreeMap_Internal_Impl_get___redArg,
    l_Std_DTreeMap_Internal_Impl_get_x3f___redArg, l_Std_DTreeMap_Internal_Impl_get_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_getD___redArg, l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKey___redArg, l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg,
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
    l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg,
    l_Std_DTreeMap_Internal_Impl_maxEntry___redArg,
    l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg, l_Std_DTreeMap_Internal_Impl_maxKey___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg, l_Std_DTreeMap_Internal_Impl_minEntry___redArg,
    l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_minEntryD___redArg, l_Std_DTreeMap_Internal_Impl_minKey___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_minKeyD___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Lemmas::{
    initialize_Std_Data_DTreeMap_Lemmas, runtime_initialize_Std_Data_DTreeMap_Lemmas,
};
pub static l_Std_ExtDTreeMap___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtDTreeMap___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__6_value: leanh::LeanStringObject<19> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtDTreeMap___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap___auto__1___closed__10_value: leanh::LeanStringObject<6> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_ExtDTreeMap___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtDTreeMap___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDTreeMap___auto__1___closed__14_value: leanh::LeanStringObject<8> =
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
static mut l_Std_ExtDTreeMap___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtDTreeMap___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDTreeMap___auto__1___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16710690322389477741 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtDTreeMap___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtDTreeMap___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_ExtDTreeMap___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0_value:
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
static mut l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1_value:
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
static mut l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2_value:
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
static mut l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_foldr___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_ExtDTreeMap_foldr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_foldr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_partition___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_ExtDTreeMap_partition___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_partition___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_any___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_ExtDTreeMap_any___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_any___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_keys___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDTreeMap_keys___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_keys___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_keysArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_ExtDTreeMap_keysArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_keysArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_values___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtDTreeMap_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDTreeMap_values___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_values___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_ExtDTreeMap_valuesArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_valuesArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_ExtDTreeMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_ExtDTreeMap_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtDTreeMap_ofList___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDTreeMap_toArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_ExtDTreeMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_ExtDTreeMap_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtDTreeMap_ofArray___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDTreeMap_Const_toList___redArg___closed__0_value:
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
    m_fun: l_Std_ExtDTreeMap_Const_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_ExtDTreeMap_Const_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_Const_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtDTreeMap_Const_ofList___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0_value:
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
    m_fun: l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1_value:
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
static mut l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_ExtDTreeMap_Const_ofArray___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_ExtDTreeMap_Const_unitOfList___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_ExtDTreeMap_Const_unitOfArray___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
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
        83, 116, 100, 46, 69, 120, 116, 68, 84, 114, 101, 101, 77, 97, 112, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value:
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
        l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3831_ = l_Std_ExtDTreeMap___auto__1___closed__10;
    v___x_3832_ = l_Lean_mkAtom(v___x_3831_);
    return v___x_3832_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__12_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__12,
    );
    v___x_3834_ = l_Std_ExtDTreeMap___auto__1___closed__5;
    v___x_3835_ = lean_array_push(v___x_3834_, v___x_3833_);
    return v___x_3835_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3837_ = l_Std_ExtDTreeMap___auto__1___closed__14;
    v___x_3838_ = lean_string_utf8_byte_size(v___x_3837_);
    return v___x_3838_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__15_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__15,
    );
    v___x_3840_ = leanh::lean_unsigned_to_nat(0);
    v___x_3841_ = l_Std_ExtDTreeMap___auto__1___closed__14;
    v___x_3842_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3842_, 0, v___x_3841_);
    leanh::lean_ctor_set(v___x_3842_, 1, v___x_3840_);
    leanh::lean_ctor_set(v___x_3842_, 2, v___x_3839_);
    return v___x_3842_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = leanh::lean_box(0);
    v___x_3846_ = l_Std_ExtDTreeMap___auto__1___closed__17;
    v___x_3847_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__16_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__16,
    );
    v___x_3848_ = leanh::lean_box(2);
    v___x_3849_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3849_, 0, v___x_3848_);
    leanh::lean_ctor_set(v___x_3849_, 1, v___x_3847_);
    leanh::lean_ctor_set(v___x_3849_, 2, v___x_3846_);
    leanh::lean_ctor_set(v___x_3849_, 3, v___x_3845_);
    return v___x_3849_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3850_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__18_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__18,
    );
    v___x_3851_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__13_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__13,
    );
    v___x_3852_ = lean_array_push(v___x_3851_, v___x_3850_);
    return v___x_3852_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__19_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__19,
    );
    v___x_3854_ = l_Std_ExtDTreeMap___auto__1___closed__11;
    v___x_3855_ = leanh::lean_box(2);
    v___x_3856_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3856_, 0, v___x_3855_);
    leanh::lean_ctor_set(v___x_3856_, 1, v___x_3854_);
    leanh::lean_ctor_set(v___x_3856_, 2, v___x_3853_);
    return v___x_3856_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__20_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__20,
    );
    v___x_3858_ = l_Std_ExtDTreeMap___auto__1___closed__5;
    v___x_3859_ = lean_array_push(v___x_3858_, v___x_3857_);
    return v___x_3859_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__21_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__21,
    );
    v___x_3861_ = l_Std_ExtDTreeMap___auto__1___closed__9;
    v___x_3862_ = leanh::lean_box(2);
    v___x_3863_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3863_, 0, v___x_3862_);
    leanh::lean_ctor_set(v___x_3863_, 1, v___x_3861_);
    leanh::lean_ctor_set(v___x_3863_, 2, v___x_3860_);
    return v___x_3863_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__22_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__22,
    );
    v___x_3865_ = l_Std_ExtDTreeMap___auto__1___closed__5;
    v___x_3866_ = lean_array_push(v___x_3865_, v___x_3864_);
    return v___x_3866_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__23_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__23,
    );
    v___x_3868_ = l_Std_ExtDTreeMap___auto__1___closed__7;
    v___x_3869_ = leanh::lean_box(2);
    v___x_3870_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3870_, 0, v___x_3869_);
    leanh::lean_ctor_set(v___x_3870_, 1, v___x_3868_);
    leanh::lean_ctor_set(v___x_3870_, 2, v___x_3867_);
    return v___x_3870_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3871_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__24_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__24,
    );
    v___x_3872_ = l_Std_ExtDTreeMap___auto__1___closed__5;
    v___x_3873_ = lean_array_push(v___x_3872_, v___x_3871_);
    return v___x_3873_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__25_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__25,
    );
    v___x_3875_ = l_Std_ExtDTreeMap___auto__1___closed__4;
    v___x_3876_ = leanh::lean_box(2);
    v___x_3877_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3877_, 0, v___x_3876_);
    leanh::lean_ctor_set(v___x_3877_, 1, v___x_3875_);
    leanh::lean_ctor_set(v___x_3877_, 2, v___x_3874_);
    return v___x_3877_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__26,
    );
    return v___x_3878_;
}
pub unsafe fn l_Std_ExtDTreeMap_mk___redArg(
    mut v_t_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_t_3879_);
    return v_t_3879_;
}
pub unsafe fn l_Std_ExtDTreeMap_mk___redArg___boxed(
    mut v_t_3880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3881_ = l_Std_ExtDTreeMap_mk___redArg(v_t_3880_);
    leanh::lean_dec(v_t_3880_);
    return v_res_3881_;
}
pub unsafe fn l_Std_ExtDTreeMap_mk(
    mut v_00_u03b1_3882_: *mut leanh::LeanObject,
    mut v_00_u03b2_3883_: *mut leanh::LeanObject,
    mut v_cmp_3884_: *mut leanh::LeanObject,
    mut v_t_3885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_t_3885_);
    return v_t_3885_;
}
pub unsafe fn l_Std_ExtDTreeMap_mk___boxed(
    mut v_00_u03b1_3886_: *mut leanh::LeanObject,
    mut v_00_u03b2_3887_: *mut leanh::LeanObject,
    mut v_cmp_3888_: *mut leanh::LeanObject,
    mut v_t_3889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3890_ = l_Std_ExtDTreeMap_mk(v_00_u03b1_3886_, v_00_u03b2_3887_, v_cmp_3888_, v_t_3889_);
    leanh::lean_dec(v_t_3889_);
    leanh::lean_dec_ref(v_cmp_3888_);
    return v_res_3890_;
}
pub unsafe fn l_Std_ExtDTreeMap_lift___redArg(
    mut v_f_3891_: *mut leanh::LeanObject,
    mut v_t_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3893_ = leanh::lean_apply_1(v_f_3891_, v_t_3892_);
    return v___x_3893_;
}
pub unsafe fn l_Std_ExtDTreeMap_lift(
    mut v_00_u03b1_3894_: *mut leanh::LeanObject,
    mut v_00_u03b2_3895_: *mut leanh::LeanObject,
    mut v_cmp_3896_: *mut leanh::LeanObject,
    mut v_00_u03b3_3897_: *mut leanh::LeanObject,
    mut v_f_3898_: *mut leanh::LeanObject,
    mut v_h_3899_: *mut leanh::LeanObject,
    mut v_t_3900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3901_ = leanh::lean_apply_1(v_f_3898_, v_t_3900_);
    return v___x_3901_;
}
pub unsafe fn l_Std_ExtDTreeMap_lift___boxed(
    mut v_00_u03b1_3902_: *mut leanh::LeanObject,
    mut v_00_u03b2_3903_: *mut leanh::LeanObject,
    mut v_cmp_3904_: *mut leanh::LeanObject,
    mut v_00_u03b3_3905_: *mut leanh::LeanObject,
    mut v_f_3906_: *mut leanh::LeanObject,
    mut v_h_3907_: *mut leanh::LeanObject,
    mut v_t_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_Std_ExtDTreeMap_lift(
        v_00_u03b1_3902_,
        v_00_u03b2_3903_,
        v_cmp_3904_,
        v_00_u03b3_3905_,
        v_f_3906_,
        v_h_3907_,
        v_t_3908_,
    );
    leanh::lean_dec_ref(v_cmp_3904_);
    return v_res_3909_;
}
pub unsafe fn l_Std_ExtDTreeMap_lift_u2082___redArg(
    mut v_f_3910_: *mut leanh::LeanObject,
    mut v_m_u2081_3911_: *mut leanh::LeanObject,
    mut v_m_u2082_3912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3913_ = leanh::lean_apply_2(v_f_3910_, v_m_u2081_3911_, v_m_u2082_3912_);
    return v___x_3913_;
}
pub unsafe fn l_Std_ExtDTreeMap_lift_u2082(
    mut v_00_u03b1_3914_: *mut leanh::LeanObject,
    mut v_00_u03b2_3915_: *mut leanh::LeanObject,
    mut v_cmp_3916_: *mut leanh::LeanObject,
    mut v_00_u03b3_3917_: *mut leanh::LeanObject,
    mut v_f_3918_: *mut leanh::LeanObject,
    mut v_h_3919_: *mut leanh::LeanObject,
    mut v_m_u2081_3920_: *mut leanh::LeanObject,
    mut v_m_u2082_3921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3922_ = leanh::lean_apply_2(v_f_3918_, v_m_u2081_3920_, v_m_u2082_3921_);
    return v___x_3922_;
}
pub unsafe fn l_Std_ExtDTreeMap_lift_u2082___boxed(
    mut v_00_u03b1_3923_: *mut leanh::LeanObject,
    mut v_00_u03b2_3924_: *mut leanh::LeanObject,
    mut v_cmp_3925_: *mut leanh::LeanObject,
    mut v_00_u03b3_3926_: *mut leanh::LeanObject,
    mut v_f_3927_: *mut leanh::LeanObject,
    mut v_h_3928_: *mut leanh::LeanObject,
    mut v_m_u2081_3929_: *mut leanh::LeanObject,
    mut v_m_u2082_3930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Std_ExtDTreeMap_lift_u2082(
        v_00_u03b1_3923_,
        v_00_u03b2_3924_,
        v_cmp_3925_,
        v_00_u03b3_3926_,
        v_f_3927_,
        v_h_3928_,
        v_m_u2081_3929_,
        v_m_u2082_3930_,
    );
    leanh::lean_dec_ref(v_cmp_3925_);
    return v_res_3931_;
}
pub unsafe fn l_Std_ExtDTreeMap_liftOn_u2082___redArg(
    mut v_t_u2081_3932_: *mut leanh::LeanObject,
    mut v_t_u2082_3933_: *mut leanh::LeanObject,
    mut v_f_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3935_ = leanh::lean_apply_2(v_f_3934_, v_t_u2081_3932_, v_t_u2082_3933_);
    return v___x_3935_;
}
pub unsafe fn l_Std_ExtDTreeMap_liftOn_u2082(
    mut v_00_u03b1_3936_: *mut leanh::LeanObject,
    mut v_00_u03b2_3937_: *mut leanh::LeanObject,
    mut v_cmp_3938_: *mut leanh::LeanObject,
    mut v_00_u03b3_3939_: *mut leanh::LeanObject,
    mut v_t_u2081_3940_: *mut leanh::LeanObject,
    mut v_t_u2082_3941_: *mut leanh::LeanObject,
    mut v_f_3942_: *mut leanh::LeanObject,
    mut v_h_3943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3944_ = leanh::lean_apply_2(v_f_3942_, v_t_u2081_3940_, v_t_u2082_3941_);
    return v___x_3944_;
}
pub unsafe fn l_Std_ExtDTreeMap_liftOn_u2082___boxed(
    mut v_00_u03b1_3945_: *mut leanh::LeanObject,
    mut v_00_u03b2_3946_: *mut leanh::LeanObject,
    mut v_cmp_3947_: *mut leanh::LeanObject,
    mut v_00_u03b3_3948_: *mut leanh::LeanObject,
    mut v_t_u2081_3949_: *mut leanh::LeanObject,
    mut v_t_u2082_3950_: *mut leanh::LeanObject,
    mut v_f_3951_: *mut leanh::LeanObject,
    mut v_h_3952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Std_ExtDTreeMap_liftOn_u2082(
        v_00_u03b1_3945_,
        v_00_u03b2_3946_,
        v_cmp_3947_,
        v_00_u03b3_3948_,
        v_t_u2081_3949_,
        v_t_u2082_3950_,
        v_f_3951_,
        v_h_3952_,
    );
    leanh::lean_dec_ref(v_cmp_3947_);
    return v_res_3953_;
}
pub unsafe fn l_Std_ExtDTreeMap_pliftOn___redArg(
    mut v_t_3954_: *mut leanh::LeanObject,
    mut v_f_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3956_ = leanh::lean_apply_2(v_f_3955_, v_t_3954_, leanh::lean_box(0));
    return v___x_3956_;
}
pub unsafe fn l_Std_ExtDTreeMap_pliftOn(
    mut v_00_u03b1_3957_: *mut leanh::LeanObject,
    mut v_00_u03b2_3958_: *mut leanh::LeanObject,
    mut v_cmp_3959_: *mut leanh::LeanObject,
    mut v_00_u03b3_3960_: *mut leanh::LeanObject,
    mut v_t_3961_: *mut leanh::LeanObject,
    mut v_f_3962_: *mut leanh::LeanObject,
    mut v_h_3963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3964_ = leanh::lean_apply_2(v_f_3962_, v_t_3961_, leanh::lean_box(0));
    return v___x_3964_;
}
pub unsafe fn l_Std_ExtDTreeMap_pliftOn___boxed(
    mut v_00_u03b1_3965_: *mut leanh::LeanObject,
    mut v_00_u03b2_3966_: *mut leanh::LeanObject,
    mut v_cmp_3967_: *mut leanh::LeanObject,
    mut v_00_u03b3_3968_: *mut leanh::LeanObject,
    mut v_t_3969_: *mut leanh::LeanObject,
    mut v_f_3970_: *mut leanh::LeanObject,
    mut v_h_3971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3972_ = l_Std_ExtDTreeMap_pliftOn(
        v_00_u03b1_3965_,
        v_00_u03b2_3966_,
        v_cmp_3967_,
        v_00_u03b3_3968_,
        v_t_3969_,
        v_f_3970_,
        v_h_3971_,
    );
    leanh::lean_dec_ref(v_cmp_3967_);
    return v_res_3972_;
}
pub unsafe fn l_Std_ExtDTreeMap_instCoeTypeForall(
    mut v_00_u03b1_3973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3974_ = leanh::lean_box(0);
    return v___x_3974_;
}
pub unsafe fn l_Std_ExtDTreeMap_empty(
    mut v_00_u03b1_3975_: *mut leanh::LeanObject,
    mut v_00_u03b2_3976_: *mut leanh::LeanObject,
    mut v_cmp_3977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3978_ = leanh::lean_box(1);
    return v___x_3978_;
}
pub unsafe fn l_Std_ExtDTreeMap_empty___boxed(
    mut v_00_u03b1_3979_: *mut leanh::LeanObject,
    mut v_00_u03b2_3980_: *mut leanh::LeanObject,
    mut v_cmp_3981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3982_ = l_Std_ExtDTreeMap_empty(v_00_u03b1_3979_, v_00_u03b2_3980_, v_cmp_3981_);
    leanh::lean_dec_ref(v_cmp_3981_);
    return v_res_3982_;
}
pub unsafe fn l_Std_ExtDTreeMap_instEmptyCollection(
    mut v_00_u03b1_3983_: *mut leanh::LeanObject,
    mut v_00_u03b2_3984_: *mut leanh::LeanObject,
    mut v_cmp_3985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3986_ = leanh::lean_box(1);
    return v___x_3986_;
}
pub unsafe fn l_Std_ExtDTreeMap_instEmptyCollection___boxed(
    mut v_00_u03b1_3987_: *mut leanh::LeanObject,
    mut v_00_u03b2_3988_: *mut leanh::LeanObject,
    mut v_cmp_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ =
        l_Std_ExtDTreeMap_instEmptyCollection(v_00_u03b1_3987_, v_00_u03b2_3988_, v_cmp_3989_);
    leanh::lean_dec_ref(v_cmp_3989_);
    return v_res_3990_;
}
pub unsafe fn l_Std_ExtDTreeMap_instInhabited(
    mut v_00_u03b1_3991_: *mut leanh::LeanObject,
    mut v_00_u03b2_3992_: *mut leanh::LeanObject,
    mut v_cmp_3993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3994_ = leanh::lean_box(1);
    return v___x_3994_;
}
pub unsafe fn l_Std_ExtDTreeMap_instInhabited___boxed(
    mut v_00_u03b1_3995_: *mut leanh::LeanObject,
    mut v_00_u03b2_3996_: *mut leanh::LeanObject,
    mut v_cmp_3997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Std_ExtDTreeMap_instInhabited(v_00_u03b1_3995_, v_00_u03b2_3996_, v_cmp_3997_);
    leanh::lean_dec_ref(v_cmp_3997_);
    return v_res_3998_;
}
pub unsafe fn l_Std_ExtDTreeMap_insert___redArg(
    mut v_cmp_3999_: *mut leanh::LeanObject,
    mut v_t_4000_: *mut leanh::LeanObject,
    mut v_a_4001_: *mut leanh::LeanObject,
    mut v_b_4002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4003_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_3999_, v_a_4001_, v_b_4002_, v_t_4000_);
    return v___x_4003_;
}
pub unsafe fn l_Std_ExtDTreeMap_insert(
    mut v_00_u03b1_4004_: *mut leanh::LeanObject,
    mut v_00_u03b2_4005_: *mut leanh::LeanObject,
    mut v_cmp_4006_: *mut leanh::LeanObject,
    mut v_inst_4007_: *mut leanh::LeanObject,
    mut v_t_4008_: *mut leanh::LeanObject,
    mut v_a_4009_: *mut leanh::LeanObject,
    mut v_b_4010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4011_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4006_, v_a_4009_, v_b_4010_, v_t_4008_);
    return v___x_4011_;
}
pub unsafe fn l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0(
    mut v_cmp_4012_: *mut leanh::LeanObject,
    mut v_e_4013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4014_ = leanh::lean_ctor_get(v_e_4013_, 0);
    leanh::lean_inc(v_fst_4014_);
    v_snd_4015_ = leanh::lean_ctor_get(v_e_4013_, 1);
    leanh::lean_inc(v_snd_4015_);
    leanh::lean_dec_ref(v_e_4013_);
    v___x_4016_ = leanh::lean_box(1);
    v___x_4017_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_4012_,
        v_fst_4014_,
        v_snd_4015_,
        v___x_4016_,
    );
    return v___x_4017_;
}
pub unsafe fn l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg(
    mut v_cmp_4018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4019_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4019_, 0, v_cmp_4018_);
    return v___f_4019_;
}
pub unsafe fn l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp(
    mut v_00_u03b1_4020_: *mut leanh::LeanObject,
    mut v_00_u03b2_4021_: *mut leanh::LeanObject,
    mut v_cmp_4022_: *mut leanh::LeanObject,
    mut v_inst_4023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4024_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instSingletonSigmaOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4024_, 0, v_cmp_4022_);
    return v___f_4024_;
}
pub unsafe fn l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0(
    mut v_cmp_4025_: *mut leanh::LeanObject,
    mut v_e_4026_: *mut leanh::LeanObject,
    mut v_s_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4028_ = leanh::lean_ctor_get(v_e_4026_, 0);
    leanh::lean_inc(v_fst_4028_);
    v_snd_4029_ = leanh::lean_ctor_get(v_e_4026_, 1);
    leanh::lean_inc(v_snd_4029_);
    leanh::lean_dec_ref(v_e_4026_);
    v___x_4030_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_4025_,
        v_fst_4028_,
        v_snd_4029_,
        v_s_4027_,
    );
    return v___x_4030_;
}
pub unsafe fn l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg(
    mut v_cmp_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4032_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4032_, 0, v_cmp_4031_);
    return v___f_4032_;
}
pub unsafe fn l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp(
    mut v_00_u03b1_4033_: *mut leanh::LeanObject,
    mut v_00_u03b2_4034_: *mut leanh::LeanObject,
    mut v_cmp_4035_: *mut leanh::LeanObject,
    mut v_inst_4036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4037_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instInsertSigmaOfTransCmp___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4037_, 0, v_cmp_4035_);
    return v___f_4037_;
}
pub unsafe fn l_Std_ExtDTreeMap_insertIfNew___redArg(
    mut v_cmp_4038_: *mut leanh::LeanObject,
    mut v_t_4039_: *mut leanh::LeanObject,
    mut v_a_4040_: *mut leanh::LeanObject,
    mut v_b_4041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4042_: u8 = 0;
    leanh::lean_inc(v_t_4039_);
    leanh::lean_inc(v_a_4040_);
    leanh::lean_inc_ref(v_cmp_4038_);
    v___x_4042_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4038_, v_a_4040_, v_t_4039_);
    if v___x_4042_ == 0 {
        let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4043_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4038_,
            v_a_4040_,
            v_b_4041_,
            v_t_4039_,
        );
        return v___x_4043_;
    } else {
        leanh::lean_dec(v_b_4041_);
        leanh::lean_dec(v_a_4040_);
        leanh::lean_dec_ref(v_cmp_4038_);
        return v_t_4039_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_insertIfNew(
    mut v_00_u03b1_4044_: *mut leanh::LeanObject,
    mut v_00_u03b2_4045_: *mut leanh::LeanObject,
    mut v_cmp_4046_: *mut leanh::LeanObject,
    mut v_inst_4047_: *mut leanh::LeanObject,
    mut v_t_4048_: *mut leanh::LeanObject,
    mut v_a_4049_: *mut leanh::LeanObject,
    mut v_b_4050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4051_: u8 = 0;
    leanh::lean_inc(v_t_4048_);
    leanh::lean_inc(v_a_4049_);
    leanh::lean_inc_ref(v_cmp_4046_);
    v___x_4051_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4046_, v_a_4049_, v_t_4048_);
    if v___x_4051_ == 0 {
        let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4052_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4046_,
            v_a_4049_,
            v_b_4050_,
            v_t_4048_,
        );
        return v___x_4052_;
    } else {
        leanh::lean_dec(v_b_4050_);
        leanh::lean_dec(v_a_4049_);
        leanh::lean_dec_ref(v_cmp_4046_);
        return v_t_4048_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_containsThenInsert___redArg(
    mut v_cmp_4053_: *mut leanh::LeanObject,
    mut v_t_4054_: *mut leanh::LeanObject,
    mut v_a_4055_: *mut leanh::LeanObject,
    mut v_b_4056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4057_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_4054_);
                v_m_4058_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_4053_,
                    v_a_4055_,
                    v_b_4056_,
                    v_t_4054_,
                );
                if leanh::lean_obj_tag(v_m_4058_) == 0 {
                    v_size_4064_ = leanh::lean_ctor_get(v_m_4058_, 0);
                    leanh::lean_inc(v_size_4064_);
                    v___y_4060_ = v_size_4064_;
                    state = 1;
                    continue;
                } else {
                    v___x_4065_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4060_ = v___x_4065_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4061_ = lean_nat_dec_eq(v_sz_4057_, v___y_4060_);
                leanh::lean_dec(v___y_4060_);
                leanh::lean_dec(v_sz_4057_);
                v___x_4062_ = leanh::lean_box((v___x_4061_) as usize);
                v___x_4063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4063_, 0, v___x_4062_);
                leanh::lean_ctor_set(v___x_4063_, 1, v_m_4058_);
                return v___x_4063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_containsThenInsert(
    mut v_00_u03b1_4066_: *mut leanh::LeanObject,
    mut v_00_u03b2_4067_: *mut leanh::LeanObject,
    mut v_cmp_4068_: *mut leanh::LeanObject,
    mut v_inst_4069_: *mut leanh::LeanObject,
    mut v_t_4070_: *mut leanh::LeanObject,
    mut v_a_4071_: *mut leanh::LeanObject,
    mut v_b_4072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4073_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_4070_);
                v_m_4074_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_4068_,
                    v_a_4071_,
                    v_b_4072_,
                    v_t_4070_,
                );
                if leanh::lean_obj_tag(v_m_4074_) == 0 {
                    v_size_4080_ = leanh::lean_ctor_get(v_m_4074_, 0);
                    leanh::lean_inc(v_size_4080_);
                    v___y_4076_ = v_size_4080_;
                    state = 1;
                    continue;
                } else {
                    v___x_4081_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4076_ = v___x_4081_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4077_ = lean_nat_dec_eq(v_sz_4073_, v___y_4076_);
                leanh::lean_dec(v___y_4076_);
                leanh::lean_dec(v_sz_4073_);
                v___x_4078_ = leanh::lean_box((v___x_4077_) as usize);
                v___x_4079_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4079_, 0, v___x_4078_);
                leanh::lean_ctor_set(v___x_4079_, 1, v_m_4074_);
                return v___x_4079_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_containsThenInsertIfNew___redArg(
    mut v_cmp_4082_: *mut leanh::LeanObject,
    mut v_t_4083_: *mut leanh::LeanObject,
    mut v_a_4084_: *mut leanh::LeanObject,
    mut v_b_4085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4086_: u8 = 0;
    leanh::lean_inc(v_t_4083_);
    leanh::lean_inc(v_a_4084_);
    leanh::lean_inc_ref(v_cmp_4082_);
    v___x_4086_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4082_, v_a_4084_, v_t_4083_);
    if v___x_4086_ == 0 {
        let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4087_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4082_,
            v_a_4084_,
            v_b_4085_,
            v_t_4083_,
        );
        v___x_4088_ = leanh::lean_box((v___x_4086_) as usize);
        v___x_4089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4089_, 0, v___x_4088_);
        leanh::lean_ctor_set(v___x_4089_, 1, v___x_4087_);
        return v___x_4089_;
    } else {
        let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_4085_);
        leanh::lean_dec(v_a_4084_);
        leanh::lean_dec_ref(v_cmp_4082_);
        v___x_4090_ = leanh::lean_box((v___x_4086_) as usize);
        v___x_4091_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4091_, 0, v___x_4090_);
        leanh::lean_ctor_set(v___x_4091_, 1, v_t_4083_);
        return v___x_4091_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_containsThenInsertIfNew(
    mut v_00_u03b1_4092_: *mut leanh::LeanObject,
    mut v_00_u03b2_4093_: *mut leanh::LeanObject,
    mut v_cmp_4094_: *mut leanh::LeanObject,
    mut v_inst_4095_: *mut leanh::LeanObject,
    mut v_t_4096_: *mut leanh::LeanObject,
    mut v_a_4097_: *mut leanh::LeanObject,
    mut v_b_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4099_: u8 = 0;
    leanh::lean_inc(v_t_4096_);
    leanh::lean_inc(v_a_4097_);
    leanh::lean_inc_ref(v_cmp_4094_);
    v___x_4099_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4094_, v_a_4097_, v_t_4096_);
    if v___x_4099_ == 0 {
        let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4100_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4094_,
            v_a_4097_,
            v_b_4098_,
            v_t_4096_,
        );
        v___x_4101_ = leanh::lean_box((v___x_4099_) as usize);
        v___x_4102_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4102_, 0, v___x_4101_);
        leanh::lean_ctor_set(v___x_4102_, 1, v___x_4100_);
        return v___x_4102_;
    } else {
        let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_4098_);
        leanh::lean_dec(v_a_4097_);
        leanh::lean_dec_ref(v_cmp_4094_);
        v___x_4103_ = leanh::lean_box((v___x_4099_) as usize);
        v___x_4104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4104_, 0, v___x_4103_);
        leanh::lean_ctor_set(v___x_4104_, 1, v_t_4096_);
        return v___x_4104_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getThenInsertIfNew_x3f___redArg(
    mut v_cmp_4105_: *mut leanh::LeanObject,
    mut v_t_4106_: *mut leanh::LeanObject,
    mut v_a_4107_: *mut leanh::LeanObject,
    mut v_b_4108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_4107_);
    leanh::lean_inc(v_t_4106_);
    leanh::lean_inc_ref(v_cmp_4105_);
    v___x_4109_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_4105_, v_t_4106_, v_a_4107_);
    if leanh::lean_obj_tag(v___x_4109_) == 0 {
        let mut v___x_4110_: u8 = 0;
        leanh::lean_inc(v_t_4106_);
        leanh::lean_inc(v_a_4107_);
        leanh::lean_inc_ref(v_cmp_4105_);
        v___x_4110_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4105_, v_a_4107_, v_t_4106_);
        if v___x_4110_ == 0 {
            let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4111_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_4105_,
                v_a_4107_,
                v_b_4108_,
                v_t_4106_,
            );
            v___x_4112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4112_, 0, v___x_4109_);
            leanh::lean_ctor_set(v___x_4112_, 1, v___x_4111_);
            return v___x_4112_;
        } else {
            let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_4108_);
            leanh::lean_dec(v_a_4107_);
            leanh::lean_dec_ref(v_cmp_4105_);
            v___x_4113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4113_, 0, v___x_4109_);
            leanh::lean_ctor_set(v___x_4113_, 1, v_t_4106_);
            return v___x_4113_;
        }
    } else {
        let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_4108_);
        leanh::lean_dec(v_a_4107_);
        leanh::lean_dec_ref(v_cmp_4105_);
        v___x_4114_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4114_, 0, v___x_4109_);
        leanh::lean_ctor_set(v___x_4114_, 1, v_t_4106_);
        return v___x_4114_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_4115_: *mut leanh::LeanObject,
    mut v_00_u03b2_4116_: *mut leanh::LeanObject,
    mut v_cmp_4117_: *mut leanh::LeanObject,
    mut v_inst_4118_: *mut leanh::LeanObject,
    mut v_inst_4119_: *mut leanh::LeanObject,
    mut v_t_4120_: *mut leanh::LeanObject,
    mut v_a_4121_: *mut leanh::LeanObject,
    mut v_b_4122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_4121_);
    leanh::lean_inc(v_t_4120_);
    leanh::lean_inc_ref(v_cmp_4117_);
    v___x_4123_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_4117_, v_t_4120_, v_a_4121_);
    if leanh::lean_obj_tag(v___x_4123_) == 0 {
        let mut v___x_4124_: u8 = 0;
        leanh::lean_inc(v_t_4120_);
        leanh::lean_inc(v_a_4121_);
        leanh::lean_inc_ref(v_cmp_4117_);
        v___x_4124_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4117_, v_a_4121_, v_t_4120_);
        if v___x_4124_ == 0 {
            let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4125_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_4117_,
                v_a_4121_,
                v_b_4122_,
                v_t_4120_,
            );
            v___x_4126_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4126_, 0, v___x_4123_);
            leanh::lean_ctor_set(v___x_4126_, 1, v___x_4125_);
            return v___x_4126_;
        } else {
            let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_4122_);
            leanh::lean_dec(v_a_4121_);
            leanh::lean_dec_ref(v_cmp_4117_);
            v___x_4127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4127_, 0, v___x_4123_);
            leanh::lean_ctor_set(v___x_4127_, 1, v_t_4120_);
            return v___x_4127_;
        }
    } else {
        let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_4122_);
        leanh::lean_dec(v_a_4121_);
        leanh::lean_dec_ref(v_cmp_4117_);
        v___x_4128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4128_, 0, v___x_4123_);
        leanh::lean_ctor_set(v___x_4128_, 1, v_t_4120_);
        return v___x_4128_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_contains___redArg(
    mut v_cmp_4129_: *mut leanh::LeanObject,
    mut v_t_4130_: *mut leanh::LeanObject,
    mut v_a_4131_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4132_: u8 = 0;
    v___x_4132_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4129_, v_a_4131_, v_t_4130_);
    return v___x_4132_;
}
pub unsafe fn l_Std_ExtDTreeMap_contains___redArg___boxed(
    mut v_cmp_4133_: *mut leanh::LeanObject,
    mut v_t_4134_: *mut leanh::LeanObject,
    mut v_a_4135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4136_: u8 = 0;
    let mut v_r_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Std_ExtDTreeMap_contains___redArg(v_cmp_4133_, v_t_4134_, v_a_4135_);
    v_r_4137_ = leanh::lean_box((v_res_4136_) as usize);
    return v_r_4137_;
}
pub unsafe fn l_Std_ExtDTreeMap_contains(
    mut v_00_u03b1_4138_: *mut leanh::LeanObject,
    mut v_00_u03b2_4139_: *mut leanh::LeanObject,
    mut v_cmp_4140_: *mut leanh::LeanObject,
    mut v_inst_4141_: *mut leanh::LeanObject,
    mut v_t_4142_: *mut leanh::LeanObject,
    mut v_a_4143_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4144_: u8 = 0;
    v___x_4144_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4140_, v_a_4143_, v_t_4142_);
    return v___x_4144_;
}
pub unsafe fn l_Std_ExtDTreeMap_contains___boxed(
    mut v_00_u03b1_4145_: *mut leanh::LeanObject,
    mut v_00_u03b2_4146_: *mut leanh::LeanObject,
    mut v_cmp_4147_: *mut leanh::LeanObject,
    mut v_inst_4148_: *mut leanh::LeanObject,
    mut v_t_4149_: *mut leanh::LeanObject,
    mut v_a_4150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4151_: u8 = 0;
    let mut v_r_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4151_ = l_Std_ExtDTreeMap_contains(
        v_00_u03b1_4145_,
        v_00_u03b2_4146_,
        v_cmp_4147_,
        v_inst_4148_,
        v_t_4149_,
        v_a_4150_,
    );
    v_r_4152_ = leanh::lean_box((v_res_4151_) as usize);
    return v_r_4152_;
}
pub unsafe fn l_Std_ExtDTreeMap_instMembershipOfTransCmp(
    mut v_00_u03b1_4153_: *mut leanh::LeanObject,
    mut v_00_u03b2_4154_: *mut leanh::LeanObject,
    mut v_cmp_4155_: *mut leanh::LeanObject,
    mut v_inst_4156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4157_ = leanh::lean_box(0);
    return v___x_4157_;
}
pub unsafe fn l_Std_ExtDTreeMap_instMembershipOfTransCmp___boxed(
    mut v_00_u03b1_4158_: *mut leanh::LeanObject,
    mut v_00_u03b2_4159_: *mut leanh::LeanObject,
    mut v_cmp_4160_: *mut leanh::LeanObject,
    mut v_inst_4161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4162_ = l_Std_ExtDTreeMap_instMembershipOfTransCmp(
        v_00_u03b1_4158_,
        v_00_u03b2_4159_,
        v_cmp_4160_,
        v_inst_4161_,
    );
    leanh::lean_dec_ref(v_cmp_4160_);
    return v_res_4162_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableMem___redArg(
    mut v_cmp_4163_: *mut leanh::LeanObject,
    mut v_m_4164_: *mut leanh::LeanObject,
    mut v_a_4165_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4166_: u8 = 0;
    v___x_4166_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4163_, v_a_4165_, v_m_4164_);
    return v___x_4166_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableMem___redArg___boxed(
    mut v_cmp_4167_: *mut leanh::LeanObject,
    mut v_m_4168_: *mut leanh::LeanObject,
    mut v_a_4169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4170_: u8 = 0;
    let mut v_r_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4170_ = l_Std_ExtDTreeMap_instDecidableMem___redArg(v_cmp_4167_, v_m_4168_, v_a_4169_);
    v_r_4171_ = leanh::lean_box((v_res_4170_) as usize);
    return v_r_4171_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableMem(
    mut v_00_u03b1_4172_: *mut leanh::LeanObject,
    mut v_00_u03b2_4173_: *mut leanh::LeanObject,
    mut v_cmp_4174_: *mut leanh::LeanObject,
    mut v_inst_4175_: *mut leanh::LeanObject,
    mut v_m_4176_: *mut leanh::LeanObject,
    mut v_a_4177_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4178_: u8 = 0;
    v___x_4178_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4174_, v_a_4177_, v_m_4176_);
    return v___x_4178_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableMem___boxed(
    mut v_00_u03b1_4179_: *mut leanh::LeanObject,
    mut v_00_u03b2_4180_: *mut leanh::LeanObject,
    mut v_cmp_4181_: *mut leanh::LeanObject,
    mut v_inst_4182_: *mut leanh::LeanObject,
    mut v_m_4183_: *mut leanh::LeanObject,
    mut v_a_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4185_: u8 = 0;
    let mut v_r_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4185_ = l_Std_ExtDTreeMap_instDecidableMem(
        v_00_u03b1_4179_,
        v_00_u03b2_4180_,
        v_cmp_4181_,
        v_inst_4182_,
        v_m_4183_,
        v_a_4184_,
    );
    v_r_4186_ = leanh::lean_box((v_res_4185_) as usize);
    return v_r_4186_;
}
pub unsafe fn l_Std_ExtDTreeMap_size___redArg(
    mut v_t_4187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_4187_) == 0 {
        let mut v_size_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_size_4188_ = leanh::lean_ctor_get(v_t_4187_, 0);
        leanh::lean_inc(v_size_4188_);
        return v_size_4188_;
    } else {
        let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4189_ = leanh::lean_unsigned_to_nat(0);
        return v___x_4189_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_size___redArg___boxed(
    mut v_t_4190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4191_ = l_Std_ExtDTreeMap_size___redArg(v_t_4190_);
    leanh::lean_dec(v_t_4190_);
    return v_res_4191_;
}
pub unsafe fn l_Std_ExtDTreeMap_size(
    mut v_00_u03b1_4192_: *mut leanh::LeanObject,
    mut v_00_u03b2_4193_: *mut leanh::LeanObject,
    mut v_cmp_4194_: *mut leanh::LeanObject,
    mut v_t_4195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_4195_) == 0 {
        let mut v_size_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_size_4196_ = leanh::lean_ctor_get(v_t_4195_, 0);
        leanh::lean_inc(v_size_4196_);
        return v_size_4196_;
    } else {
        let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4197_ = leanh::lean_unsigned_to_nat(0);
        return v___x_4197_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_size___boxed(
    mut v_00_u03b1_4198_: *mut leanh::LeanObject,
    mut v_00_u03b2_4199_: *mut leanh::LeanObject,
    mut v_cmp_4200_: *mut leanh::LeanObject,
    mut v_t_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ =
        l_Std_ExtDTreeMap_size(v_00_u03b1_4198_, v_00_u03b2_4199_, v_cmp_4200_, v_t_4201_);
    leanh::lean_dec(v_t_4201_);
    leanh::lean_dec_ref(v_cmp_4200_);
    return v_res_4202_;
}
pub unsafe fn l_Std_ExtDTreeMap_isEmpty___redArg(
    mut v_t_4203_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_t_4203_) == 0 {
        let mut v___x_4204_: u8 = 0;
        v___x_4204_ = 0;
        return v___x_4204_;
    } else {
        let mut v___x_4205_: u8 = 0;
        v___x_4205_ = 1;
        return v___x_4205_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_isEmpty___redArg___boxed(
    mut v_t_4206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4207_: u8 = 0;
    let mut v_r_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_Std_ExtDTreeMap_isEmpty___redArg(v_t_4206_);
    leanh::lean_dec(v_t_4206_);
    v_r_4208_ = leanh::lean_box((v_res_4207_) as usize);
    return v_r_4208_;
}
pub unsafe fn l_Std_ExtDTreeMap_isEmpty(
    mut v_00_u03b1_4209_: *mut leanh::LeanObject,
    mut v_00_u03b2_4210_: *mut leanh::LeanObject,
    mut v_cmp_4211_: *mut leanh::LeanObject,
    mut v_t_4212_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_t_4212_) == 0 {
        let mut v___x_4213_: u8 = 0;
        v___x_4213_ = 0;
        return v___x_4213_;
    } else {
        let mut v___x_4214_: u8 = 0;
        v___x_4214_ = 1;
        return v___x_4214_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_isEmpty___boxed(
    mut v_00_u03b1_4215_: *mut leanh::LeanObject,
    mut v_00_u03b2_4216_: *mut leanh::LeanObject,
    mut v_cmp_4217_: *mut leanh::LeanObject,
    mut v_t_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4219_: u8 = 0;
    let mut v_r_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4219_ =
        l_Std_ExtDTreeMap_isEmpty(v_00_u03b1_4215_, v_00_u03b2_4216_, v_cmp_4217_, v_t_4218_);
    leanh::lean_dec(v_t_4218_);
    leanh::lean_dec_ref(v_cmp_4217_);
    v_r_4220_ = leanh::lean_box((v_res_4219_) as usize);
    return v_r_4220_;
}
pub unsafe fn l_Std_ExtDTreeMap_erase___redArg(
    mut v_cmp_4221_: *mut leanh::LeanObject,
    mut v_t_4222_: *mut leanh::LeanObject,
    mut v_a_4223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4224_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4221_, v_a_4223_, v_t_4222_);
    return v___x_4224_;
}
pub unsafe fn l_Std_ExtDTreeMap_erase(
    mut v_00_u03b1_4225_: *mut leanh::LeanObject,
    mut v_00_u03b2_4226_: *mut leanh::LeanObject,
    mut v_cmp_4227_: *mut leanh::LeanObject,
    mut v_inst_4228_: *mut leanh::LeanObject,
    mut v_t_4229_: *mut leanh::LeanObject,
    mut v_a_4230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4231_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4227_, v_a_4230_, v_t_4229_);
    return v___x_4231_;
}
pub unsafe fn l_Std_ExtDTreeMap_get_x3f___redArg(
    mut v_cmp_4232_: *mut leanh::LeanObject,
    mut v_t_4233_: *mut leanh::LeanObject,
    mut v_a_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4235_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_4232_, v_t_4233_, v_a_4234_);
    return v___x_4235_;
}
pub unsafe fn l_Std_ExtDTreeMap_get_x3f(
    mut v_00_u03b1_4236_: *mut leanh::LeanObject,
    mut v_00_u03b2_4237_: *mut leanh::LeanObject,
    mut v_cmp_4238_: *mut leanh::LeanObject,
    mut v_inst_4239_: *mut leanh::LeanObject,
    mut v_inst_4240_: *mut leanh::LeanObject,
    mut v_t_4241_: *mut leanh::LeanObject,
    mut v_a_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4243_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_4238_, v_t_4241_, v_a_4242_);
    return v___x_4243_;
}
pub unsafe fn l_Std_ExtDTreeMap_get___redArg(
    mut v_cmp_4244_: *mut leanh::LeanObject,
    mut v_t_4245_: *mut leanh::LeanObject,
    mut v_a_4246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_4244_, v_t_4245_, v_a_4246_);
    return v___x_4247_;
}
pub unsafe fn l_Std_ExtDTreeMap_get(
    mut v_00_u03b1_4248_: *mut leanh::LeanObject,
    mut v_00_u03b2_4249_: *mut leanh::LeanObject,
    mut v_cmp_4250_: *mut leanh::LeanObject,
    mut v_inst_4251_: *mut leanh::LeanObject,
    mut v_inst_4252_: *mut leanh::LeanObject,
    mut v_t_4253_: *mut leanh::LeanObject,
    mut v_a_4254_: *mut leanh::LeanObject,
    mut v_h_4255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4256_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_4250_, v_t_4253_, v_a_4254_);
    return v___x_4256_;
}
pub unsafe fn l_Std_ExtDTreeMap_get_x21___redArg(
    mut v_cmp_4257_: *mut leanh::LeanObject,
    mut v_t_4258_: *mut leanh::LeanObject,
    mut v_a_4259_: *mut leanh::LeanObject,
    mut v_inst_4260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4261_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(
        v_cmp_4257_,
        v_t_4258_,
        v_a_4259_,
        v_inst_4260_,
    );
    return v___x_4261_;
}
pub unsafe fn l_Std_ExtDTreeMap_get_x21___redArg___boxed(
    mut v_cmp_4262_: *mut leanh::LeanObject,
    mut v_t_4263_: *mut leanh::LeanObject,
    mut v_a_4264_: *mut leanh::LeanObject,
    mut v_inst_4265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4266_ =
        l_Std_ExtDTreeMap_get_x21___redArg(v_cmp_4262_, v_t_4263_, v_a_4264_, v_inst_4265_);
    leanh::lean_dec(v_inst_4265_);
    return v_res_4266_;
}
pub unsafe fn l_Std_ExtDTreeMap_get_x21(
    mut v_00_u03b1_4267_: *mut leanh::LeanObject,
    mut v_00_u03b2_4268_: *mut leanh::LeanObject,
    mut v_cmp_4269_: *mut leanh::LeanObject,
    mut v_inst_4270_: *mut leanh::LeanObject,
    mut v_inst_4271_: *mut leanh::LeanObject,
    mut v_t_4272_: *mut leanh::LeanObject,
    mut v_a_4273_: *mut leanh::LeanObject,
    mut v_inst_4274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4275_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(
        v_cmp_4269_,
        v_t_4272_,
        v_a_4273_,
        v_inst_4274_,
    );
    return v___x_4275_;
}
pub unsafe fn l_Std_ExtDTreeMap_get_x21___boxed(
    mut v_00_u03b1_4276_: *mut leanh::LeanObject,
    mut v_00_u03b2_4277_: *mut leanh::LeanObject,
    mut v_cmp_4278_: *mut leanh::LeanObject,
    mut v_inst_4279_: *mut leanh::LeanObject,
    mut v_inst_4280_: *mut leanh::LeanObject,
    mut v_t_4281_: *mut leanh::LeanObject,
    mut v_a_4282_: *mut leanh::LeanObject,
    mut v_inst_4283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4284_ = l_Std_ExtDTreeMap_get_x21(
        v_00_u03b1_4276_,
        v_00_u03b2_4277_,
        v_cmp_4278_,
        v_inst_4279_,
        v_inst_4280_,
        v_t_4281_,
        v_a_4282_,
        v_inst_4283_,
    );
    leanh::lean_dec(v_inst_4283_);
    return v_res_4284_;
}
pub unsafe fn l_Std_ExtDTreeMap_getD___redArg(
    mut v_cmp_4285_: *mut leanh::LeanObject,
    mut v_t_4286_: *mut leanh::LeanObject,
    mut v_a_4287_: *mut leanh::LeanObject,
    mut v_fallback_4288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4289_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(
        v_cmp_4285_,
        v_t_4286_,
        v_a_4287_,
        v_fallback_4288_,
    );
    return v___x_4289_;
}
pub unsafe fn l_Std_ExtDTreeMap_getD___redArg___boxed(
    mut v_cmp_4290_: *mut leanh::LeanObject,
    mut v_t_4291_: *mut leanh::LeanObject,
    mut v_a_4292_: *mut leanh::LeanObject,
    mut v_fallback_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4294_ =
        l_Std_ExtDTreeMap_getD___redArg(v_cmp_4290_, v_t_4291_, v_a_4292_, v_fallback_4293_);
    leanh::lean_dec(v_fallback_4293_);
    return v_res_4294_;
}
pub unsafe fn l_Std_ExtDTreeMap_getD(
    mut v_00_u03b1_4295_: *mut leanh::LeanObject,
    mut v_00_u03b2_4296_: *mut leanh::LeanObject,
    mut v_cmp_4297_: *mut leanh::LeanObject,
    mut v_inst_4298_: *mut leanh::LeanObject,
    mut v_inst_4299_: *mut leanh::LeanObject,
    mut v_t_4300_: *mut leanh::LeanObject,
    mut v_a_4301_: *mut leanh::LeanObject,
    mut v_fallback_4302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4303_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(
        v_cmp_4297_,
        v_t_4300_,
        v_a_4301_,
        v_fallback_4302_,
    );
    return v___x_4303_;
}
pub unsafe fn l_Std_ExtDTreeMap_getD___boxed(
    mut v_00_u03b1_4304_: *mut leanh::LeanObject,
    mut v_00_u03b2_4305_: *mut leanh::LeanObject,
    mut v_cmp_4306_: *mut leanh::LeanObject,
    mut v_inst_4307_: *mut leanh::LeanObject,
    mut v_inst_4308_: *mut leanh::LeanObject,
    mut v_t_4309_: *mut leanh::LeanObject,
    mut v_a_4310_: *mut leanh::LeanObject,
    mut v_fallback_4311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4312_ = l_Std_ExtDTreeMap_getD(
        v_00_u03b1_4304_,
        v_00_u03b2_4305_,
        v_cmp_4306_,
        v_inst_4307_,
        v_inst_4308_,
        v_t_4309_,
        v_a_4310_,
        v_fallback_4311_,
    );
    leanh::lean_dec(v_fallback_4311_);
    return v_res_4312_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey_x3f___redArg(
    mut v_cmp_4313_: *mut leanh::LeanObject,
    mut v_t_4314_: *mut leanh::LeanObject,
    mut v_a_4315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4316_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_4313_, v_t_4314_, v_a_4315_);
    return v___x_4316_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey_x3f(
    mut v_00_u03b1_4317_: *mut leanh::LeanObject,
    mut v_00_u03b2_4318_: *mut leanh::LeanObject,
    mut v_cmp_4319_: *mut leanh::LeanObject,
    mut v_inst_4320_: *mut leanh::LeanObject,
    mut v_t_4321_: *mut leanh::LeanObject,
    mut v_a_4322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4323_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_4319_, v_t_4321_, v_a_4322_);
    return v___x_4323_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey___redArg(
    mut v_cmp_4324_: *mut leanh::LeanObject,
    mut v_t_4325_: *mut leanh::LeanObject,
    mut v_a_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4327_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_4324_, v_t_4325_, v_a_4326_);
    return v___x_4327_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey(
    mut v_00_u03b1_4328_: *mut leanh::LeanObject,
    mut v_00_u03b2_4329_: *mut leanh::LeanObject,
    mut v_cmp_4330_: *mut leanh::LeanObject,
    mut v_inst_4331_: *mut leanh::LeanObject,
    mut v_t_4332_: *mut leanh::LeanObject,
    mut v_a_4333_: *mut leanh::LeanObject,
    mut v_h_4334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4335_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_4330_, v_t_4332_, v_a_4333_);
    return v___x_4335_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey_x21___redArg(
    mut v_cmp_4336_: *mut leanh::LeanObject,
    mut v_inst_4337_: *mut leanh::LeanObject,
    mut v_t_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4340_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_4336_,
        v_t_4338_,
        v_a_4339_,
        v_inst_4337_,
    );
    return v___x_4340_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey_x21___redArg___boxed(
    mut v_cmp_4341_: *mut leanh::LeanObject,
    mut v_inst_4342_: *mut leanh::LeanObject,
    mut v_t_4343_: *mut leanh::LeanObject,
    mut v_a_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4345_ =
        l_Std_ExtDTreeMap_getKey_x21___redArg(v_cmp_4341_, v_inst_4342_, v_t_4343_, v_a_4344_);
    leanh::lean_dec(v_inst_4342_);
    return v_res_4345_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey_x21(
    mut v_00_u03b1_4346_: *mut leanh::LeanObject,
    mut v_00_u03b2_4347_: *mut leanh::LeanObject,
    mut v_cmp_4348_: *mut leanh::LeanObject,
    mut v_inst_4349_: *mut leanh::LeanObject,
    mut v_inst_4350_: *mut leanh::LeanObject,
    mut v_t_4351_: *mut leanh::LeanObject,
    mut v_a_4352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_4348_,
        v_t_4351_,
        v_a_4352_,
        v_inst_4350_,
    );
    return v___x_4353_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKey_x21___boxed(
    mut v_00_u03b1_4354_: *mut leanh::LeanObject,
    mut v_00_u03b2_4355_: *mut leanh::LeanObject,
    mut v_cmp_4356_: *mut leanh::LeanObject,
    mut v_inst_4357_: *mut leanh::LeanObject,
    mut v_inst_4358_: *mut leanh::LeanObject,
    mut v_t_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4361_ = l_Std_ExtDTreeMap_getKey_x21(
        v_00_u03b1_4354_,
        v_00_u03b2_4355_,
        v_cmp_4356_,
        v_inst_4357_,
        v_inst_4358_,
        v_t_4359_,
        v_a_4360_,
    );
    leanh::lean_dec(v_inst_4358_);
    return v_res_4361_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyD___redArg(
    mut v_cmp_4362_: *mut leanh::LeanObject,
    mut v_t_4363_: *mut leanh::LeanObject,
    mut v_a_4364_: *mut leanh::LeanObject,
    mut v_fallback_4365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4366_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_4362_,
        v_t_4363_,
        v_a_4364_,
        v_fallback_4365_,
    );
    return v___x_4366_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyD___redArg___boxed(
    mut v_cmp_4367_: *mut leanh::LeanObject,
    mut v_t_4368_: *mut leanh::LeanObject,
    mut v_a_4369_: *mut leanh::LeanObject,
    mut v_fallback_4370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4371_ =
        l_Std_ExtDTreeMap_getKeyD___redArg(v_cmp_4367_, v_t_4368_, v_a_4369_, v_fallback_4370_);
    leanh::lean_dec(v_fallback_4370_);
    return v_res_4371_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyD(
    mut v_00_u03b1_4372_: *mut leanh::LeanObject,
    mut v_00_u03b2_4373_: *mut leanh::LeanObject,
    mut v_cmp_4374_: *mut leanh::LeanObject,
    mut v_inst_4375_: *mut leanh::LeanObject,
    mut v_t_4376_: *mut leanh::LeanObject,
    mut v_a_4377_: *mut leanh::LeanObject,
    mut v_fallback_4378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4379_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_4374_,
        v_t_4376_,
        v_a_4377_,
        v_fallback_4378_,
    );
    return v___x_4379_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyD___boxed(
    mut v_00_u03b1_4380_: *mut leanh::LeanObject,
    mut v_00_u03b2_4381_: *mut leanh::LeanObject,
    mut v_cmp_4382_: *mut leanh::LeanObject,
    mut v_inst_4383_: *mut leanh::LeanObject,
    mut v_t_4384_: *mut leanh::LeanObject,
    mut v_a_4385_: *mut leanh::LeanObject,
    mut v_fallback_4386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4387_ = l_Std_ExtDTreeMap_getKeyD(
        v_00_u03b1_4380_,
        v_00_u03b2_4381_,
        v_cmp_4382_,
        v_inst_4383_,
        v_t_4384_,
        v_a_4385_,
        v_fallback_4386_,
    );
    leanh::lean_dec(v_fallback_4386_);
    return v_res_4387_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x3f___redArg(
    mut v_t_4388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_4388_);
    return v___x_4389_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x3f___redArg___boxed(
    mut v_t_4390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4391_ = l_Std_ExtDTreeMap_minEntry_x3f___redArg(v_t_4390_);
    leanh::lean_dec(v_t_4390_);
    return v_res_4391_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x3f(
    mut v_00_u03b1_4392_: *mut leanh::LeanObject,
    mut v_00_u03b2_4393_: *mut leanh::LeanObject,
    mut v_cmp_4394_: *mut leanh::LeanObject,
    mut v_inst_4395_: *mut leanh::LeanObject,
    mut v_t_4396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_4396_);
    return v___x_4397_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x3f___boxed(
    mut v_00_u03b1_4398_: *mut leanh::LeanObject,
    mut v_00_u03b2_4399_: *mut leanh::LeanObject,
    mut v_cmp_4400_: *mut leanh::LeanObject,
    mut v_inst_4401_: *mut leanh::LeanObject,
    mut v_t_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4403_ = l_Std_ExtDTreeMap_minEntry_x3f(
        v_00_u03b1_4398_,
        v_00_u03b2_4399_,
        v_cmp_4400_,
        v_inst_4401_,
        v_t_4402_,
    );
    leanh::lean_dec(v_t_4402_);
    leanh::lean_dec_ref(v_cmp_4400_);
    return v_res_4403_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry___redArg(
    mut v_t_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4405_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_4404_);
    return v___x_4405_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry___redArg___boxed(
    mut v_t_4406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4407_ = l_Std_ExtDTreeMap_minEntry___redArg(v_t_4406_);
    leanh::lean_dec(v_t_4406_);
    return v_res_4407_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry(
    mut v_00_u03b1_4408_: *mut leanh::LeanObject,
    mut v_00_u03b2_4409_: *mut leanh::LeanObject,
    mut v_cmp_4410_: *mut leanh::LeanObject,
    mut v_inst_4411_: *mut leanh::LeanObject,
    mut v_t_4412_: *mut leanh::LeanObject,
    mut v_h_4413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4414_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_4412_);
    return v___x_4414_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry___boxed(
    mut v_00_u03b1_4415_: *mut leanh::LeanObject,
    mut v_00_u03b2_4416_: *mut leanh::LeanObject,
    mut v_cmp_4417_: *mut leanh::LeanObject,
    mut v_inst_4418_: *mut leanh::LeanObject,
    mut v_t_4419_: *mut leanh::LeanObject,
    mut v_h_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4421_ = l_Std_ExtDTreeMap_minEntry(
        v_00_u03b1_4415_,
        v_00_u03b2_4416_,
        v_cmp_4417_,
        v_inst_4418_,
        v_t_4419_,
        v_h_4420_,
    );
    leanh::lean_dec(v_t_4419_);
    leanh::lean_dec_ref(v_cmp_4417_);
    return v_res_4421_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x21___redArg(
    mut v_inst_4422_: *mut leanh::LeanObject,
    mut v_t_4423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4424_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_4422_, v_t_4423_);
    return v___x_4424_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x21___redArg___boxed(
    mut v_inst_4425_: *mut leanh::LeanObject,
    mut v_t_4426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4427_ = l_Std_ExtDTreeMap_minEntry_x21___redArg(v_inst_4425_, v_t_4426_);
    leanh::lean_dec(v_t_4426_);
    leanh::lean_dec_ref(v_inst_4425_);
    return v_res_4427_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x21(
    mut v_00_u03b1_4428_: *mut leanh::LeanObject,
    mut v_00_u03b2_4429_: *mut leanh::LeanObject,
    mut v_cmp_4430_: *mut leanh::LeanObject,
    mut v_inst_4431_: *mut leanh::LeanObject,
    mut v_inst_4432_: *mut leanh::LeanObject,
    mut v_t_4433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4434_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_4432_, v_t_4433_);
    return v___x_4434_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntry_x21___boxed(
    mut v_00_u03b1_4435_: *mut leanh::LeanObject,
    mut v_00_u03b2_4436_: *mut leanh::LeanObject,
    mut v_cmp_4437_: *mut leanh::LeanObject,
    mut v_inst_4438_: *mut leanh::LeanObject,
    mut v_inst_4439_: *mut leanh::LeanObject,
    mut v_t_4440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4441_ = l_Std_ExtDTreeMap_minEntry_x21(
        v_00_u03b1_4435_,
        v_00_u03b2_4436_,
        v_cmp_4437_,
        v_inst_4438_,
        v_inst_4439_,
        v_t_4440_,
    );
    leanh::lean_dec(v_t_4440_);
    leanh::lean_dec_ref(v_inst_4439_);
    leanh::lean_dec_ref(v_cmp_4437_);
    return v_res_4441_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntryD___redArg(
    mut v_t_4442_: *mut leanh::LeanObject,
    mut v_fallback_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4444_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_4442_, v_fallback_4443_);
    return v___x_4444_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntryD___redArg___boxed(
    mut v_t_4445_: *mut leanh::LeanObject,
    mut v_fallback_4446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4447_ = l_Std_ExtDTreeMap_minEntryD___redArg(v_t_4445_, v_fallback_4446_);
    leanh::lean_dec_ref(v_fallback_4446_);
    leanh::lean_dec(v_t_4445_);
    return v_res_4447_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntryD(
    mut v_00_u03b1_4448_: *mut leanh::LeanObject,
    mut v_00_u03b2_4449_: *mut leanh::LeanObject,
    mut v_cmp_4450_: *mut leanh::LeanObject,
    mut v_inst_4451_: *mut leanh::LeanObject,
    mut v_t_4452_: *mut leanh::LeanObject,
    mut v_fallback_4453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4454_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_4452_, v_fallback_4453_);
    return v___x_4454_;
}
pub unsafe fn l_Std_ExtDTreeMap_minEntryD___boxed(
    mut v_00_u03b1_4455_: *mut leanh::LeanObject,
    mut v_00_u03b2_4456_: *mut leanh::LeanObject,
    mut v_cmp_4457_: *mut leanh::LeanObject,
    mut v_inst_4458_: *mut leanh::LeanObject,
    mut v_t_4459_: *mut leanh::LeanObject,
    mut v_fallback_4460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4461_ = l_Std_ExtDTreeMap_minEntryD(
        v_00_u03b1_4455_,
        v_00_u03b2_4456_,
        v_cmp_4457_,
        v_inst_4458_,
        v_t_4459_,
        v_fallback_4460_,
    );
    leanh::lean_dec_ref(v_fallback_4460_);
    leanh::lean_dec(v_t_4459_);
    leanh::lean_dec_ref(v_cmp_4457_);
    return v_res_4461_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x3f___redArg(
    mut v_t_4462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_4462_);
    return v___x_4463_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x3f___redArg___boxed(
    mut v_t_4464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Std_ExtDTreeMap_maxEntry_x3f___redArg(v_t_4464_);
    leanh::lean_dec(v_t_4464_);
    return v_res_4465_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x3f(
    mut v_00_u03b1_4466_: *mut leanh::LeanObject,
    mut v_00_u03b2_4467_: *mut leanh::LeanObject,
    mut v_cmp_4468_: *mut leanh::LeanObject,
    mut v_inst_4469_: *mut leanh::LeanObject,
    mut v_t_4470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4471_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_4470_);
    return v___x_4471_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x3f___boxed(
    mut v_00_u03b1_4472_: *mut leanh::LeanObject,
    mut v_00_u03b2_4473_: *mut leanh::LeanObject,
    mut v_cmp_4474_: *mut leanh::LeanObject,
    mut v_inst_4475_: *mut leanh::LeanObject,
    mut v_t_4476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Std_ExtDTreeMap_maxEntry_x3f(
        v_00_u03b1_4472_,
        v_00_u03b2_4473_,
        v_cmp_4474_,
        v_inst_4475_,
        v_t_4476_,
    );
    leanh::lean_dec(v_t_4476_);
    leanh::lean_dec_ref(v_cmp_4474_);
    return v_res_4477_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry___redArg(
    mut v_t_4478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4479_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_4478_);
    return v___x_4479_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry___redArg___boxed(
    mut v_t_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_Std_ExtDTreeMap_maxEntry___redArg(v_t_4480_);
    leanh::lean_dec(v_t_4480_);
    return v_res_4481_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry(
    mut v_00_u03b1_4482_: *mut leanh::LeanObject,
    mut v_00_u03b2_4483_: *mut leanh::LeanObject,
    mut v_cmp_4484_: *mut leanh::LeanObject,
    mut v_inst_4485_: *mut leanh::LeanObject,
    mut v_t_4486_: *mut leanh::LeanObject,
    mut v_h_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_4486_);
    return v___x_4488_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry___boxed(
    mut v_00_u03b1_4489_: *mut leanh::LeanObject,
    mut v_00_u03b2_4490_: *mut leanh::LeanObject,
    mut v_cmp_4491_: *mut leanh::LeanObject,
    mut v_inst_4492_: *mut leanh::LeanObject,
    mut v_t_4493_: *mut leanh::LeanObject,
    mut v_h_4494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4495_ = l_Std_ExtDTreeMap_maxEntry(
        v_00_u03b1_4489_,
        v_00_u03b2_4490_,
        v_cmp_4491_,
        v_inst_4492_,
        v_t_4493_,
        v_h_4494_,
    );
    leanh::lean_dec(v_t_4493_);
    leanh::lean_dec_ref(v_cmp_4491_);
    return v_res_4495_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x21___redArg(
    mut v_inst_4496_: *mut leanh::LeanObject,
    mut v_t_4497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4498_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_4496_, v_t_4497_);
    return v___x_4498_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x21___redArg___boxed(
    mut v_inst_4499_: *mut leanh::LeanObject,
    mut v_t_4500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4501_ = l_Std_ExtDTreeMap_maxEntry_x21___redArg(v_inst_4499_, v_t_4500_);
    leanh::lean_dec(v_t_4500_);
    leanh::lean_dec_ref(v_inst_4499_);
    return v_res_4501_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x21(
    mut v_00_u03b1_4502_: *mut leanh::LeanObject,
    mut v_00_u03b2_4503_: *mut leanh::LeanObject,
    mut v_cmp_4504_: *mut leanh::LeanObject,
    mut v_inst_4505_: *mut leanh::LeanObject,
    mut v_inst_4506_: *mut leanh::LeanObject,
    mut v_t_4507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4508_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_4506_, v_t_4507_);
    return v___x_4508_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntry_x21___boxed(
    mut v_00_u03b1_4509_: *mut leanh::LeanObject,
    mut v_00_u03b2_4510_: *mut leanh::LeanObject,
    mut v_cmp_4511_: *mut leanh::LeanObject,
    mut v_inst_4512_: *mut leanh::LeanObject,
    mut v_inst_4513_: *mut leanh::LeanObject,
    mut v_t_4514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4515_ = l_Std_ExtDTreeMap_maxEntry_x21(
        v_00_u03b1_4509_,
        v_00_u03b2_4510_,
        v_cmp_4511_,
        v_inst_4512_,
        v_inst_4513_,
        v_t_4514_,
    );
    leanh::lean_dec(v_t_4514_);
    leanh::lean_dec_ref(v_inst_4513_);
    leanh::lean_dec_ref(v_cmp_4511_);
    return v_res_4515_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntryD___redArg(
    mut v_t_4516_: *mut leanh::LeanObject,
    mut v_fallback_4517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4518_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_4516_, v_fallback_4517_);
    return v___x_4518_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntryD___redArg___boxed(
    mut v_t_4519_: *mut leanh::LeanObject,
    mut v_fallback_4520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4521_ = l_Std_ExtDTreeMap_maxEntryD___redArg(v_t_4519_, v_fallback_4520_);
    leanh::lean_dec_ref(v_fallback_4520_);
    leanh::lean_dec(v_t_4519_);
    return v_res_4521_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntryD(
    mut v_00_u03b1_4522_: *mut leanh::LeanObject,
    mut v_00_u03b2_4523_: *mut leanh::LeanObject,
    mut v_cmp_4524_: *mut leanh::LeanObject,
    mut v_inst_4525_: *mut leanh::LeanObject,
    mut v_t_4526_: *mut leanh::LeanObject,
    mut v_fallback_4527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4528_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_4526_, v_fallback_4527_);
    return v___x_4528_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxEntryD___boxed(
    mut v_00_u03b1_4529_: *mut leanh::LeanObject,
    mut v_00_u03b2_4530_: *mut leanh::LeanObject,
    mut v_cmp_4531_: *mut leanh::LeanObject,
    mut v_inst_4532_: *mut leanh::LeanObject,
    mut v_t_4533_: *mut leanh::LeanObject,
    mut v_fallback_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4535_ = l_Std_ExtDTreeMap_maxEntryD(
        v_00_u03b1_4529_,
        v_00_u03b2_4530_,
        v_cmp_4531_,
        v_inst_4532_,
        v_t_4533_,
        v_fallback_4534_,
    );
    leanh::lean_dec_ref(v_fallback_4534_);
    leanh::lean_dec(v_t_4533_);
    leanh::lean_dec_ref(v_cmp_4531_);
    return v_res_4535_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x3f___redArg(
    mut v_t_4536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4537_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_4536_);
    return v___x_4537_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x3f___redArg___boxed(
    mut v_t_4538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4539_ = l_Std_ExtDTreeMap_minKey_x3f___redArg(v_t_4538_);
    leanh::lean_dec(v_t_4538_);
    return v_res_4539_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x3f(
    mut v_00_u03b1_4540_: *mut leanh::LeanObject,
    mut v_00_u03b2_4541_: *mut leanh::LeanObject,
    mut v_cmp_4542_: *mut leanh::LeanObject,
    mut v_inst_4543_: *mut leanh::LeanObject,
    mut v_t_4544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4545_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_4544_);
    return v___x_4545_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x3f___boxed(
    mut v_00_u03b1_4546_: *mut leanh::LeanObject,
    mut v_00_u03b2_4547_: *mut leanh::LeanObject,
    mut v_cmp_4548_: *mut leanh::LeanObject,
    mut v_inst_4549_: *mut leanh::LeanObject,
    mut v_t_4550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4551_ = l_Std_ExtDTreeMap_minKey_x3f(
        v_00_u03b1_4546_,
        v_00_u03b2_4547_,
        v_cmp_4548_,
        v_inst_4549_,
        v_t_4550_,
    );
    leanh::lean_dec(v_t_4550_);
    leanh::lean_dec_ref(v_cmp_4548_);
    return v_res_4551_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey___redArg(
    mut v_t_4552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_4552_);
    return v___x_4553_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey___redArg___boxed(
    mut v_t_4554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4555_ = l_Std_ExtDTreeMap_minKey___redArg(v_t_4554_);
    leanh::lean_dec(v_t_4554_);
    return v_res_4555_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey(
    mut v_00_u03b1_4556_: *mut leanh::LeanObject,
    mut v_00_u03b2_4557_: *mut leanh::LeanObject,
    mut v_cmp_4558_: *mut leanh::LeanObject,
    mut v_inst_4559_: *mut leanh::LeanObject,
    mut v_t_4560_: *mut leanh::LeanObject,
    mut v_h_4561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4562_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_4560_);
    return v___x_4562_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey___boxed(
    mut v_00_u03b1_4563_: *mut leanh::LeanObject,
    mut v_00_u03b2_4564_: *mut leanh::LeanObject,
    mut v_cmp_4565_: *mut leanh::LeanObject,
    mut v_inst_4566_: *mut leanh::LeanObject,
    mut v_t_4567_: *mut leanh::LeanObject,
    mut v_h_4568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4569_ = l_Std_ExtDTreeMap_minKey(
        v_00_u03b1_4563_,
        v_00_u03b2_4564_,
        v_cmp_4565_,
        v_inst_4566_,
        v_t_4567_,
        v_h_4568_,
    );
    leanh::lean_dec(v_t_4567_);
    leanh::lean_dec_ref(v_cmp_4565_);
    return v_res_4569_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x21___redArg(
    mut v_inst_4570_: *mut leanh::LeanObject,
    mut v_t_4571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4572_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_4570_, v_t_4571_);
    return v___x_4572_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x21___redArg___boxed(
    mut v_inst_4573_: *mut leanh::LeanObject,
    mut v_t_4574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4575_ = l_Std_ExtDTreeMap_minKey_x21___redArg(v_inst_4573_, v_t_4574_);
    leanh::lean_dec(v_t_4574_);
    leanh::lean_dec(v_inst_4573_);
    return v_res_4575_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x21(
    mut v_00_u03b1_4576_: *mut leanh::LeanObject,
    mut v_00_u03b2_4577_: *mut leanh::LeanObject,
    mut v_cmp_4578_: *mut leanh::LeanObject,
    mut v_inst_4579_: *mut leanh::LeanObject,
    mut v_inst_4580_: *mut leanh::LeanObject,
    mut v_t_4581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_4580_, v_t_4581_);
    return v___x_4582_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKey_x21___boxed(
    mut v_00_u03b1_4583_: *mut leanh::LeanObject,
    mut v_00_u03b2_4584_: *mut leanh::LeanObject,
    mut v_cmp_4585_: *mut leanh::LeanObject,
    mut v_inst_4586_: *mut leanh::LeanObject,
    mut v_inst_4587_: *mut leanh::LeanObject,
    mut v_t_4588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4589_ = l_Std_ExtDTreeMap_minKey_x21(
        v_00_u03b1_4583_,
        v_00_u03b2_4584_,
        v_cmp_4585_,
        v_inst_4586_,
        v_inst_4587_,
        v_t_4588_,
    );
    leanh::lean_dec(v_t_4588_);
    leanh::lean_dec(v_inst_4587_);
    leanh::lean_dec_ref(v_cmp_4585_);
    return v_res_4589_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKeyD___redArg(
    mut v_t_4590_: *mut leanh::LeanObject,
    mut v_fallback_4591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_4590_, v_fallback_4591_);
    return v___x_4592_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKeyD___redArg___boxed(
    mut v_t_4593_: *mut leanh::LeanObject,
    mut v_fallback_4594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4595_ = l_Std_ExtDTreeMap_minKeyD___redArg(v_t_4593_, v_fallback_4594_);
    leanh::lean_dec(v_fallback_4594_);
    leanh::lean_dec(v_t_4593_);
    return v_res_4595_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKeyD(
    mut v_00_u03b1_4596_: *mut leanh::LeanObject,
    mut v_00_u03b2_4597_: *mut leanh::LeanObject,
    mut v_cmp_4598_: *mut leanh::LeanObject,
    mut v_inst_4599_: *mut leanh::LeanObject,
    mut v_t_4600_: *mut leanh::LeanObject,
    mut v_fallback_4601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4602_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_4600_, v_fallback_4601_);
    return v___x_4602_;
}
pub unsafe fn l_Std_ExtDTreeMap_minKeyD___boxed(
    mut v_00_u03b1_4603_: *mut leanh::LeanObject,
    mut v_00_u03b2_4604_: *mut leanh::LeanObject,
    mut v_cmp_4605_: *mut leanh::LeanObject,
    mut v_inst_4606_: *mut leanh::LeanObject,
    mut v_t_4607_: *mut leanh::LeanObject,
    mut v_fallback_4608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4609_ = l_Std_ExtDTreeMap_minKeyD(
        v_00_u03b1_4603_,
        v_00_u03b2_4604_,
        v_cmp_4605_,
        v_inst_4606_,
        v_t_4607_,
        v_fallback_4608_,
    );
    leanh::lean_dec(v_fallback_4608_);
    leanh::lean_dec(v_t_4607_);
    leanh::lean_dec_ref(v_cmp_4605_);
    return v_res_4609_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x3f___redArg(
    mut v_t_4610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4611_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_4610_);
    return v___x_4611_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x3f___redArg___boxed(
    mut v_t_4612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4613_ = l_Std_ExtDTreeMap_maxKey_x3f___redArg(v_t_4612_);
    leanh::lean_dec(v_t_4612_);
    return v_res_4613_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x3f(
    mut v_00_u03b1_4614_: *mut leanh::LeanObject,
    mut v_00_u03b2_4615_: *mut leanh::LeanObject,
    mut v_cmp_4616_: *mut leanh::LeanObject,
    mut v_inst_4617_: *mut leanh::LeanObject,
    mut v_t_4618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4619_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_4618_);
    return v___x_4619_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x3f___boxed(
    mut v_00_u03b1_4620_: *mut leanh::LeanObject,
    mut v_00_u03b2_4621_: *mut leanh::LeanObject,
    mut v_cmp_4622_: *mut leanh::LeanObject,
    mut v_inst_4623_: *mut leanh::LeanObject,
    mut v_t_4624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4625_ = l_Std_ExtDTreeMap_maxKey_x3f(
        v_00_u03b1_4620_,
        v_00_u03b2_4621_,
        v_cmp_4622_,
        v_inst_4623_,
        v_t_4624_,
    );
    leanh::lean_dec(v_t_4624_);
    leanh::lean_dec_ref(v_cmp_4622_);
    return v_res_4625_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey___redArg(
    mut v_t_4626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_4626_);
    return v___x_4627_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey___redArg___boxed(
    mut v_t_4628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4629_ = l_Std_ExtDTreeMap_maxKey___redArg(v_t_4628_);
    leanh::lean_dec(v_t_4628_);
    return v_res_4629_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey(
    mut v_00_u03b1_4630_: *mut leanh::LeanObject,
    mut v_00_u03b2_4631_: *mut leanh::LeanObject,
    mut v_cmp_4632_: *mut leanh::LeanObject,
    mut v_inst_4633_: *mut leanh::LeanObject,
    mut v_t_4634_: *mut leanh::LeanObject,
    mut v_h_4635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_4634_);
    return v___x_4636_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey___boxed(
    mut v_00_u03b1_4637_: *mut leanh::LeanObject,
    mut v_00_u03b2_4638_: *mut leanh::LeanObject,
    mut v_cmp_4639_: *mut leanh::LeanObject,
    mut v_inst_4640_: *mut leanh::LeanObject,
    mut v_t_4641_: *mut leanh::LeanObject,
    mut v_h_4642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4643_ = l_Std_ExtDTreeMap_maxKey(
        v_00_u03b1_4637_,
        v_00_u03b2_4638_,
        v_cmp_4639_,
        v_inst_4640_,
        v_t_4641_,
        v_h_4642_,
    );
    leanh::lean_dec(v_t_4641_);
    leanh::lean_dec_ref(v_cmp_4639_);
    return v_res_4643_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x21___redArg(
    mut v_inst_4644_: *mut leanh::LeanObject,
    mut v_t_4645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4646_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_4644_, v_t_4645_);
    return v___x_4646_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x21___redArg___boxed(
    mut v_inst_4647_: *mut leanh::LeanObject,
    mut v_t_4648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4649_ = l_Std_ExtDTreeMap_maxKey_x21___redArg(v_inst_4647_, v_t_4648_);
    leanh::lean_dec(v_t_4648_);
    leanh::lean_dec(v_inst_4647_);
    return v_res_4649_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x21(
    mut v_00_u03b1_4650_: *mut leanh::LeanObject,
    mut v_00_u03b2_4651_: *mut leanh::LeanObject,
    mut v_cmp_4652_: *mut leanh::LeanObject,
    mut v_inst_4653_: *mut leanh::LeanObject,
    mut v_inst_4654_: *mut leanh::LeanObject,
    mut v_t_4655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4656_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_4654_, v_t_4655_);
    return v___x_4656_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKey_x21___boxed(
    mut v_00_u03b1_4657_: *mut leanh::LeanObject,
    mut v_00_u03b2_4658_: *mut leanh::LeanObject,
    mut v_cmp_4659_: *mut leanh::LeanObject,
    mut v_inst_4660_: *mut leanh::LeanObject,
    mut v_inst_4661_: *mut leanh::LeanObject,
    mut v_t_4662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4663_ = l_Std_ExtDTreeMap_maxKey_x21(
        v_00_u03b1_4657_,
        v_00_u03b2_4658_,
        v_cmp_4659_,
        v_inst_4660_,
        v_inst_4661_,
        v_t_4662_,
    );
    leanh::lean_dec(v_t_4662_);
    leanh::lean_dec(v_inst_4661_);
    leanh::lean_dec_ref(v_cmp_4659_);
    return v_res_4663_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKeyD___redArg(
    mut v_t_4664_: *mut leanh::LeanObject,
    mut v_fallback_4665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4666_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_4664_, v_fallback_4665_);
    return v___x_4666_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKeyD___redArg___boxed(
    mut v_t_4667_: *mut leanh::LeanObject,
    mut v_fallback_4668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4669_ = l_Std_ExtDTreeMap_maxKeyD___redArg(v_t_4667_, v_fallback_4668_);
    leanh::lean_dec(v_fallback_4668_);
    leanh::lean_dec(v_t_4667_);
    return v_res_4669_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKeyD(
    mut v_00_u03b1_4670_: *mut leanh::LeanObject,
    mut v_00_u03b2_4671_: *mut leanh::LeanObject,
    mut v_cmp_4672_: *mut leanh::LeanObject,
    mut v_inst_4673_: *mut leanh::LeanObject,
    mut v_t_4674_: *mut leanh::LeanObject,
    mut v_fallback_4675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4676_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_4674_, v_fallback_4675_);
    return v___x_4676_;
}
pub unsafe fn l_Std_ExtDTreeMap_maxKeyD___boxed(
    mut v_00_u03b1_4677_: *mut leanh::LeanObject,
    mut v_00_u03b2_4678_: *mut leanh::LeanObject,
    mut v_cmp_4679_: *mut leanh::LeanObject,
    mut v_inst_4680_: *mut leanh::LeanObject,
    mut v_t_4681_: *mut leanh::LeanObject,
    mut v_fallback_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4683_ = l_Std_ExtDTreeMap_maxKeyD(
        v_00_u03b1_4677_,
        v_00_u03b2_4678_,
        v_cmp_4679_,
        v_inst_4680_,
        v_t_4681_,
        v_fallback_4682_,
    );
    leanh::lean_dec(v_fallback_4682_);
    leanh::lean_dec(v_t_4681_);
    leanh::lean_dec_ref(v_cmp_4679_);
    return v_res_4683_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(
    mut v_t_4684_: *mut leanh::LeanObject,
    mut v_n_4685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4686_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_4684_, v_n_4685_);
    return v___x_4686_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg___boxed(
    mut v_t_4687_: *mut leanh::LeanObject,
    mut v_n_4688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4689_ = l_Std_ExtDTreeMap_entryAtIdx_x3f___redArg(v_t_4687_, v_n_4688_);
    leanh::lean_dec(v_t_4687_);
    return v_res_4689_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x3f(
    mut v_00_u03b1_4690_: *mut leanh::LeanObject,
    mut v_00_u03b2_4691_: *mut leanh::LeanObject,
    mut v_cmp_4692_: *mut leanh::LeanObject,
    mut v_inst_4693_: *mut leanh::LeanObject,
    mut v_t_4694_: *mut leanh::LeanObject,
    mut v_n_4695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4696_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_4694_, v_n_4695_);
    return v___x_4696_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_4697_: *mut leanh::LeanObject,
    mut v_00_u03b2_4698_: *mut leanh::LeanObject,
    mut v_cmp_4699_: *mut leanh::LeanObject,
    mut v_inst_4700_: *mut leanh::LeanObject,
    mut v_t_4701_: *mut leanh::LeanObject,
    mut v_n_4702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4703_ = l_Std_ExtDTreeMap_entryAtIdx_x3f(
        v_00_u03b1_4697_,
        v_00_u03b2_4698_,
        v_cmp_4699_,
        v_inst_4700_,
        v_t_4701_,
        v_n_4702_,
    );
    leanh::lean_dec(v_t_4701_);
    leanh::lean_dec_ref(v_cmp_4699_);
    return v_res_4703_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx___redArg(
    mut v_t_4704_: *mut leanh::LeanObject,
    mut v_n_4705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4706_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_4704_, v_n_4705_);
    return v___x_4706_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx___redArg___boxed(
    mut v_t_4707_: *mut leanh::LeanObject,
    mut v_n_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4709_ = l_Std_ExtDTreeMap_entryAtIdx___redArg(v_t_4707_, v_n_4708_);
    leanh::lean_dec(v_t_4707_);
    return v_res_4709_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx(
    mut v_00_u03b1_4710_: *mut leanh::LeanObject,
    mut v_00_u03b2_4711_: *mut leanh::LeanObject,
    mut v_cmp_4712_: *mut leanh::LeanObject,
    mut v_inst_4713_: *mut leanh::LeanObject,
    mut v_t_4714_: *mut leanh::LeanObject,
    mut v_n_4715_: *mut leanh::LeanObject,
    mut v_h_4716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4717_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_4714_, v_n_4715_);
    return v___x_4717_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx___boxed(
    mut v_00_u03b1_4718_: *mut leanh::LeanObject,
    mut v_00_u03b2_4719_: *mut leanh::LeanObject,
    mut v_cmp_4720_: *mut leanh::LeanObject,
    mut v_inst_4721_: *mut leanh::LeanObject,
    mut v_t_4722_: *mut leanh::LeanObject,
    mut v_n_4723_: *mut leanh::LeanObject,
    mut v_h_4724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4725_ = l_Std_ExtDTreeMap_entryAtIdx(
        v_00_u03b1_4718_,
        v_00_u03b2_4719_,
        v_cmp_4720_,
        v_inst_4721_,
        v_t_4722_,
        v_n_4723_,
        v_h_4724_,
    );
    leanh::lean_dec(v_t_4722_);
    leanh::lean_dec_ref(v_cmp_4720_);
    return v_res_4725_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(
    mut v_inst_4726_: *mut leanh::LeanObject,
    mut v_t_4727_: *mut leanh::LeanObject,
    mut v_n_4728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4729_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_4726_, v_t_4727_, v_n_4728_);
    return v___x_4729_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x21___redArg___boxed(
    mut v_inst_4730_: *mut leanh::LeanObject,
    mut v_t_4731_: *mut leanh::LeanObject,
    mut v_n_4732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4733_ = l_Std_ExtDTreeMap_entryAtIdx_x21___redArg(v_inst_4730_, v_t_4731_, v_n_4732_);
    leanh::lean_dec(v_t_4731_);
    leanh::lean_dec_ref(v_inst_4730_);
    return v_res_4733_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x21(
    mut v_00_u03b1_4734_: *mut leanh::LeanObject,
    mut v_00_u03b2_4735_: *mut leanh::LeanObject,
    mut v_cmp_4736_: *mut leanh::LeanObject,
    mut v_inst_4737_: *mut leanh::LeanObject,
    mut v_inst_4738_: *mut leanh::LeanObject,
    mut v_t_4739_: *mut leanh::LeanObject,
    mut v_n_4740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4741_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_4738_, v_t_4739_, v_n_4740_);
    return v___x_4741_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdx_x21___boxed(
    mut v_00_u03b1_4742_: *mut leanh::LeanObject,
    mut v_00_u03b2_4743_: *mut leanh::LeanObject,
    mut v_cmp_4744_: *mut leanh::LeanObject,
    mut v_inst_4745_: *mut leanh::LeanObject,
    mut v_inst_4746_: *mut leanh::LeanObject,
    mut v_t_4747_: *mut leanh::LeanObject,
    mut v_n_4748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4749_ = l_Std_ExtDTreeMap_entryAtIdx_x21(
        v_00_u03b1_4742_,
        v_00_u03b2_4743_,
        v_cmp_4744_,
        v_inst_4745_,
        v_inst_4746_,
        v_t_4747_,
        v_n_4748_,
    );
    leanh::lean_dec(v_t_4747_);
    leanh::lean_dec_ref(v_inst_4746_);
    leanh::lean_dec_ref(v_cmp_4744_);
    return v_res_4749_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdxD___redArg(
    mut v_t_4750_: *mut leanh::LeanObject,
    mut v_n_4751_: *mut leanh::LeanObject,
    mut v_fallback_4752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4753_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_4750_, v_n_4751_, v_fallback_4752_);
    return v___x_4753_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdxD___redArg___boxed(
    mut v_t_4754_: *mut leanh::LeanObject,
    mut v_n_4755_: *mut leanh::LeanObject,
    mut v_fallback_4756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4757_ = l_Std_ExtDTreeMap_entryAtIdxD___redArg(v_t_4754_, v_n_4755_, v_fallback_4756_);
    leanh::lean_dec_ref(v_fallback_4756_);
    leanh::lean_dec(v_t_4754_);
    return v_res_4757_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdxD(
    mut v_00_u03b1_4758_: *mut leanh::LeanObject,
    mut v_00_u03b2_4759_: *mut leanh::LeanObject,
    mut v_cmp_4760_: *mut leanh::LeanObject,
    mut v_inst_4761_: *mut leanh::LeanObject,
    mut v_t_4762_: *mut leanh::LeanObject,
    mut v_n_4763_: *mut leanh::LeanObject,
    mut v_fallback_4764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4765_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_4762_, v_n_4763_, v_fallback_4764_);
    return v___x_4765_;
}
pub unsafe fn l_Std_ExtDTreeMap_entryAtIdxD___boxed(
    mut v_00_u03b1_4766_: *mut leanh::LeanObject,
    mut v_00_u03b2_4767_: *mut leanh::LeanObject,
    mut v_cmp_4768_: *mut leanh::LeanObject,
    mut v_inst_4769_: *mut leanh::LeanObject,
    mut v_t_4770_: *mut leanh::LeanObject,
    mut v_n_4771_: *mut leanh::LeanObject,
    mut v_fallback_4772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Std_ExtDTreeMap_entryAtIdxD(
        v_00_u03b1_4766_,
        v_00_u03b2_4767_,
        v_cmp_4768_,
        v_inst_4769_,
        v_t_4770_,
        v_n_4771_,
        v_fallback_4772_,
    );
    leanh::lean_dec_ref(v_fallback_4772_);
    leanh::lean_dec(v_t_4770_);
    leanh::lean_dec_ref(v_cmp_4768_);
    return v_res_4773_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(
    mut v_t_4774_: *mut leanh::LeanObject,
    mut v_n_4775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_4774_, v_n_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg___boxed(
    mut v_t_4777_: *mut leanh::LeanObject,
    mut v_n_4778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4779_ = l_Std_ExtDTreeMap_keyAtIdx_x3f___redArg(v_t_4777_, v_n_4778_);
    leanh::lean_dec(v_t_4777_);
    return v_res_4779_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x3f(
    mut v_00_u03b1_4780_: *mut leanh::LeanObject,
    mut v_00_u03b2_4781_: *mut leanh::LeanObject,
    mut v_cmp_4782_: *mut leanh::LeanObject,
    mut v_inst_4783_: *mut leanh::LeanObject,
    mut v_t_4784_: *mut leanh::LeanObject,
    mut v_n_4785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4786_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_4784_, v_n_4785_);
    return v___x_4786_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x3f___boxed(
    mut v_00_u03b1_4787_: *mut leanh::LeanObject,
    mut v_00_u03b2_4788_: *mut leanh::LeanObject,
    mut v_cmp_4789_: *mut leanh::LeanObject,
    mut v_inst_4790_: *mut leanh::LeanObject,
    mut v_t_4791_: *mut leanh::LeanObject,
    mut v_n_4792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4793_ = l_Std_ExtDTreeMap_keyAtIdx_x3f(
        v_00_u03b1_4787_,
        v_00_u03b2_4788_,
        v_cmp_4789_,
        v_inst_4790_,
        v_t_4791_,
        v_n_4792_,
    );
    leanh::lean_dec(v_t_4791_);
    leanh::lean_dec_ref(v_cmp_4789_);
    return v_res_4793_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx___redArg(
    mut v_t_4794_: *mut leanh::LeanObject,
    mut v_n_4795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_4794_, v_n_4795_);
    return v___x_4796_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx___redArg___boxed(
    mut v_t_4797_: *mut leanh::LeanObject,
    mut v_n_4798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4799_ = l_Std_ExtDTreeMap_keyAtIdx___redArg(v_t_4797_, v_n_4798_);
    leanh::lean_dec(v_t_4797_);
    return v_res_4799_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx(
    mut v_00_u03b1_4800_: *mut leanh::LeanObject,
    mut v_00_u03b2_4801_: *mut leanh::LeanObject,
    mut v_cmp_4802_: *mut leanh::LeanObject,
    mut v_inst_4803_: *mut leanh::LeanObject,
    mut v_t_4804_: *mut leanh::LeanObject,
    mut v_n_4805_: *mut leanh::LeanObject,
    mut v_h_4806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4807_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_4804_, v_n_4805_);
    return v___x_4807_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx___boxed(
    mut v_00_u03b1_4808_: *mut leanh::LeanObject,
    mut v_00_u03b2_4809_: *mut leanh::LeanObject,
    mut v_cmp_4810_: *mut leanh::LeanObject,
    mut v_inst_4811_: *mut leanh::LeanObject,
    mut v_t_4812_: *mut leanh::LeanObject,
    mut v_n_4813_: *mut leanh::LeanObject,
    mut v_h_4814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4815_ = l_Std_ExtDTreeMap_keyAtIdx(
        v_00_u03b1_4808_,
        v_00_u03b2_4809_,
        v_cmp_4810_,
        v_inst_4811_,
        v_t_4812_,
        v_n_4813_,
        v_h_4814_,
    );
    leanh::lean_dec(v_t_4812_);
    leanh::lean_dec_ref(v_cmp_4810_);
    return v_res_4815_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(
    mut v_inst_4816_: *mut leanh::LeanObject,
    mut v_t_4817_: *mut leanh::LeanObject,
    mut v_n_4818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4819_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_4816_, v_t_4817_, v_n_4818_);
    return v___x_4819_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x21___redArg___boxed(
    mut v_inst_4820_: *mut leanh::LeanObject,
    mut v_t_4821_: *mut leanh::LeanObject,
    mut v_n_4822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4823_ = l_Std_ExtDTreeMap_keyAtIdx_x21___redArg(v_inst_4820_, v_t_4821_, v_n_4822_);
    leanh::lean_dec(v_t_4821_);
    leanh::lean_dec(v_inst_4820_);
    return v_res_4823_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x21(
    mut v_00_u03b1_4824_: *mut leanh::LeanObject,
    mut v_00_u03b2_4825_: *mut leanh::LeanObject,
    mut v_cmp_4826_: *mut leanh::LeanObject,
    mut v_inst_4827_: *mut leanh::LeanObject,
    mut v_inst_4828_: *mut leanh::LeanObject,
    mut v_t_4829_: *mut leanh::LeanObject,
    mut v_n_4830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_4828_, v_t_4829_, v_n_4830_);
    return v___x_4831_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdx_x21___boxed(
    mut v_00_u03b1_4832_: *mut leanh::LeanObject,
    mut v_00_u03b2_4833_: *mut leanh::LeanObject,
    mut v_cmp_4834_: *mut leanh::LeanObject,
    mut v_inst_4835_: *mut leanh::LeanObject,
    mut v_inst_4836_: *mut leanh::LeanObject,
    mut v_t_4837_: *mut leanh::LeanObject,
    mut v_n_4838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4839_ = l_Std_ExtDTreeMap_keyAtIdx_x21(
        v_00_u03b1_4832_,
        v_00_u03b2_4833_,
        v_cmp_4834_,
        v_inst_4835_,
        v_inst_4836_,
        v_t_4837_,
        v_n_4838_,
    );
    leanh::lean_dec(v_t_4837_);
    leanh::lean_dec(v_inst_4836_);
    leanh::lean_dec_ref(v_cmp_4834_);
    return v_res_4839_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdxD___redArg(
    mut v_t_4840_: *mut leanh::LeanObject,
    mut v_n_4841_: *mut leanh::LeanObject,
    mut v_fallback_4842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4843_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_4840_, v_n_4841_, v_fallback_4842_);
    return v___x_4843_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdxD___redArg___boxed(
    mut v_t_4844_: *mut leanh::LeanObject,
    mut v_n_4845_: *mut leanh::LeanObject,
    mut v_fallback_4846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Std_ExtDTreeMap_keyAtIdxD___redArg(v_t_4844_, v_n_4845_, v_fallback_4846_);
    leanh::lean_dec(v_fallback_4846_);
    leanh::lean_dec(v_t_4844_);
    return v_res_4847_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdxD(
    mut v_00_u03b1_4848_: *mut leanh::LeanObject,
    mut v_00_u03b2_4849_: *mut leanh::LeanObject,
    mut v_cmp_4850_: *mut leanh::LeanObject,
    mut v_inst_4851_: *mut leanh::LeanObject,
    mut v_t_4852_: *mut leanh::LeanObject,
    mut v_n_4853_: *mut leanh::LeanObject,
    mut v_fallback_4854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4855_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_4852_, v_n_4853_, v_fallback_4854_);
    return v___x_4855_;
}
pub unsafe fn l_Std_ExtDTreeMap_keyAtIdxD___boxed(
    mut v_00_u03b1_4856_: *mut leanh::LeanObject,
    mut v_00_u03b2_4857_: *mut leanh::LeanObject,
    mut v_cmp_4858_: *mut leanh::LeanObject,
    mut v_inst_4859_: *mut leanh::LeanObject,
    mut v_t_4860_: *mut leanh::LeanObject,
    mut v_n_4861_: *mut leanh::LeanObject,
    mut v_fallback_4862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4863_ = l_Std_ExtDTreeMap_keyAtIdxD(
        v_00_u03b1_4856_,
        v_00_u03b2_4857_,
        v_cmp_4858_,
        v_inst_4859_,
        v_t_4860_,
        v_n_4861_,
        v_fallback_4862_,
    );
    leanh::lean_dec(v_fallback_4862_);
    leanh::lean_dec(v_t_4860_);
    leanh::lean_dec_ref(v_cmp_4858_);
    return v_res_4863_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE_x3f___redArg(
    mut v_cmp_4864_: *mut leanh::LeanObject,
    mut v_t_4865_: *mut leanh::LeanObject,
    mut v_k_4866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = leanh::lean_box(0);
    v___x_4868_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_4864_,
        v_k_4866_,
        v___x_4867_,
        v_t_4865_,
    );
    return v___x_4868_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE_x3f(
    mut v_00_u03b1_4869_: *mut leanh::LeanObject,
    mut v_00_u03b2_4870_: *mut leanh::LeanObject,
    mut v_cmp_4871_: *mut leanh::LeanObject,
    mut v_inst_4872_: *mut leanh::LeanObject,
    mut v_t_4873_: *mut leanh::LeanObject,
    mut v_k_4874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4875_ = leanh::lean_box(0);
    v___x_4876_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_4871_,
        v_k_4874_,
        v___x_4875_,
        v_t_4873_,
    );
    return v___x_4876_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT_x3f___redArg(
    mut v_cmp_4877_: *mut leanh::LeanObject,
    mut v_t_4878_: *mut leanh::LeanObject,
    mut v_k_4879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4880_ = leanh::lean_box(0);
    v___x_4881_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_4877_,
        v_k_4879_,
        v___x_4880_,
        v_t_4878_,
    );
    return v___x_4881_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT_x3f(
    mut v_00_u03b1_4882_: *mut leanh::LeanObject,
    mut v_00_u03b2_4883_: *mut leanh::LeanObject,
    mut v_cmp_4884_: *mut leanh::LeanObject,
    mut v_inst_4885_: *mut leanh::LeanObject,
    mut v_t_4886_: *mut leanh::LeanObject,
    mut v_k_4887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4888_ = leanh::lean_box(0);
    v___x_4889_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_4884_,
        v_k_4887_,
        v___x_4888_,
        v_t_4886_,
    );
    return v___x_4889_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE_x3f___redArg(
    mut v_cmp_4890_: *mut leanh::LeanObject,
    mut v_t_4891_: *mut leanh::LeanObject,
    mut v_k_4892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4893_ = leanh::lean_box(0);
    v___x_4894_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_4890_,
        v_k_4892_,
        v___x_4893_,
        v_t_4891_,
    );
    return v___x_4894_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE_x3f(
    mut v_00_u03b1_4895_: *mut leanh::LeanObject,
    mut v_00_u03b2_4896_: *mut leanh::LeanObject,
    mut v_cmp_4897_: *mut leanh::LeanObject,
    mut v_inst_4898_: *mut leanh::LeanObject,
    mut v_t_4899_: *mut leanh::LeanObject,
    mut v_k_4900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = leanh::lean_box(0);
    v___x_4902_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_4897_,
        v_k_4900_,
        v___x_4901_,
        v_t_4899_,
    );
    return v___x_4902_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT_x3f___redArg(
    mut v_cmp_4903_: *mut leanh::LeanObject,
    mut v_t_4904_: *mut leanh::LeanObject,
    mut v_k_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4906_ = leanh::lean_box(0);
    v___x_4907_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_4903_,
        v_k_4905_,
        v___x_4906_,
        v_t_4904_,
    );
    return v___x_4907_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT_x3f(
    mut v_00_u03b1_4908_: *mut leanh::LeanObject,
    mut v_00_u03b2_4909_: *mut leanh::LeanObject,
    mut v_cmp_4910_: *mut leanh::LeanObject,
    mut v_inst_4911_: *mut leanh::LeanObject,
    mut v_t_4912_: *mut leanh::LeanObject,
    mut v_k_4913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4914_ = leanh::lean_box(0);
    v___x_4915_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_4910_,
        v_k_4913_,
        v___x_4914_,
        v_t_4912_,
    );
    return v___x_4915_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE___redArg(
    mut v_cmp_4916_: *mut leanh::LeanObject,
    mut v_t_4917_: *mut leanh::LeanObject,
    mut v_k_4918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4919_ =
        l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_4916_, v_k_4918_, v_t_4917_);
    return v___x_4919_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE(
    mut v_00_u03b1_4920_: *mut leanh::LeanObject,
    mut v_00_u03b2_4921_: *mut leanh::LeanObject,
    mut v_cmp_4922_: *mut leanh::LeanObject,
    mut v_inst_4923_: *mut leanh::LeanObject,
    mut v_t_4924_: *mut leanh::LeanObject,
    mut v_k_4925_: *mut leanh::LeanObject,
    mut v_h_4926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4927_ =
        l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_4922_, v_k_4925_, v_t_4924_);
    return v___x_4927_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT___redArg(
    mut v_cmp_4928_: *mut leanh::LeanObject,
    mut v_t_4929_: *mut leanh::LeanObject,
    mut v_k_4930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4931_ =
        l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_4928_, v_k_4930_, v_t_4929_);
    return v___x_4931_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT(
    mut v_00_u03b1_4932_: *mut leanh::LeanObject,
    mut v_00_u03b2_4933_: *mut leanh::LeanObject,
    mut v_cmp_4934_: *mut leanh::LeanObject,
    mut v_inst_4935_: *mut leanh::LeanObject,
    mut v_t_4936_: *mut leanh::LeanObject,
    mut v_k_4937_: *mut leanh::LeanObject,
    mut v_h_4938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ =
        l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_4934_, v_k_4937_, v_t_4936_);
    return v___x_4939_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE___redArg(
    mut v_cmp_4940_: *mut leanh::LeanObject,
    mut v_t_4941_: *mut leanh::LeanObject,
    mut v_k_4942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4943_ =
        l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_4940_, v_k_4942_, v_t_4941_);
    return v___x_4943_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE(
    mut v_00_u03b1_4944_: *mut leanh::LeanObject,
    mut v_00_u03b2_4945_: *mut leanh::LeanObject,
    mut v_cmp_4946_: *mut leanh::LeanObject,
    mut v_inst_4947_: *mut leanh::LeanObject,
    mut v_t_4948_: *mut leanh::LeanObject,
    mut v_k_4949_: *mut leanh::LeanObject,
    mut v_h_4950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4951_ =
        l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_4946_, v_k_4949_, v_t_4948_);
    return v___x_4951_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT___redArg(
    mut v_cmp_4952_: *mut leanh::LeanObject,
    mut v_t_4953_: *mut leanh::LeanObject,
    mut v_k_4954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4955_ =
        l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_4952_, v_k_4954_, v_t_4953_);
    return v___x_4955_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT(
    mut v_00_u03b1_4956_: *mut leanh::LeanObject,
    mut v_00_u03b2_4957_: *mut leanh::LeanObject,
    mut v_cmp_4958_: *mut leanh::LeanObject,
    mut v_inst_4959_: *mut leanh::LeanObject,
    mut v_t_4960_: *mut leanh::LeanObject,
    mut v_k_4961_: *mut leanh::LeanObject,
    mut v_h_4962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4963_ =
        l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_4958_, v_k_4961_, v_t_4960_);
    return v___x_4963_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4967_ = l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__2;
    v___x_4968_ = leanh::lean_unsigned_to_nat(14);
    v___x_4969_ = leanh::lean_unsigned_to_nat(22);
    v___x_4970_ = l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__1;
    v___x_4971_ = l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__0;
    v___x_4972_ = l_mkPanicMessageWithDecl(
        v___x_4971_,
        v___x_4970_,
        v___x_4969_,
        v___x_4968_,
        v___x_4967_,
    );
    return v___x_4972_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE_x21___redArg(
    mut v_cmp_4973_: *mut leanh::LeanObject,
    mut v_inst_4974_: *mut leanh::LeanObject,
    mut v_t_4975_: *mut leanh::LeanObject,
    mut v_k_4976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4977_ = leanh::lean_box(0);
    v___x_4978_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_4973_,
        v_k_4976_,
        v___x_4977_,
        v_t_4975_,
    );
    if leanh::lean_obj_tag(v___x_4978_) == 0 {
        let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4979_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4980_ = l_panic___redArg(v_inst_4974_, v___x_4979_);
        return v___x_4980_;
    } else {
        let mut v_val_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4981_ = leanh::lean_ctor_get(v___x_4978_, 0);
        leanh::lean_inc(v_val_4981_);
        leanh::lean_dec_ref_known(v___x_4978_, 1);
        return v_val_4981_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE_x21___redArg___boxed(
    mut v_cmp_4982_: *mut leanh::LeanObject,
    mut v_inst_4983_: *mut leanh::LeanObject,
    mut v_t_4984_: *mut leanh::LeanObject,
    mut v_k_4985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4986_ =
        l_Std_ExtDTreeMap_getEntryGE_x21___redArg(v_cmp_4982_, v_inst_4983_, v_t_4984_, v_k_4985_);
    leanh::lean_dec_ref(v_inst_4983_);
    return v_res_4986_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE_x21(
    mut v_00_u03b1_4987_: *mut leanh::LeanObject,
    mut v_00_u03b2_4988_: *mut leanh::LeanObject,
    mut v_cmp_4989_: *mut leanh::LeanObject,
    mut v_inst_4990_: *mut leanh::LeanObject,
    mut v_inst_4991_: *mut leanh::LeanObject,
    mut v_t_4992_: *mut leanh::LeanObject,
    mut v_k_4993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4994_ = leanh::lean_box(0);
    v___x_4995_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_4989_,
        v_k_4993_,
        v___x_4994_,
        v_t_4992_,
    );
    if leanh::lean_obj_tag(v___x_4995_) == 0 {
        let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4996_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_4997_ = l_panic___redArg(v_inst_4991_, v___x_4996_);
        return v___x_4997_;
    } else {
        let mut v_val_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4998_ = leanh::lean_ctor_get(v___x_4995_, 0);
        leanh::lean_inc(v_val_4998_);
        leanh::lean_dec_ref_known(v___x_4995_, 1);
        return v_val_4998_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGE_x21___boxed(
    mut v_00_u03b1_4999_: *mut leanh::LeanObject,
    mut v_00_u03b2_5000_: *mut leanh::LeanObject,
    mut v_cmp_5001_: *mut leanh::LeanObject,
    mut v_inst_5002_: *mut leanh::LeanObject,
    mut v_inst_5003_: *mut leanh::LeanObject,
    mut v_t_5004_: *mut leanh::LeanObject,
    mut v_k_5005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5006_ = l_Std_ExtDTreeMap_getEntryGE_x21(
        v_00_u03b1_4999_,
        v_00_u03b2_5000_,
        v_cmp_5001_,
        v_inst_5002_,
        v_inst_5003_,
        v_t_5004_,
        v_k_5005_,
    );
    leanh::lean_dec_ref(v_inst_5003_);
    return v_res_5006_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT_x21___redArg(
    mut v_cmp_5007_: *mut leanh::LeanObject,
    mut v_inst_5008_: *mut leanh::LeanObject,
    mut v_t_5009_: *mut leanh::LeanObject,
    mut v_k_5010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5011_ = leanh::lean_box(0);
    v___x_5012_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5007_,
        v_k_5010_,
        v___x_5011_,
        v_t_5009_,
    );
    if leanh::lean_obj_tag(v___x_5012_) == 0 {
        let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5013_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5014_ = l_panic___redArg(v_inst_5008_, v___x_5013_);
        return v___x_5014_;
    } else {
        let mut v_val_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5015_ = leanh::lean_ctor_get(v___x_5012_, 0);
        leanh::lean_inc(v_val_5015_);
        leanh::lean_dec_ref_known(v___x_5012_, 1);
        return v_val_5015_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT_x21___redArg___boxed(
    mut v_cmp_5016_: *mut leanh::LeanObject,
    mut v_inst_5017_: *mut leanh::LeanObject,
    mut v_t_5018_: *mut leanh::LeanObject,
    mut v_k_5019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5020_ =
        l_Std_ExtDTreeMap_getEntryGT_x21___redArg(v_cmp_5016_, v_inst_5017_, v_t_5018_, v_k_5019_);
    leanh::lean_dec_ref(v_inst_5017_);
    return v_res_5020_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT_x21(
    mut v_00_u03b1_5021_: *mut leanh::LeanObject,
    mut v_00_u03b2_5022_: *mut leanh::LeanObject,
    mut v_cmp_5023_: *mut leanh::LeanObject,
    mut v_inst_5024_: *mut leanh::LeanObject,
    mut v_inst_5025_: *mut leanh::LeanObject,
    mut v_t_5026_: *mut leanh::LeanObject,
    mut v_k_5027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5028_ = leanh::lean_box(0);
    v___x_5029_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5023_,
        v_k_5027_,
        v___x_5028_,
        v_t_5026_,
    );
    if leanh::lean_obj_tag(v___x_5029_) == 0 {
        let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5030_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5031_ = l_panic___redArg(v_inst_5025_, v___x_5030_);
        return v___x_5031_;
    } else {
        let mut v_val_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5032_ = leanh::lean_ctor_get(v___x_5029_, 0);
        leanh::lean_inc(v_val_5032_);
        leanh::lean_dec_ref_known(v___x_5029_, 1);
        return v_val_5032_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGT_x21___boxed(
    mut v_00_u03b1_5033_: *mut leanh::LeanObject,
    mut v_00_u03b2_5034_: *mut leanh::LeanObject,
    mut v_cmp_5035_: *mut leanh::LeanObject,
    mut v_inst_5036_: *mut leanh::LeanObject,
    mut v_inst_5037_: *mut leanh::LeanObject,
    mut v_t_5038_: *mut leanh::LeanObject,
    mut v_k_5039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5040_ = l_Std_ExtDTreeMap_getEntryGT_x21(
        v_00_u03b1_5033_,
        v_00_u03b2_5034_,
        v_cmp_5035_,
        v_inst_5036_,
        v_inst_5037_,
        v_t_5038_,
        v_k_5039_,
    );
    leanh::lean_dec_ref(v_inst_5037_);
    return v_res_5040_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE_x21___redArg(
    mut v_cmp_5041_: *mut leanh::LeanObject,
    mut v_inst_5042_: *mut leanh::LeanObject,
    mut v_t_5043_: *mut leanh::LeanObject,
    mut v_k_5044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5045_ = leanh::lean_box(0);
    v___x_5046_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5041_,
        v_k_5044_,
        v___x_5045_,
        v_t_5043_,
    );
    if leanh::lean_obj_tag(v___x_5046_) == 0 {
        let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5047_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5048_ = l_panic___redArg(v_inst_5042_, v___x_5047_);
        return v___x_5048_;
    } else {
        let mut v_val_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5049_ = leanh::lean_ctor_get(v___x_5046_, 0);
        leanh::lean_inc(v_val_5049_);
        leanh::lean_dec_ref_known(v___x_5046_, 1);
        return v_val_5049_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE_x21___redArg___boxed(
    mut v_cmp_5050_: *mut leanh::LeanObject,
    mut v_inst_5051_: *mut leanh::LeanObject,
    mut v_t_5052_: *mut leanh::LeanObject,
    mut v_k_5053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5054_ =
        l_Std_ExtDTreeMap_getEntryLE_x21___redArg(v_cmp_5050_, v_inst_5051_, v_t_5052_, v_k_5053_);
    leanh::lean_dec_ref(v_inst_5051_);
    return v_res_5054_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE_x21(
    mut v_00_u03b1_5055_: *mut leanh::LeanObject,
    mut v_00_u03b2_5056_: *mut leanh::LeanObject,
    mut v_cmp_5057_: *mut leanh::LeanObject,
    mut v_inst_5058_: *mut leanh::LeanObject,
    mut v_inst_5059_: *mut leanh::LeanObject,
    mut v_t_5060_: *mut leanh::LeanObject,
    mut v_k_5061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5062_ = leanh::lean_box(0);
    v___x_5063_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5057_,
        v_k_5061_,
        v___x_5062_,
        v_t_5060_,
    );
    if leanh::lean_obj_tag(v___x_5063_) == 0 {
        let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5064_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5065_ = l_panic___redArg(v_inst_5059_, v___x_5064_);
        return v___x_5065_;
    } else {
        let mut v_val_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5066_ = leanh::lean_ctor_get(v___x_5063_, 0);
        leanh::lean_inc(v_val_5066_);
        leanh::lean_dec_ref_known(v___x_5063_, 1);
        return v_val_5066_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLE_x21___boxed(
    mut v_00_u03b1_5067_: *mut leanh::LeanObject,
    mut v_00_u03b2_5068_: *mut leanh::LeanObject,
    mut v_cmp_5069_: *mut leanh::LeanObject,
    mut v_inst_5070_: *mut leanh::LeanObject,
    mut v_inst_5071_: *mut leanh::LeanObject,
    mut v_t_5072_: *mut leanh::LeanObject,
    mut v_k_5073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5074_ = l_Std_ExtDTreeMap_getEntryLE_x21(
        v_00_u03b1_5067_,
        v_00_u03b2_5068_,
        v_cmp_5069_,
        v_inst_5070_,
        v_inst_5071_,
        v_t_5072_,
        v_k_5073_,
    );
    leanh::lean_dec_ref(v_inst_5071_);
    return v_res_5074_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT_x21___redArg(
    mut v_cmp_5075_: *mut leanh::LeanObject,
    mut v_inst_5076_: *mut leanh::LeanObject,
    mut v_t_5077_: *mut leanh::LeanObject,
    mut v_k_5078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5079_ = leanh::lean_box(0);
    v___x_5080_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5075_,
        v_k_5078_,
        v___x_5079_,
        v_t_5077_,
    );
    if leanh::lean_obj_tag(v___x_5080_) == 0 {
        let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5081_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5082_ = l_panic___redArg(v_inst_5076_, v___x_5081_);
        return v___x_5082_;
    } else {
        let mut v_val_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5083_ = leanh::lean_ctor_get(v___x_5080_, 0);
        leanh::lean_inc(v_val_5083_);
        leanh::lean_dec_ref_known(v___x_5080_, 1);
        return v_val_5083_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT_x21___redArg___boxed(
    mut v_cmp_5084_: *mut leanh::LeanObject,
    mut v_inst_5085_: *mut leanh::LeanObject,
    mut v_t_5086_: *mut leanh::LeanObject,
    mut v_k_5087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5088_ =
        l_Std_ExtDTreeMap_getEntryLT_x21___redArg(v_cmp_5084_, v_inst_5085_, v_t_5086_, v_k_5087_);
    leanh::lean_dec_ref(v_inst_5085_);
    return v_res_5088_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT_x21(
    mut v_00_u03b1_5089_: *mut leanh::LeanObject,
    mut v_00_u03b2_5090_: *mut leanh::LeanObject,
    mut v_cmp_5091_: *mut leanh::LeanObject,
    mut v_inst_5092_: *mut leanh::LeanObject,
    mut v_inst_5093_: *mut leanh::LeanObject,
    mut v_t_5094_: *mut leanh::LeanObject,
    mut v_k_5095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5096_ = leanh::lean_box(0);
    v___x_5097_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5091_,
        v_k_5095_,
        v___x_5096_,
        v_t_5094_,
    );
    if leanh::lean_obj_tag(v___x_5097_) == 0 {
        let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5098_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5099_ = l_panic___redArg(v_inst_5093_, v___x_5098_);
        return v___x_5099_;
    } else {
        let mut v_val_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5100_ = leanh::lean_ctor_get(v___x_5097_, 0);
        leanh::lean_inc(v_val_5100_);
        leanh::lean_dec_ref_known(v___x_5097_, 1);
        return v_val_5100_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLT_x21___boxed(
    mut v_00_u03b1_5101_: *mut leanh::LeanObject,
    mut v_00_u03b2_5102_: *mut leanh::LeanObject,
    mut v_cmp_5103_: *mut leanh::LeanObject,
    mut v_inst_5104_: *mut leanh::LeanObject,
    mut v_inst_5105_: *mut leanh::LeanObject,
    mut v_t_5106_: *mut leanh::LeanObject,
    mut v_k_5107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5108_ = l_Std_ExtDTreeMap_getEntryLT_x21(
        v_00_u03b1_5101_,
        v_00_u03b2_5102_,
        v_cmp_5103_,
        v_inst_5104_,
        v_inst_5105_,
        v_t_5106_,
        v_k_5107_,
    );
    leanh::lean_dec_ref(v_inst_5105_);
    return v_res_5108_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGED___redArg(
    mut v_cmp_5109_: *mut leanh::LeanObject,
    mut v_t_5110_: *mut leanh::LeanObject,
    mut v_k_5111_: *mut leanh::LeanObject,
    mut v_fallback_5112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5113_ = leanh::lean_box(0);
    v___x_5114_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_5109_,
        v_k_5111_,
        v___x_5113_,
        v_t_5110_,
    );
    if leanh::lean_obj_tag(v___x_5114_) == 0 {
        leanh::lean_inc_ref(v_fallback_5112_);
        return v_fallback_5112_;
    } else {
        let mut v_val_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5115_ = leanh::lean_ctor_get(v___x_5114_, 0);
        leanh::lean_inc(v_val_5115_);
        leanh::lean_dec_ref_known(v___x_5114_, 1);
        return v_val_5115_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGED___redArg___boxed(
    mut v_cmp_5116_: *mut leanh::LeanObject,
    mut v_t_5117_: *mut leanh::LeanObject,
    mut v_k_5118_: *mut leanh::LeanObject,
    mut v_fallback_5119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5120_ =
        l_Std_ExtDTreeMap_getEntryGED___redArg(v_cmp_5116_, v_t_5117_, v_k_5118_, v_fallback_5119_);
    leanh::lean_dec_ref(v_fallback_5119_);
    return v_res_5120_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGED(
    mut v_00_u03b1_5121_: *mut leanh::LeanObject,
    mut v_00_u03b2_5122_: *mut leanh::LeanObject,
    mut v_cmp_5123_: *mut leanh::LeanObject,
    mut v_inst_5124_: *mut leanh::LeanObject,
    mut v_t_5125_: *mut leanh::LeanObject,
    mut v_k_5126_: *mut leanh::LeanObject,
    mut v_fallback_5127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5128_ = leanh::lean_box(0);
    v___x_5129_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_5123_,
        v_k_5126_,
        v___x_5128_,
        v_t_5125_,
    );
    if leanh::lean_obj_tag(v___x_5129_) == 0 {
        leanh::lean_inc_ref(v_fallback_5127_);
        return v_fallback_5127_;
    } else {
        let mut v_val_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5130_ = leanh::lean_ctor_get(v___x_5129_, 0);
        leanh::lean_inc(v_val_5130_);
        leanh::lean_dec_ref_known(v___x_5129_, 1);
        return v_val_5130_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGED___boxed(
    mut v_00_u03b1_5131_: *mut leanh::LeanObject,
    mut v_00_u03b2_5132_: *mut leanh::LeanObject,
    mut v_cmp_5133_: *mut leanh::LeanObject,
    mut v_inst_5134_: *mut leanh::LeanObject,
    mut v_t_5135_: *mut leanh::LeanObject,
    mut v_k_5136_: *mut leanh::LeanObject,
    mut v_fallback_5137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5138_ = l_Std_ExtDTreeMap_getEntryGED(
        v_00_u03b1_5131_,
        v_00_u03b2_5132_,
        v_cmp_5133_,
        v_inst_5134_,
        v_t_5135_,
        v_k_5136_,
        v_fallback_5137_,
    );
    leanh::lean_dec_ref(v_fallback_5137_);
    return v_res_5138_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGTD___redArg(
    mut v_cmp_5139_: *mut leanh::LeanObject,
    mut v_t_5140_: *mut leanh::LeanObject,
    mut v_k_5141_: *mut leanh::LeanObject,
    mut v_fallback_5142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5143_ = leanh::lean_box(0);
    v___x_5144_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5139_,
        v_k_5141_,
        v___x_5143_,
        v_t_5140_,
    );
    if leanh::lean_obj_tag(v___x_5144_) == 0 {
        leanh::lean_inc_ref(v_fallback_5142_);
        return v_fallback_5142_;
    } else {
        let mut v_val_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5145_ = leanh::lean_ctor_get(v___x_5144_, 0);
        leanh::lean_inc(v_val_5145_);
        leanh::lean_dec_ref_known(v___x_5144_, 1);
        return v_val_5145_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGTD___redArg___boxed(
    mut v_cmp_5146_: *mut leanh::LeanObject,
    mut v_t_5147_: *mut leanh::LeanObject,
    mut v_k_5148_: *mut leanh::LeanObject,
    mut v_fallback_5149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5150_ =
        l_Std_ExtDTreeMap_getEntryGTD___redArg(v_cmp_5146_, v_t_5147_, v_k_5148_, v_fallback_5149_);
    leanh::lean_dec_ref(v_fallback_5149_);
    return v_res_5150_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGTD(
    mut v_00_u03b1_5151_: *mut leanh::LeanObject,
    mut v_00_u03b2_5152_: *mut leanh::LeanObject,
    mut v_cmp_5153_: *mut leanh::LeanObject,
    mut v_inst_5154_: *mut leanh::LeanObject,
    mut v_t_5155_: *mut leanh::LeanObject,
    mut v_k_5156_: *mut leanh::LeanObject,
    mut v_fallback_5157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5158_ = leanh::lean_box(0);
    v___x_5159_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5153_,
        v_k_5156_,
        v___x_5158_,
        v_t_5155_,
    );
    if leanh::lean_obj_tag(v___x_5159_) == 0 {
        leanh::lean_inc_ref(v_fallback_5157_);
        return v_fallback_5157_;
    } else {
        let mut v_val_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5160_ = leanh::lean_ctor_get(v___x_5159_, 0);
        leanh::lean_inc(v_val_5160_);
        leanh::lean_dec_ref_known(v___x_5159_, 1);
        return v_val_5160_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryGTD___boxed(
    mut v_00_u03b1_5161_: *mut leanh::LeanObject,
    mut v_00_u03b2_5162_: *mut leanh::LeanObject,
    mut v_cmp_5163_: *mut leanh::LeanObject,
    mut v_inst_5164_: *mut leanh::LeanObject,
    mut v_t_5165_: *mut leanh::LeanObject,
    mut v_k_5166_: *mut leanh::LeanObject,
    mut v_fallback_5167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5168_ = l_Std_ExtDTreeMap_getEntryGTD(
        v_00_u03b1_5161_,
        v_00_u03b2_5162_,
        v_cmp_5163_,
        v_inst_5164_,
        v_t_5165_,
        v_k_5166_,
        v_fallback_5167_,
    );
    leanh::lean_dec_ref(v_fallback_5167_);
    return v_res_5168_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLED___redArg(
    mut v_cmp_5169_: *mut leanh::LeanObject,
    mut v_t_5170_: *mut leanh::LeanObject,
    mut v_k_5171_: *mut leanh::LeanObject,
    mut v_fallback_5172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5173_ = leanh::lean_box(0);
    v___x_5174_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5169_,
        v_k_5171_,
        v___x_5173_,
        v_t_5170_,
    );
    if leanh::lean_obj_tag(v___x_5174_) == 0 {
        leanh::lean_inc_ref(v_fallback_5172_);
        return v_fallback_5172_;
    } else {
        let mut v_val_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5175_ = leanh::lean_ctor_get(v___x_5174_, 0);
        leanh::lean_inc(v_val_5175_);
        leanh::lean_dec_ref_known(v___x_5174_, 1);
        return v_val_5175_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLED___redArg___boxed(
    mut v_cmp_5176_: *mut leanh::LeanObject,
    mut v_t_5177_: *mut leanh::LeanObject,
    mut v_k_5178_: *mut leanh::LeanObject,
    mut v_fallback_5179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5180_ =
        l_Std_ExtDTreeMap_getEntryLED___redArg(v_cmp_5176_, v_t_5177_, v_k_5178_, v_fallback_5179_);
    leanh::lean_dec_ref(v_fallback_5179_);
    return v_res_5180_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLED(
    mut v_00_u03b1_5181_: *mut leanh::LeanObject,
    mut v_00_u03b2_5182_: *mut leanh::LeanObject,
    mut v_cmp_5183_: *mut leanh::LeanObject,
    mut v_inst_5184_: *mut leanh::LeanObject,
    mut v_t_5185_: *mut leanh::LeanObject,
    mut v_k_5186_: *mut leanh::LeanObject,
    mut v_fallback_5187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5188_ = leanh::lean_box(0);
    v___x_5189_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5183_,
        v_k_5186_,
        v___x_5188_,
        v_t_5185_,
    );
    if leanh::lean_obj_tag(v___x_5189_) == 0 {
        leanh::lean_inc_ref(v_fallback_5187_);
        return v_fallback_5187_;
    } else {
        let mut v_val_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5190_ = leanh::lean_ctor_get(v___x_5189_, 0);
        leanh::lean_inc(v_val_5190_);
        leanh::lean_dec_ref_known(v___x_5189_, 1);
        return v_val_5190_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLED___boxed(
    mut v_00_u03b1_5191_: *mut leanh::LeanObject,
    mut v_00_u03b2_5192_: *mut leanh::LeanObject,
    mut v_cmp_5193_: *mut leanh::LeanObject,
    mut v_inst_5194_: *mut leanh::LeanObject,
    mut v_t_5195_: *mut leanh::LeanObject,
    mut v_k_5196_: *mut leanh::LeanObject,
    mut v_fallback_5197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Std_ExtDTreeMap_getEntryLED(
        v_00_u03b1_5191_,
        v_00_u03b2_5192_,
        v_cmp_5193_,
        v_inst_5194_,
        v_t_5195_,
        v_k_5196_,
        v_fallback_5197_,
    );
    leanh::lean_dec_ref(v_fallback_5197_);
    return v_res_5198_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLTD___redArg(
    mut v_cmp_5199_: *mut leanh::LeanObject,
    mut v_t_5200_: *mut leanh::LeanObject,
    mut v_k_5201_: *mut leanh::LeanObject,
    mut v_fallback_5202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5203_ = leanh::lean_box(0);
    v___x_5204_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5199_,
        v_k_5201_,
        v___x_5203_,
        v_t_5200_,
    );
    if leanh::lean_obj_tag(v___x_5204_) == 0 {
        leanh::lean_inc_ref(v_fallback_5202_);
        return v_fallback_5202_;
    } else {
        let mut v_val_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5205_ = leanh::lean_ctor_get(v___x_5204_, 0);
        leanh::lean_inc(v_val_5205_);
        leanh::lean_dec_ref_known(v___x_5204_, 1);
        return v_val_5205_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLTD___redArg___boxed(
    mut v_cmp_5206_: *mut leanh::LeanObject,
    mut v_t_5207_: *mut leanh::LeanObject,
    mut v_k_5208_: *mut leanh::LeanObject,
    mut v_fallback_5209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5210_ =
        l_Std_ExtDTreeMap_getEntryLTD___redArg(v_cmp_5206_, v_t_5207_, v_k_5208_, v_fallback_5209_);
    leanh::lean_dec_ref(v_fallback_5209_);
    return v_res_5210_;
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLTD(
    mut v_00_u03b1_5211_: *mut leanh::LeanObject,
    mut v_00_u03b2_5212_: *mut leanh::LeanObject,
    mut v_cmp_5213_: *mut leanh::LeanObject,
    mut v_inst_5214_: *mut leanh::LeanObject,
    mut v_t_5215_: *mut leanh::LeanObject,
    mut v_k_5216_: *mut leanh::LeanObject,
    mut v_fallback_5217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5218_ = leanh::lean_box(0);
    v___x_5219_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5213_,
        v_k_5216_,
        v___x_5218_,
        v_t_5215_,
    );
    if leanh::lean_obj_tag(v___x_5219_) == 0 {
        leanh::lean_inc_ref(v_fallback_5217_);
        return v_fallback_5217_;
    } else {
        let mut v_val_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5220_ = leanh::lean_ctor_get(v___x_5219_, 0);
        leanh::lean_inc(v_val_5220_);
        leanh::lean_dec_ref_known(v___x_5219_, 1);
        return v_val_5220_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getEntryLTD___boxed(
    mut v_00_u03b1_5221_: *mut leanh::LeanObject,
    mut v_00_u03b2_5222_: *mut leanh::LeanObject,
    mut v_cmp_5223_: *mut leanh::LeanObject,
    mut v_inst_5224_: *mut leanh::LeanObject,
    mut v_t_5225_: *mut leanh::LeanObject,
    mut v_k_5226_: *mut leanh::LeanObject,
    mut v_fallback_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Std_ExtDTreeMap_getEntryLTD(
        v_00_u03b1_5221_,
        v_00_u03b2_5222_,
        v_cmp_5223_,
        v_inst_5224_,
        v_t_5225_,
        v_k_5226_,
        v_fallback_5227_,
    );
    leanh::lean_dec_ref(v_fallback_5227_);
    return v_res_5228_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE_x3f___redArg(
    mut v_cmp_5229_: *mut leanh::LeanObject,
    mut v_t_5230_: *mut leanh::LeanObject,
    mut v_k_5231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5232_ = leanh::lean_box(0);
    v___x_5233_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_5229_,
        v_k_5231_,
        v___x_5232_,
        v_t_5230_,
    );
    return v___x_5233_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE_x3f(
    mut v_00_u03b1_5234_: *mut leanh::LeanObject,
    mut v_00_u03b2_5235_: *mut leanh::LeanObject,
    mut v_cmp_5236_: *mut leanh::LeanObject,
    mut v_inst_5237_: *mut leanh::LeanObject,
    mut v_t_5238_: *mut leanh::LeanObject,
    mut v_k_5239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5240_ = leanh::lean_box(0);
    v___x_5241_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_5236_,
        v_k_5239_,
        v___x_5240_,
        v_t_5238_,
    );
    return v___x_5241_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT_x3f___redArg(
    mut v_cmp_5242_: *mut leanh::LeanObject,
    mut v_t_5243_: *mut leanh::LeanObject,
    mut v_k_5244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5245_ = leanh::lean_box(0);
    v___x_5246_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_5242_,
        v_k_5244_,
        v___x_5245_,
        v_t_5243_,
    );
    return v___x_5246_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT_x3f(
    mut v_00_u03b1_5247_: *mut leanh::LeanObject,
    mut v_00_u03b2_5248_: *mut leanh::LeanObject,
    mut v_cmp_5249_: *mut leanh::LeanObject,
    mut v_inst_5250_: *mut leanh::LeanObject,
    mut v_t_5251_: *mut leanh::LeanObject,
    mut v_k_5252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5253_ = leanh::lean_box(0);
    v___x_5254_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_5249_,
        v_k_5252_,
        v___x_5253_,
        v_t_5251_,
    );
    return v___x_5254_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE_x3f___redArg(
    mut v_cmp_5255_: *mut leanh::LeanObject,
    mut v_t_5256_: *mut leanh::LeanObject,
    mut v_k_5257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5258_ = leanh::lean_box(0);
    v___x_5259_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_5255_,
        v_k_5257_,
        v___x_5258_,
        v_t_5256_,
    );
    return v___x_5259_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE_x3f(
    mut v_00_u03b1_5260_: *mut leanh::LeanObject,
    mut v_00_u03b2_5261_: *mut leanh::LeanObject,
    mut v_cmp_5262_: *mut leanh::LeanObject,
    mut v_inst_5263_: *mut leanh::LeanObject,
    mut v_t_5264_: *mut leanh::LeanObject,
    mut v_k_5265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5266_ = leanh::lean_box(0);
    v___x_5267_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_5262_,
        v_k_5265_,
        v___x_5266_,
        v_t_5264_,
    );
    return v___x_5267_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT_x3f___redArg(
    mut v_cmp_5268_: *mut leanh::LeanObject,
    mut v_t_5269_: *mut leanh::LeanObject,
    mut v_k_5270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5271_ = leanh::lean_box(0);
    v___x_5272_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_5268_,
        v_k_5270_,
        v___x_5271_,
        v_t_5269_,
    );
    return v___x_5272_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT_x3f(
    mut v_00_u03b1_5273_: *mut leanh::LeanObject,
    mut v_00_u03b2_5274_: *mut leanh::LeanObject,
    mut v_cmp_5275_: *mut leanh::LeanObject,
    mut v_inst_5276_: *mut leanh::LeanObject,
    mut v_t_5277_: *mut leanh::LeanObject,
    mut v_k_5278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5279_ = leanh::lean_box(0);
    v___x_5280_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_5275_,
        v_k_5278_,
        v___x_5279_,
        v_t_5277_,
    );
    return v___x_5280_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE___redArg(
    mut v_cmp_5281_: *mut leanh::LeanObject,
    mut v_t_5282_: *mut leanh::LeanObject,
    mut v_k_5283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5284_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_5281_, v_k_5283_, v_t_5282_);
    return v___x_5284_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE(
    mut v_00_u03b1_5285_: *mut leanh::LeanObject,
    mut v_00_u03b2_5286_: *mut leanh::LeanObject,
    mut v_cmp_5287_: *mut leanh::LeanObject,
    mut v_inst_5288_: *mut leanh::LeanObject,
    mut v_t_5289_: *mut leanh::LeanObject,
    mut v_k_5290_: *mut leanh::LeanObject,
    mut v_h_5291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5292_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_5287_, v_k_5290_, v_t_5289_);
    return v___x_5292_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT___redArg(
    mut v_cmp_5293_: *mut leanh::LeanObject,
    mut v_t_5294_: *mut leanh::LeanObject,
    mut v_k_5295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5296_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_5293_, v_k_5295_, v_t_5294_);
    return v___x_5296_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT(
    mut v_00_u03b1_5297_: *mut leanh::LeanObject,
    mut v_00_u03b2_5298_: *mut leanh::LeanObject,
    mut v_cmp_5299_: *mut leanh::LeanObject,
    mut v_inst_5300_: *mut leanh::LeanObject,
    mut v_t_5301_: *mut leanh::LeanObject,
    mut v_k_5302_: *mut leanh::LeanObject,
    mut v_h_5303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5304_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_5299_, v_k_5302_, v_t_5301_);
    return v___x_5304_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE___redArg(
    mut v_cmp_5305_: *mut leanh::LeanObject,
    mut v_t_5306_: *mut leanh::LeanObject,
    mut v_k_5307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5308_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_5305_, v_k_5307_, v_t_5306_);
    return v___x_5308_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE(
    mut v_00_u03b1_5309_: *mut leanh::LeanObject,
    mut v_00_u03b2_5310_: *mut leanh::LeanObject,
    mut v_cmp_5311_: *mut leanh::LeanObject,
    mut v_inst_5312_: *mut leanh::LeanObject,
    mut v_t_5313_: *mut leanh::LeanObject,
    mut v_k_5314_: *mut leanh::LeanObject,
    mut v_h_5315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5316_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_5311_, v_k_5314_, v_t_5313_);
    return v___x_5316_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT___redArg(
    mut v_cmp_5317_: *mut leanh::LeanObject,
    mut v_t_5318_: *mut leanh::LeanObject,
    mut v_k_5319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5320_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_5317_, v_k_5319_, v_t_5318_);
    return v___x_5320_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT(
    mut v_00_u03b1_5321_: *mut leanh::LeanObject,
    mut v_00_u03b2_5322_: *mut leanh::LeanObject,
    mut v_cmp_5323_: *mut leanh::LeanObject,
    mut v_inst_5324_: *mut leanh::LeanObject,
    mut v_t_5325_: *mut leanh::LeanObject,
    mut v_k_5326_: *mut leanh::LeanObject,
    mut v_h_5327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5328_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_5323_, v_k_5326_, v_t_5325_);
    return v___x_5328_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE_x21___redArg(
    mut v_cmp_5329_: *mut leanh::LeanObject,
    mut v_inst_5330_: *mut leanh::LeanObject,
    mut v_t_5331_: *mut leanh::LeanObject,
    mut v_k_5332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5333_ = leanh::lean_box(0);
    v___x_5334_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_5329_,
        v_k_5332_,
        v___x_5333_,
        v_t_5331_,
    );
    if leanh::lean_obj_tag(v___x_5334_) == 0 {
        let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5335_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5336_ = l_panic___redArg(v_inst_5330_, v___x_5335_);
        return v___x_5336_;
    } else {
        let mut v_val_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5337_ = leanh::lean_ctor_get(v___x_5334_, 0);
        leanh::lean_inc(v_val_5337_);
        leanh::lean_dec_ref_known(v___x_5334_, 1);
        return v_val_5337_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE_x21___redArg___boxed(
    mut v_cmp_5338_: *mut leanh::LeanObject,
    mut v_inst_5339_: *mut leanh::LeanObject,
    mut v_t_5340_: *mut leanh::LeanObject,
    mut v_k_5341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5342_ =
        l_Std_ExtDTreeMap_getKeyGE_x21___redArg(v_cmp_5338_, v_inst_5339_, v_t_5340_, v_k_5341_);
    leanh::lean_dec(v_inst_5339_);
    return v_res_5342_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE_x21(
    mut v_00_u03b1_5343_: *mut leanh::LeanObject,
    mut v_00_u03b2_5344_: *mut leanh::LeanObject,
    mut v_cmp_5345_: *mut leanh::LeanObject,
    mut v_inst_5346_: *mut leanh::LeanObject,
    mut v_inst_5347_: *mut leanh::LeanObject,
    mut v_t_5348_: *mut leanh::LeanObject,
    mut v_k_5349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5350_ = leanh::lean_box(0);
    v___x_5351_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_5345_,
        v_k_5349_,
        v___x_5350_,
        v_t_5348_,
    );
    if leanh::lean_obj_tag(v___x_5351_) == 0 {
        let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5352_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5353_ = l_panic___redArg(v_inst_5347_, v___x_5352_);
        return v___x_5353_;
    } else {
        let mut v_val_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5354_ = leanh::lean_ctor_get(v___x_5351_, 0);
        leanh::lean_inc(v_val_5354_);
        leanh::lean_dec_ref_known(v___x_5351_, 1);
        return v_val_5354_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGE_x21___boxed(
    mut v_00_u03b1_5355_: *mut leanh::LeanObject,
    mut v_00_u03b2_5356_: *mut leanh::LeanObject,
    mut v_cmp_5357_: *mut leanh::LeanObject,
    mut v_inst_5358_: *mut leanh::LeanObject,
    mut v_inst_5359_: *mut leanh::LeanObject,
    mut v_t_5360_: *mut leanh::LeanObject,
    mut v_k_5361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5362_ = l_Std_ExtDTreeMap_getKeyGE_x21(
        v_00_u03b1_5355_,
        v_00_u03b2_5356_,
        v_cmp_5357_,
        v_inst_5358_,
        v_inst_5359_,
        v_t_5360_,
        v_k_5361_,
    );
    leanh::lean_dec(v_inst_5359_);
    return v_res_5362_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT_x21___redArg(
    mut v_cmp_5363_: *mut leanh::LeanObject,
    mut v_inst_5364_: *mut leanh::LeanObject,
    mut v_t_5365_: *mut leanh::LeanObject,
    mut v_k_5366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5367_ = leanh::lean_box(0);
    v___x_5368_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_5363_,
        v_k_5366_,
        v___x_5367_,
        v_t_5365_,
    );
    if leanh::lean_obj_tag(v___x_5368_) == 0 {
        let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5369_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5370_ = l_panic___redArg(v_inst_5364_, v___x_5369_);
        return v___x_5370_;
    } else {
        let mut v_val_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5371_ = leanh::lean_ctor_get(v___x_5368_, 0);
        leanh::lean_inc(v_val_5371_);
        leanh::lean_dec_ref_known(v___x_5368_, 1);
        return v_val_5371_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT_x21___redArg___boxed(
    mut v_cmp_5372_: *mut leanh::LeanObject,
    mut v_inst_5373_: *mut leanh::LeanObject,
    mut v_t_5374_: *mut leanh::LeanObject,
    mut v_k_5375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5376_ =
        l_Std_ExtDTreeMap_getKeyGT_x21___redArg(v_cmp_5372_, v_inst_5373_, v_t_5374_, v_k_5375_);
    leanh::lean_dec(v_inst_5373_);
    return v_res_5376_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT_x21(
    mut v_00_u03b1_5377_: *mut leanh::LeanObject,
    mut v_00_u03b2_5378_: *mut leanh::LeanObject,
    mut v_cmp_5379_: *mut leanh::LeanObject,
    mut v_inst_5380_: *mut leanh::LeanObject,
    mut v_inst_5381_: *mut leanh::LeanObject,
    mut v_t_5382_: *mut leanh::LeanObject,
    mut v_k_5383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5384_ = leanh::lean_box(0);
    v___x_5385_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_5379_,
        v_k_5383_,
        v___x_5384_,
        v_t_5382_,
    );
    if leanh::lean_obj_tag(v___x_5385_) == 0 {
        let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5386_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5387_ = l_panic___redArg(v_inst_5381_, v___x_5386_);
        return v___x_5387_;
    } else {
        let mut v_val_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5388_ = leanh::lean_ctor_get(v___x_5385_, 0);
        leanh::lean_inc(v_val_5388_);
        leanh::lean_dec_ref_known(v___x_5385_, 1);
        return v_val_5388_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGT_x21___boxed(
    mut v_00_u03b1_5389_: *mut leanh::LeanObject,
    mut v_00_u03b2_5390_: *mut leanh::LeanObject,
    mut v_cmp_5391_: *mut leanh::LeanObject,
    mut v_inst_5392_: *mut leanh::LeanObject,
    mut v_inst_5393_: *mut leanh::LeanObject,
    mut v_t_5394_: *mut leanh::LeanObject,
    mut v_k_5395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5396_ = l_Std_ExtDTreeMap_getKeyGT_x21(
        v_00_u03b1_5389_,
        v_00_u03b2_5390_,
        v_cmp_5391_,
        v_inst_5392_,
        v_inst_5393_,
        v_t_5394_,
        v_k_5395_,
    );
    leanh::lean_dec(v_inst_5393_);
    return v_res_5396_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE_x21___redArg(
    mut v_cmp_5397_: *mut leanh::LeanObject,
    mut v_inst_5398_: *mut leanh::LeanObject,
    mut v_t_5399_: *mut leanh::LeanObject,
    mut v_k_5400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5401_ = leanh::lean_box(0);
    v___x_5402_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_5397_,
        v_k_5400_,
        v___x_5401_,
        v_t_5399_,
    );
    if leanh::lean_obj_tag(v___x_5402_) == 0 {
        let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5403_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5404_ = l_panic___redArg(v_inst_5398_, v___x_5403_);
        return v___x_5404_;
    } else {
        let mut v_val_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5405_ = leanh::lean_ctor_get(v___x_5402_, 0);
        leanh::lean_inc(v_val_5405_);
        leanh::lean_dec_ref_known(v___x_5402_, 1);
        return v_val_5405_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE_x21___redArg___boxed(
    mut v_cmp_5406_: *mut leanh::LeanObject,
    mut v_inst_5407_: *mut leanh::LeanObject,
    mut v_t_5408_: *mut leanh::LeanObject,
    mut v_k_5409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5410_ =
        l_Std_ExtDTreeMap_getKeyLE_x21___redArg(v_cmp_5406_, v_inst_5407_, v_t_5408_, v_k_5409_);
    leanh::lean_dec(v_inst_5407_);
    return v_res_5410_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE_x21(
    mut v_00_u03b1_5411_: *mut leanh::LeanObject,
    mut v_00_u03b2_5412_: *mut leanh::LeanObject,
    mut v_cmp_5413_: *mut leanh::LeanObject,
    mut v_inst_5414_: *mut leanh::LeanObject,
    mut v_inst_5415_: *mut leanh::LeanObject,
    mut v_t_5416_: *mut leanh::LeanObject,
    mut v_k_5417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5418_ = leanh::lean_box(0);
    v___x_5419_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_5413_,
        v_k_5417_,
        v___x_5418_,
        v_t_5416_,
    );
    if leanh::lean_obj_tag(v___x_5419_) == 0 {
        let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5420_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5421_ = l_panic___redArg(v_inst_5415_, v___x_5420_);
        return v___x_5421_;
    } else {
        let mut v_val_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5422_ = leanh::lean_ctor_get(v___x_5419_, 0);
        leanh::lean_inc(v_val_5422_);
        leanh::lean_dec_ref_known(v___x_5419_, 1);
        return v_val_5422_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLE_x21___boxed(
    mut v_00_u03b1_5423_: *mut leanh::LeanObject,
    mut v_00_u03b2_5424_: *mut leanh::LeanObject,
    mut v_cmp_5425_: *mut leanh::LeanObject,
    mut v_inst_5426_: *mut leanh::LeanObject,
    mut v_inst_5427_: *mut leanh::LeanObject,
    mut v_t_5428_: *mut leanh::LeanObject,
    mut v_k_5429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5430_ = l_Std_ExtDTreeMap_getKeyLE_x21(
        v_00_u03b1_5423_,
        v_00_u03b2_5424_,
        v_cmp_5425_,
        v_inst_5426_,
        v_inst_5427_,
        v_t_5428_,
        v_k_5429_,
    );
    leanh::lean_dec(v_inst_5427_);
    return v_res_5430_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT_x21___redArg(
    mut v_cmp_5431_: *mut leanh::LeanObject,
    mut v_inst_5432_: *mut leanh::LeanObject,
    mut v_t_5433_: *mut leanh::LeanObject,
    mut v_k_5434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5435_ = leanh::lean_box(0);
    v___x_5436_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_5431_,
        v_k_5434_,
        v___x_5435_,
        v_t_5433_,
    );
    if leanh::lean_obj_tag(v___x_5436_) == 0 {
        let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5437_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5438_ = l_panic___redArg(v_inst_5432_, v___x_5437_);
        return v___x_5438_;
    } else {
        let mut v_val_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5439_ = leanh::lean_ctor_get(v___x_5436_, 0);
        leanh::lean_inc(v_val_5439_);
        leanh::lean_dec_ref_known(v___x_5436_, 1);
        return v_val_5439_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT_x21___redArg___boxed(
    mut v_cmp_5440_: *mut leanh::LeanObject,
    mut v_inst_5441_: *mut leanh::LeanObject,
    mut v_t_5442_: *mut leanh::LeanObject,
    mut v_k_5443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5444_ =
        l_Std_ExtDTreeMap_getKeyLT_x21___redArg(v_cmp_5440_, v_inst_5441_, v_t_5442_, v_k_5443_);
    leanh::lean_dec(v_inst_5441_);
    return v_res_5444_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT_x21(
    mut v_00_u03b1_5445_: *mut leanh::LeanObject,
    mut v_00_u03b2_5446_: *mut leanh::LeanObject,
    mut v_cmp_5447_: *mut leanh::LeanObject,
    mut v_inst_5448_: *mut leanh::LeanObject,
    mut v_inst_5449_: *mut leanh::LeanObject,
    mut v_t_5450_: *mut leanh::LeanObject,
    mut v_k_5451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5452_ = leanh::lean_box(0);
    v___x_5453_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_5447_,
        v_k_5451_,
        v___x_5452_,
        v_t_5450_,
    );
    if leanh::lean_obj_tag(v___x_5453_) == 0 {
        let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5454_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5455_ = l_panic___redArg(v_inst_5449_, v___x_5454_);
        return v___x_5455_;
    } else {
        let mut v_val_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5456_ = leanh::lean_ctor_get(v___x_5453_, 0);
        leanh::lean_inc(v_val_5456_);
        leanh::lean_dec_ref_known(v___x_5453_, 1);
        return v_val_5456_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLT_x21___boxed(
    mut v_00_u03b1_5457_: *mut leanh::LeanObject,
    mut v_00_u03b2_5458_: *mut leanh::LeanObject,
    mut v_cmp_5459_: *mut leanh::LeanObject,
    mut v_inst_5460_: *mut leanh::LeanObject,
    mut v_inst_5461_: *mut leanh::LeanObject,
    mut v_t_5462_: *mut leanh::LeanObject,
    mut v_k_5463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5464_ = l_Std_ExtDTreeMap_getKeyLT_x21(
        v_00_u03b1_5457_,
        v_00_u03b2_5458_,
        v_cmp_5459_,
        v_inst_5460_,
        v_inst_5461_,
        v_t_5462_,
        v_k_5463_,
    );
    leanh::lean_dec(v_inst_5461_);
    return v_res_5464_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGED___redArg(
    mut v_cmp_5465_: *mut leanh::LeanObject,
    mut v_t_5466_: *mut leanh::LeanObject,
    mut v_k_5467_: *mut leanh::LeanObject,
    mut v_fallback_5468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5469_ = leanh::lean_box(0);
    v___x_5470_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_5465_,
        v_k_5467_,
        v___x_5469_,
        v_t_5466_,
    );
    if leanh::lean_obj_tag(v___x_5470_) == 0 {
        leanh::lean_inc(v_fallback_5468_);
        return v_fallback_5468_;
    } else {
        let mut v_val_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5471_ = leanh::lean_ctor_get(v___x_5470_, 0);
        leanh::lean_inc(v_val_5471_);
        leanh::lean_dec_ref_known(v___x_5470_, 1);
        return v_val_5471_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGED___redArg___boxed(
    mut v_cmp_5472_: *mut leanh::LeanObject,
    mut v_t_5473_: *mut leanh::LeanObject,
    mut v_k_5474_: *mut leanh::LeanObject,
    mut v_fallback_5475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5476_ =
        l_Std_ExtDTreeMap_getKeyGED___redArg(v_cmp_5472_, v_t_5473_, v_k_5474_, v_fallback_5475_);
    leanh::lean_dec(v_fallback_5475_);
    return v_res_5476_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGED(
    mut v_00_u03b1_5477_: *mut leanh::LeanObject,
    mut v_00_u03b2_5478_: *mut leanh::LeanObject,
    mut v_cmp_5479_: *mut leanh::LeanObject,
    mut v_inst_5480_: *mut leanh::LeanObject,
    mut v_t_5481_: *mut leanh::LeanObject,
    mut v_k_5482_: *mut leanh::LeanObject,
    mut v_fallback_5483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5484_ = leanh::lean_box(0);
    v___x_5485_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_5479_,
        v_k_5482_,
        v___x_5484_,
        v_t_5481_,
    );
    if leanh::lean_obj_tag(v___x_5485_) == 0 {
        leanh::lean_inc(v_fallback_5483_);
        return v_fallback_5483_;
    } else {
        let mut v_val_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5486_ = leanh::lean_ctor_get(v___x_5485_, 0);
        leanh::lean_inc(v_val_5486_);
        leanh::lean_dec_ref_known(v___x_5485_, 1);
        return v_val_5486_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGED___boxed(
    mut v_00_u03b1_5487_: *mut leanh::LeanObject,
    mut v_00_u03b2_5488_: *mut leanh::LeanObject,
    mut v_cmp_5489_: *mut leanh::LeanObject,
    mut v_inst_5490_: *mut leanh::LeanObject,
    mut v_t_5491_: *mut leanh::LeanObject,
    mut v_k_5492_: *mut leanh::LeanObject,
    mut v_fallback_5493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5494_ = l_Std_ExtDTreeMap_getKeyGED(
        v_00_u03b1_5487_,
        v_00_u03b2_5488_,
        v_cmp_5489_,
        v_inst_5490_,
        v_t_5491_,
        v_k_5492_,
        v_fallback_5493_,
    );
    leanh::lean_dec(v_fallback_5493_);
    return v_res_5494_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGTD___redArg(
    mut v_cmp_5495_: *mut leanh::LeanObject,
    mut v_t_5496_: *mut leanh::LeanObject,
    mut v_k_5497_: *mut leanh::LeanObject,
    mut v_fallback_5498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = leanh::lean_box(0);
    v___x_5500_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_5495_,
        v_k_5497_,
        v___x_5499_,
        v_t_5496_,
    );
    if leanh::lean_obj_tag(v___x_5500_) == 0 {
        leanh::lean_inc(v_fallback_5498_);
        return v_fallback_5498_;
    } else {
        let mut v_val_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5501_ = leanh::lean_ctor_get(v___x_5500_, 0);
        leanh::lean_inc(v_val_5501_);
        leanh::lean_dec_ref_known(v___x_5500_, 1);
        return v_val_5501_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGTD___redArg___boxed(
    mut v_cmp_5502_: *mut leanh::LeanObject,
    mut v_t_5503_: *mut leanh::LeanObject,
    mut v_k_5504_: *mut leanh::LeanObject,
    mut v_fallback_5505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5506_ =
        l_Std_ExtDTreeMap_getKeyGTD___redArg(v_cmp_5502_, v_t_5503_, v_k_5504_, v_fallback_5505_);
    leanh::lean_dec(v_fallback_5505_);
    return v_res_5506_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGTD(
    mut v_00_u03b1_5507_: *mut leanh::LeanObject,
    mut v_00_u03b2_5508_: *mut leanh::LeanObject,
    mut v_cmp_5509_: *mut leanh::LeanObject,
    mut v_inst_5510_: *mut leanh::LeanObject,
    mut v_t_5511_: *mut leanh::LeanObject,
    mut v_k_5512_: *mut leanh::LeanObject,
    mut v_fallback_5513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5514_ = leanh::lean_box(0);
    v___x_5515_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_5509_,
        v_k_5512_,
        v___x_5514_,
        v_t_5511_,
    );
    if leanh::lean_obj_tag(v___x_5515_) == 0 {
        leanh::lean_inc(v_fallback_5513_);
        return v_fallback_5513_;
    } else {
        let mut v_val_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5516_ = leanh::lean_ctor_get(v___x_5515_, 0);
        leanh::lean_inc(v_val_5516_);
        leanh::lean_dec_ref_known(v___x_5515_, 1);
        return v_val_5516_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyGTD___boxed(
    mut v_00_u03b1_5517_: *mut leanh::LeanObject,
    mut v_00_u03b2_5518_: *mut leanh::LeanObject,
    mut v_cmp_5519_: *mut leanh::LeanObject,
    mut v_inst_5520_: *mut leanh::LeanObject,
    mut v_t_5521_: *mut leanh::LeanObject,
    mut v_k_5522_: *mut leanh::LeanObject,
    mut v_fallback_5523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5524_ = l_Std_ExtDTreeMap_getKeyGTD(
        v_00_u03b1_5517_,
        v_00_u03b2_5518_,
        v_cmp_5519_,
        v_inst_5520_,
        v_t_5521_,
        v_k_5522_,
        v_fallback_5523_,
    );
    leanh::lean_dec(v_fallback_5523_);
    return v_res_5524_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLED___redArg(
    mut v_cmp_5525_: *mut leanh::LeanObject,
    mut v_t_5526_: *mut leanh::LeanObject,
    mut v_k_5527_: *mut leanh::LeanObject,
    mut v_fallback_5528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5529_ = leanh::lean_box(0);
    v___x_5530_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_5525_,
        v_k_5527_,
        v___x_5529_,
        v_t_5526_,
    );
    if leanh::lean_obj_tag(v___x_5530_) == 0 {
        leanh::lean_inc(v_fallback_5528_);
        return v_fallback_5528_;
    } else {
        let mut v_val_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5531_ = leanh::lean_ctor_get(v___x_5530_, 0);
        leanh::lean_inc(v_val_5531_);
        leanh::lean_dec_ref_known(v___x_5530_, 1);
        return v_val_5531_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLED___redArg___boxed(
    mut v_cmp_5532_: *mut leanh::LeanObject,
    mut v_t_5533_: *mut leanh::LeanObject,
    mut v_k_5534_: *mut leanh::LeanObject,
    mut v_fallback_5535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5536_ =
        l_Std_ExtDTreeMap_getKeyLED___redArg(v_cmp_5532_, v_t_5533_, v_k_5534_, v_fallback_5535_);
    leanh::lean_dec(v_fallback_5535_);
    return v_res_5536_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLED(
    mut v_00_u03b1_5537_: *mut leanh::LeanObject,
    mut v_00_u03b2_5538_: *mut leanh::LeanObject,
    mut v_cmp_5539_: *mut leanh::LeanObject,
    mut v_inst_5540_: *mut leanh::LeanObject,
    mut v_t_5541_: *mut leanh::LeanObject,
    mut v_k_5542_: *mut leanh::LeanObject,
    mut v_fallback_5543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5544_ = leanh::lean_box(0);
    v___x_5545_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_5539_,
        v_k_5542_,
        v___x_5544_,
        v_t_5541_,
    );
    if leanh::lean_obj_tag(v___x_5545_) == 0 {
        leanh::lean_inc(v_fallback_5543_);
        return v_fallback_5543_;
    } else {
        let mut v_val_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5546_ = leanh::lean_ctor_get(v___x_5545_, 0);
        leanh::lean_inc(v_val_5546_);
        leanh::lean_dec_ref_known(v___x_5545_, 1);
        return v_val_5546_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLED___boxed(
    mut v_00_u03b1_5547_: *mut leanh::LeanObject,
    mut v_00_u03b2_5548_: *mut leanh::LeanObject,
    mut v_cmp_5549_: *mut leanh::LeanObject,
    mut v_inst_5550_: *mut leanh::LeanObject,
    mut v_t_5551_: *mut leanh::LeanObject,
    mut v_k_5552_: *mut leanh::LeanObject,
    mut v_fallback_5553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5554_ = l_Std_ExtDTreeMap_getKeyLED(
        v_00_u03b1_5547_,
        v_00_u03b2_5548_,
        v_cmp_5549_,
        v_inst_5550_,
        v_t_5551_,
        v_k_5552_,
        v_fallback_5553_,
    );
    leanh::lean_dec(v_fallback_5553_);
    return v_res_5554_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLTD___redArg(
    mut v_cmp_5555_: *mut leanh::LeanObject,
    mut v_t_5556_: *mut leanh::LeanObject,
    mut v_k_5557_: *mut leanh::LeanObject,
    mut v_fallback_5558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5559_ = leanh::lean_box(0);
    v___x_5560_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_5555_,
        v_k_5557_,
        v___x_5559_,
        v_t_5556_,
    );
    if leanh::lean_obj_tag(v___x_5560_) == 0 {
        leanh::lean_inc(v_fallback_5558_);
        return v_fallback_5558_;
    } else {
        let mut v_val_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5561_ = leanh::lean_ctor_get(v___x_5560_, 0);
        leanh::lean_inc(v_val_5561_);
        leanh::lean_dec_ref_known(v___x_5560_, 1);
        return v_val_5561_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLTD___redArg___boxed(
    mut v_cmp_5562_: *mut leanh::LeanObject,
    mut v_t_5563_: *mut leanh::LeanObject,
    mut v_k_5564_: *mut leanh::LeanObject,
    mut v_fallback_5565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5566_ =
        l_Std_ExtDTreeMap_getKeyLTD___redArg(v_cmp_5562_, v_t_5563_, v_k_5564_, v_fallback_5565_);
    leanh::lean_dec(v_fallback_5565_);
    return v_res_5566_;
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLTD(
    mut v_00_u03b1_5567_: *mut leanh::LeanObject,
    mut v_00_u03b2_5568_: *mut leanh::LeanObject,
    mut v_cmp_5569_: *mut leanh::LeanObject,
    mut v_inst_5570_: *mut leanh::LeanObject,
    mut v_t_5571_: *mut leanh::LeanObject,
    mut v_k_5572_: *mut leanh::LeanObject,
    mut v_fallback_5573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5574_ = leanh::lean_box(0);
    v___x_5575_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_5569_,
        v_k_5572_,
        v___x_5574_,
        v_t_5571_,
    );
    if leanh::lean_obj_tag(v___x_5575_) == 0 {
        leanh::lean_inc(v_fallback_5573_);
        return v_fallback_5573_;
    } else {
        let mut v_val_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5576_ = leanh::lean_ctor_get(v___x_5575_, 0);
        leanh::lean_inc(v_val_5576_);
        leanh::lean_dec_ref_known(v___x_5575_, 1);
        return v_val_5576_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_getKeyLTD___boxed(
    mut v_00_u03b1_5577_: *mut leanh::LeanObject,
    mut v_00_u03b2_5578_: *mut leanh::LeanObject,
    mut v_cmp_5579_: *mut leanh::LeanObject,
    mut v_inst_5580_: *mut leanh::LeanObject,
    mut v_t_5581_: *mut leanh::LeanObject,
    mut v_k_5582_: *mut leanh::LeanObject,
    mut v_fallback_5583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5584_ = l_Std_ExtDTreeMap_getKeyLTD(
        v_00_u03b1_5577_,
        v_00_u03b2_5578_,
        v_cmp_5579_,
        v_inst_5580_,
        v_t_5581_,
        v_k_5582_,
        v_fallback_5583_,
    );
    leanh::lean_dec(v_fallback_5583_);
    return v_res_5584_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f___redArg(
    mut v_cmp_5585_: *mut leanh::LeanObject,
    mut v_t_5586_: *mut leanh::LeanObject,
    mut v_a_5587_: *mut leanh::LeanObject,
    mut v_b_5588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_5587_);
    leanh::lean_inc(v_t_5586_);
    leanh::lean_inc_ref(v_cmp_5585_);
    v___x_5589_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_5585_, v_t_5586_, v_a_5587_);
    if leanh::lean_obj_tag(v___x_5589_) == 0 {
        let mut v___x_5590_: u8 = 0;
        leanh::lean_inc(v_t_5586_);
        leanh::lean_inc(v_a_5587_);
        leanh::lean_inc_ref(v_cmp_5585_);
        v___x_5590_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5585_, v_a_5587_, v_t_5586_);
        if v___x_5590_ == 0 {
            let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5591_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_5585_,
                v_a_5587_,
                v_b_5588_,
                v_t_5586_,
            );
            v___x_5592_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5592_, 0, v___x_5589_);
            leanh::lean_ctor_set(v___x_5592_, 1, v___x_5591_);
            return v___x_5592_;
        } else {
            let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_5588_);
            leanh::lean_dec(v_a_5587_);
            leanh::lean_dec_ref(v_cmp_5585_);
            v___x_5593_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5593_, 0, v___x_5589_);
            leanh::lean_ctor_set(v___x_5593_, 1, v_t_5586_);
            return v___x_5593_;
        }
    } else {
        let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_5588_);
        leanh::lean_dec(v_a_5587_);
        leanh::lean_dec_ref(v_cmp_5585_);
        v___x_5594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5594_, 0, v___x_5589_);
        leanh::lean_ctor_set(v___x_5594_, 1, v_t_5586_);
        return v___x_5594_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_5595_: *mut leanh::LeanObject,
    mut v_cmp_5596_: *mut leanh::LeanObject,
    mut v_00_u03b2_5597_: *mut leanh::LeanObject,
    mut v_inst_5598_: *mut leanh::LeanObject,
    mut v_t_5599_: *mut leanh::LeanObject,
    mut v_a_5600_: *mut leanh::LeanObject,
    mut v_b_5601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_5600_);
    leanh::lean_inc(v_t_5599_);
    leanh::lean_inc_ref(v_cmp_5596_);
    v___x_5602_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_5596_, v_t_5599_, v_a_5600_);
    if leanh::lean_obj_tag(v___x_5602_) == 0 {
        let mut v___x_5603_: u8 = 0;
        leanh::lean_inc(v_t_5599_);
        leanh::lean_inc(v_a_5600_);
        leanh::lean_inc_ref(v_cmp_5596_);
        v___x_5603_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5596_, v_a_5600_, v_t_5599_);
        if v___x_5603_ == 0 {
            let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5604_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_5596_,
                v_a_5600_,
                v_b_5601_,
                v_t_5599_,
            );
            v___x_5605_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5605_, 0, v___x_5602_);
            leanh::lean_ctor_set(v___x_5605_, 1, v___x_5604_);
            return v___x_5605_;
        } else {
            let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_5601_);
            leanh::lean_dec(v_a_5600_);
            leanh::lean_dec_ref(v_cmp_5596_);
            v___x_5606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5606_, 0, v___x_5602_);
            leanh::lean_ctor_set(v___x_5606_, 1, v_t_5599_);
            return v___x_5606_;
        }
    } else {
        let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_b_5601_);
        leanh::lean_dec(v_a_5600_);
        leanh::lean_dec_ref(v_cmp_5596_);
        v___x_5607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5607_, 0, v___x_5602_);
        leanh::lean_ctor_set(v___x_5607_, 1, v_t_5599_);
        return v___x_5607_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get_x3f___redArg(
    mut v_cmp_5608_: *mut leanh::LeanObject,
    mut v_t_5609_: *mut leanh::LeanObject,
    mut v_a_5610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5611_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_5608_, v_t_5609_, v_a_5610_);
    return v___x_5611_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get_x3f(
    mut v_00_u03b1_5612_: *mut leanh::LeanObject,
    mut v_cmp_5613_: *mut leanh::LeanObject,
    mut v_00_u03b2_5614_: *mut leanh::LeanObject,
    mut v_inst_5615_: *mut leanh::LeanObject,
    mut v_t_5616_: *mut leanh::LeanObject,
    mut v_a_5617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5618_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_5613_, v_t_5616_, v_a_5617_);
    return v___x_5618_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get___redArg(
    mut v_cmp_5619_: *mut leanh::LeanObject,
    mut v_t_5620_: *mut leanh::LeanObject,
    mut v_a_5621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5622_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_5619_, v_t_5620_, v_a_5621_);
    return v___x_5622_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get(
    mut v_00_u03b1_5623_: *mut leanh::LeanObject,
    mut v_cmp_5624_: *mut leanh::LeanObject,
    mut v_00_u03b2_5625_: *mut leanh::LeanObject,
    mut v_inst_5626_: *mut leanh::LeanObject,
    mut v_t_5627_: *mut leanh::LeanObject,
    mut v_a_5628_: *mut leanh::LeanObject,
    mut v_h_5629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5630_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_5624_, v_t_5627_, v_a_5628_);
    return v___x_5630_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get_x21___redArg(
    mut v_cmp_5631_: *mut leanh::LeanObject,
    mut v_inst_5632_: *mut leanh::LeanObject,
    mut v_t_5633_: *mut leanh::LeanObject,
    mut v_a_5634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_5631_,
        v_inst_5632_,
        v_t_5633_,
        v_a_5634_,
    );
    return v___x_5635_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get_x21___redArg___boxed(
    mut v_cmp_5636_: *mut leanh::LeanObject,
    mut v_inst_5637_: *mut leanh::LeanObject,
    mut v_t_5638_: *mut leanh::LeanObject,
    mut v_a_5639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5640_ =
        l_Std_ExtDTreeMap_Const_get_x21___redArg(v_cmp_5636_, v_inst_5637_, v_t_5638_, v_a_5639_);
    leanh::lean_dec(v_inst_5637_);
    return v_res_5640_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get_x21(
    mut v_00_u03b1_5641_: *mut leanh::LeanObject,
    mut v_cmp_5642_: *mut leanh::LeanObject,
    mut v_00_u03b2_5643_: *mut leanh::LeanObject,
    mut v_inst_5644_: *mut leanh::LeanObject,
    mut v_inst_5645_: *mut leanh::LeanObject,
    mut v_t_5646_: *mut leanh::LeanObject,
    mut v_a_5647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5648_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_5642_,
        v_inst_5645_,
        v_t_5646_,
        v_a_5647_,
    );
    return v___x_5648_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_get_x21___boxed(
    mut v_00_u03b1_5649_: *mut leanh::LeanObject,
    mut v_cmp_5650_: *mut leanh::LeanObject,
    mut v_00_u03b2_5651_: *mut leanh::LeanObject,
    mut v_inst_5652_: *mut leanh::LeanObject,
    mut v_inst_5653_: *mut leanh::LeanObject,
    mut v_t_5654_: *mut leanh::LeanObject,
    mut v_a_5655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5656_ = l_Std_ExtDTreeMap_Const_get_x21(
        v_00_u03b1_5649_,
        v_cmp_5650_,
        v_00_u03b2_5651_,
        v_inst_5652_,
        v_inst_5653_,
        v_t_5654_,
        v_a_5655_,
    );
    leanh::lean_dec(v_inst_5653_);
    return v_res_5656_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getD___redArg(
    mut v_cmp_5657_: *mut leanh::LeanObject,
    mut v_t_5658_: *mut leanh::LeanObject,
    mut v_a_5659_: *mut leanh::LeanObject,
    mut v_fallback_5660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5661_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_5657_,
        v_t_5658_,
        v_a_5659_,
        v_fallback_5660_,
    );
    return v___x_5661_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getD___redArg___boxed(
    mut v_cmp_5662_: *mut leanh::LeanObject,
    mut v_t_5663_: *mut leanh::LeanObject,
    mut v_a_5664_: *mut leanh::LeanObject,
    mut v_fallback_5665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5666_ =
        l_Std_ExtDTreeMap_Const_getD___redArg(v_cmp_5662_, v_t_5663_, v_a_5664_, v_fallback_5665_);
    leanh::lean_dec(v_fallback_5665_);
    return v_res_5666_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getD(
    mut v_00_u03b1_5667_: *mut leanh::LeanObject,
    mut v_cmp_5668_: *mut leanh::LeanObject,
    mut v_00_u03b2_5669_: *mut leanh::LeanObject,
    mut v_inst_5670_: *mut leanh::LeanObject,
    mut v_t_5671_: *mut leanh::LeanObject,
    mut v_a_5672_: *mut leanh::LeanObject,
    mut v_fallback_5673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5674_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_5668_,
        v_t_5671_,
        v_a_5672_,
        v_fallback_5673_,
    );
    return v___x_5674_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getD___boxed(
    mut v_00_u03b1_5675_: *mut leanh::LeanObject,
    mut v_cmp_5676_: *mut leanh::LeanObject,
    mut v_00_u03b2_5677_: *mut leanh::LeanObject,
    mut v_inst_5678_: *mut leanh::LeanObject,
    mut v_t_5679_: *mut leanh::LeanObject,
    mut v_a_5680_: *mut leanh::LeanObject,
    mut v_fallback_5681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5682_ = l_Std_ExtDTreeMap_Const_getD(
        v_00_u03b1_5675_,
        v_cmp_5676_,
        v_00_u03b2_5677_,
        v_inst_5678_,
        v_t_5679_,
        v_a_5680_,
        v_fallback_5681_,
    );
    leanh::lean_dec(v_fallback_5681_);
    return v_res_5682_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(
    mut v_t_5683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5684_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_5683_);
    return v___x_5684_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg___boxed(
    mut v_t_5685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5686_ = l_Std_ExtDTreeMap_Const_minEntry_x3f___redArg(v_t_5685_);
    leanh::lean_dec(v_t_5685_);
    return v_res_5686_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x3f(
    mut v_00_u03b1_5687_: *mut leanh::LeanObject,
    mut v_cmp_5688_: *mut leanh::LeanObject,
    mut v_00_u03b2_5689_: *mut leanh::LeanObject,
    mut v_inst_5690_: *mut leanh::LeanObject,
    mut v_t_5691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5692_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_5691_);
    return v___x_5692_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x3f___boxed(
    mut v_00_u03b1_5693_: *mut leanh::LeanObject,
    mut v_cmp_5694_: *mut leanh::LeanObject,
    mut v_00_u03b2_5695_: *mut leanh::LeanObject,
    mut v_inst_5696_: *mut leanh::LeanObject,
    mut v_t_5697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5698_ = l_Std_ExtDTreeMap_Const_minEntry_x3f(
        v_00_u03b1_5693_,
        v_cmp_5694_,
        v_00_u03b2_5695_,
        v_inst_5696_,
        v_t_5697_,
    );
    leanh::lean_dec(v_t_5697_);
    leanh::lean_dec_ref(v_cmp_5694_);
    return v_res_5698_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry___redArg(
    mut v_t_5699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_5699_);
    return v___x_5700_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry___redArg___boxed(
    mut v_t_5701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5702_ = l_Std_ExtDTreeMap_Const_minEntry___redArg(v_t_5701_);
    leanh::lean_dec(v_t_5701_);
    return v_res_5702_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry(
    mut v_00_u03b1_5703_: *mut leanh::LeanObject,
    mut v_cmp_5704_: *mut leanh::LeanObject,
    mut v_00_u03b2_5705_: *mut leanh::LeanObject,
    mut v_inst_5706_: *mut leanh::LeanObject,
    mut v_t_5707_: *mut leanh::LeanObject,
    mut v_h_5708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5709_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_5707_);
    return v___x_5709_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry___boxed(
    mut v_00_u03b1_5710_: *mut leanh::LeanObject,
    mut v_cmp_5711_: *mut leanh::LeanObject,
    mut v_00_u03b2_5712_: *mut leanh::LeanObject,
    mut v_inst_5713_: *mut leanh::LeanObject,
    mut v_t_5714_: *mut leanh::LeanObject,
    mut v_h_5715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5716_ = l_Std_ExtDTreeMap_Const_minEntry(
        v_00_u03b1_5710_,
        v_cmp_5711_,
        v_00_u03b2_5712_,
        v_inst_5713_,
        v_t_5714_,
        v_h_5715_,
    );
    leanh::lean_dec(v_t_5714_);
    leanh::lean_dec_ref(v_cmp_5711_);
    return v_res_5716_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(
    mut v_inst_5717_: *mut leanh::LeanObject,
    mut v_t_5718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5719_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_5717_, v_t_5718_);
    return v___x_5719_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x21___redArg___boxed(
    mut v_inst_5720_: *mut leanh::LeanObject,
    mut v_t_5721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5722_ = l_Std_ExtDTreeMap_Const_minEntry_x21___redArg(v_inst_5720_, v_t_5721_);
    leanh::lean_dec(v_t_5721_);
    leanh::lean_dec_ref(v_inst_5720_);
    return v_res_5722_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x21(
    mut v_00_u03b1_5723_: *mut leanh::LeanObject,
    mut v_cmp_5724_: *mut leanh::LeanObject,
    mut v_00_u03b2_5725_: *mut leanh::LeanObject,
    mut v_inst_5726_: *mut leanh::LeanObject,
    mut v_inst_5727_: *mut leanh::LeanObject,
    mut v_t_5728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5729_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_5727_, v_t_5728_);
    return v___x_5729_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntry_x21___boxed(
    mut v_00_u03b1_5730_: *mut leanh::LeanObject,
    mut v_cmp_5731_: *mut leanh::LeanObject,
    mut v_00_u03b2_5732_: *mut leanh::LeanObject,
    mut v_inst_5733_: *mut leanh::LeanObject,
    mut v_inst_5734_: *mut leanh::LeanObject,
    mut v_t_5735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5736_ = l_Std_ExtDTreeMap_Const_minEntry_x21(
        v_00_u03b1_5730_,
        v_cmp_5731_,
        v_00_u03b2_5732_,
        v_inst_5733_,
        v_inst_5734_,
        v_t_5735_,
    );
    leanh::lean_dec(v_t_5735_);
    leanh::lean_dec_ref(v_inst_5734_);
    leanh::lean_dec_ref(v_cmp_5731_);
    return v_res_5736_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntryD___redArg(
    mut v_t_5737_: *mut leanh::LeanObject,
    mut v_fallback_5738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5739_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_5737_, v_fallback_5738_);
    return v___x_5739_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntryD___redArg___boxed(
    mut v_t_5740_: *mut leanh::LeanObject,
    mut v_fallback_5741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5742_ = l_Std_ExtDTreeMap_Const_minEntryD___redArg(v_t_5740_, v_fallback_5741_);
    leanh::lean_dec_ref(v_fallback_5741_);
    leanh::lean_dec(v_t_5740_);
    return v_res_5742_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntryD(
    mut v_00_u03b1_5743_: *mut leanh::LeanObject,
    mut v_cmp_5744_: *mut leanh::LeanObject,
    mut v_00_u03b2_5745_: *mut leanh::LeanObject,
    mut v_inst_5746_: *mut leanh::LeanObject,
    mut v_t_5747_: *mut leanh::LeanObject,
    mut v_fallback_5748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5749_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_5747_, v_fallback_5748_);
    return v___x_5749_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_minEntryD___boxed(
    mut v_00_u03b1_5750_: *mut leanh::LeanObject,
    mut v_cmp_5751_: *mut leanh::LeanObject,
    mut v_00_u03b2_5752_: *mut leanh::LeanObject,
    mut v_inst_5753_: *mut leanh::LeanObject,
    mut v_t_5754_: *mut leanh::LeanObject,
    mut v_fallback_5755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5756_ = l_Std_ExtDTreeMap_Const_minEntryD(
        v_00_u03b1_5750_,
        v_cmp_5751_,
        v_00_u03b2_5752_,
        v_inst_5753_,
        v_t_5754_,
        v_fallback_5755_,
    );
    leanh::lean_dec_ref(v_fallback_5755_);
    leanh::lean_dec(v_t_5754_);
    leanh::lean_dec_ref(v_cmp_5751_);
    return v_res_5756_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(
    mut v_t_5757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5758_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_5757_);
    return v___x_5758_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg___boxed(
    mut v_t_5759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5760_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f___redArg(v_t_5759_);
    leanh::lean_dec(v_t_5759_);
    return v_res_5760_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x3f(
    mut v_00_u03b1_5761_: *mut leanh::LeanObject,
    mut v_cmp_5762_: *mut leanh::LeanObject,
    mut v_00_u03b2_5763_: *mut leanh::LeanObject,
    mut v_inst_5764_: *mut leanh::LeanObject,
    mut v_t_5765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5766_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_5765_);
    return v___x_5766_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x3f___boxed(
    mut v_00_u03b1_5767_: *mut leanh::LeanObject,
    mut v_cmp_5768_: *mut leanh::LeanObject,
    mut v_00_u03b2_5769_: *mut leanh::LeanObject,
    mut v_inst_5770_: *mut leanh::LeanObject,
    mut v_t_5771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5772_ = l_Std_ExtDTreeMap_Const_maxEntry_x3f(
        v_00_u03b1_5767_,
        v_cmp_5768_,
        v_00_u03b2_5769_,
        v_inst_5770_,
        v_t_5771_,
    );
    leanh::lean_dec(v_t_5771_);
    leanh::lean_dec_ref(v_cmp_5768_);
    return v_res_5772_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry___redArg(
    mut v_t_5773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5774_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_5773_);
    return v___x_5774_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry___redArg___boxed(
    mut v_t_5775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5776_ = l_Std_ExtDTreeMap_Const_maxEntry___redArg(v_t_5775_);
    leanh::lean_dec(v_t_5775_);
    return v_res_5776_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry(
    mut v_00_u03b1_5777_: *mut leanh::LeanObject,
    mut v_cmp_5778_: *mut leanh::LeanObject,
    mut v_00_u03b2_5779_: *mut leanh::LeanObject,
    mut v_inst_5780_: *mut leanh::LeanObject,
    mut v_t_5781_: *mut leanh::LeanObject,
    mut v_h_5782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5783_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_5781_);
    return v___x_5783_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry___boxed(
    mut v_00_u03b1_5784_: *mut leanh::LeanObject,
    mut v_cmp_5785_: *mut leanh::LeanObject,
    mut v_00_u03b2_5786_: *mut leanh::LeanObject,
    mut v_inst_5787_: *mut leanh::LeanObject,
    mut v_t_5788_: *mut leanh::LeanObject,
    mut v_h_5789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5790_ = l_Std_ExtDTreeMap_Const_maxEntry(
        v_00_u03b1_5784_,
        v_cmp_5785_,
        v_00_u03b2_5786_,
        v_inst_5787_,
        v_t_5788_,
        v_h_5789_,
    );
    leanh::lean_dec(v_t_5788_);
    leanh::lean_dec_ref(v_cmp_5785_);
    return v_res_5790_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(
    mut v_inst_5791_: *mut leanh::LeanObject,
    mut v_t_5792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5793_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_5791_, v_t_5792_);
    return v___x_5793_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg___boxed(
    mut v_inst_5794_: *mut leanh::LeanObject,
    mut v_t_5795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5796_ = l_Std_ExtDTreeMap_Const_maxEntry_x21___redArg(v_inst_5794_, v_t_5795_);
    leanh::lean_dec(v_t_5795_);
    leanh::lean_dec_ref(v_inst_5794_);
    return v_res_5796_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x21(
    mut v_00_u03b1_5797_: *mut leanh::LeanObject,
    mut v_cmp_5798_: *mut leanh::LeanObject,
    mut v_00_u03b2_5799_: *mut leanh::LeanObject,
    mut v_inst_5800_: *mut leanh::LeanObject,
    mut v_inst_5801_: *mut leanh::LeanObject,
    mut v_t_5802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5803_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_5801_, v_t_5802_);
    return v___x_5803_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntry_x21___boxed(
    mut v_00_u03b1_5804_: *mut leanh::LeanObject,
    mut v_cmp_5805_: *mut leanh::LeanObject,
    mut v_00_u03b2_5806_: *mut leanh::LeanObject,
    mut v_inst_5807_: *mut leanh::LeanObject,
    mut v_inst_5808_: *mut leanh::LeanObject,
    mut v_t_5809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5810_ = l_Std_ExtDTreeMap_Const_maxEntry_x21(
        v_00_u03b1_5804_,
        v_cmp_5805_,
        v_00_u03b2_5806_,
        v_inst_5807_,
        v_inst_5808_,
        v_t_5809_,
    );
    leanh::lean_dec(v_t_5809_);
    leanh::lean_dec_ref(v_inst_5808_);
    leanh::lean_dec_ref(v_cmp_5805_);
    return v_res_5810_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntryD___redArg(
    mut v_t_5811_: *mut leanh::LeanObject,
    mut v_fallback_5812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5813_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_5811_, v_fallback_5812_);
    return v___x_5813_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntryD___redArg___boxed(
    mut v_t_5814_: *mut leanh::LeanObject,
    mut v_fallback_5815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5816_ = l_Std_ExtDTreeMap_Const_maxEntryD___redArg(v_t_5814_, v_fallback_5815_);
    leanh::lean_dec_ref(v_fallback_5815_);
    leanh::lean_dec(v_t_5814_);
    return v_res_5816_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntryD(
    mut v_00_u03b1_5817_: *mut leanh::LeanObject,
    mut v_cmp_5818_: *mut leanh::LeanObject,
    mut v_00_u03b2_5819_: *mut leanh::LeanObject,
    mut v_inst_5820_: *mut leanh::LeanObject,
    mut v_t_5821_: *mut leanh::LeanObject,
    mut v_fallback_5822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5823_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_5821_, v_fallback_5822_);
    return v___x_5823_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_maxEntryD___boxed(
    mut v_00_u03b1_5824_: *mut leanh::LeanObject,
    mut v_cmp_5825_: *mut leanh::LeanObject,
    mut v_00_u03b2_5826_: *mut leanh::LeanObject,
    mut v_inst_5827_: *mut leanh::LeanObject,
    mut v_t_5828_: *mut leanh::LeanObject,
    mut v_fallback_5829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5830_ = l_Std_ExtDTreeMap_Const_maxEntryD(
        v_00_u03b1_5824_,
        v_cmp_5825_,
        v_00_u03b2_5826_,
        v_inst_5827_,
        v_t_5828_,
        v_fallback_5829_,
    );
    leanh::lean_dec_ref(v_fallback_5829_);
    leanh::lean_dec(v_t_5828_);
    leanh::lean_dec_ref(v_cmp_5825_);
    return v_res_5830_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(
    mut v_t_5831_: *mut leanh::LeanObject,
    mut v_n_5832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5833_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_5831_, v_n_5832_);
    return v___x_5833_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg___boxed(
    mut v_t_5834_: *mut leanh::LeanObject,
    mut v_n_5835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5836_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___redArg(v_t_5834_, v_n_5835_);
    leanh::lean_dec(v_t_5834_);
    return v_res_5836_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(
    mut v_00_u03b1_5837_: *mut leanh::LeanObject,
    mut v_cmp_5838_: *mut leanh::LeanObject,
    mut v_00_u03b2_5839_: *mut leanh::LeanObject,
    mut v_inst_5840_: *mut leanh::LeanObject,
    mut v_t_5841_: *mut leanh::LeanObject,
    mut v_n_5842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5843_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_5841_, v_n_5842_);
    return v___x_5843_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_5844_: *mut leanh::LeanObject,
    mut v_cmp_5845_: *mut leanh::LeanObject,
    mut v_00_u03b2_5846_: *mut leanh::LeanObject,
    mut v_inst_5847_: *mut leanh::LeanObject,
    mut v_t_5848_: *mut leanh::LeanObject,
    mut v_n_5849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5850_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x3f(
        v_00_u03b1_5844_,
        v_cmp_5845_,
        v_00_u03b2_5846_,
        v_inst_5847_,
        v_t_5848_,
        v_n_5849_,
    );
    leanh::lean_dec(v_t_5848_);
    leanh::lean_dec_ref(v_cmp_5845_);
    return v_res_5850_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(
    mut v_t_5851_: *mut leanh::LeanObject,
    mut v_n_5852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5853_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_5851_, v_n_5852_);
    return v___x_5853_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx___redArg___boxed(
    mut v_t_5854_: *mut leanh::LeanObject,
    mut v_n_5855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5856_ = l_Std_ExtDTreeMap_Const_entryAtIdx___redArg(v_t_5854_, v_n_5855_);
    leanh::lean_dec(v_t_5854_);
    return v_res_5856_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx(
    mut v_00_u03b1_5857_: *mut leanh::LeanObject,
    mut v_cmp_5858_: *mut leanh::LeanObject,
    mut v_00_u03b2_5859_: *mut leanh::LeanObject,
    mut v_inst_5860_: *mut leanh::LeanObject,
    mut v_t_5861_: *mut leanh::LeanObject,
    mut v_n_5862_: *mut leanh::LeanObject,
    mut v_h_5863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5864_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_5861_, v_n_5862_);
    return v___x_5864_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx___boxed(
    mut v_00_u03b1_5865_: *mut leanh::LeanObject,
    mut v_cmp_5866_: *mut leanh::LeanObject,
    mut v_00_u03b2_5867_: *mut leanh::LeanObject,
    mut v_inst_5868_: *mut leanh::LeanObject,
    mut v_t_5869_: *mut leanh::LeanObject,
    mut v_n_5870_: *mut leanh::LeanObject,
    mut v_h_5871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5872_ = l_Std_ExtDTreeMap_Const_entryAtIdx(
        v_00_u03b1_5865_,
        v_cmp_5866_,
        v_00_u03b2_5867_,
        v_inst_5868_,
        v_t_5869_,
        v_n_5870_,
        v_h_5871_,
    );
    leanh::lean_dec(v_t_5869_);
    leanh::lean_dec_ref(v_cmp_5866_);
    return v_res_5872_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(
    mut v_inst_5873_: *mut leanh::LeanObject,
    mut v_t_5874_: *mut leanh::LeanObject,
    mut v_n_5875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5876_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_5873_,
        v_t_5874_,
        v_n_5875_,
    );
    return v___x_5876_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg___boxed(
    mut v_inst_5877_: *mut leanh::LeanObject,
    mut v_t_5878_: *mut leanh::LeanObject,
    mut v_n_5879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5880_ =
        l_Std_ExtDTreeMap_Const_entryAtIdx_x21___redArg(v_inst_5877_, v_t_5878_, v_n_5879_);
    leanh::lean_dec(v_t_5878_);
    leanh::lean_dec_ref(v_inst_5877_);
    return v_res_5880_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x21(
    mut v_00_u03b1_5881_: *mut leanh::LeanObject,
    mut v_cmp_5882_: *mut leanh::LeanObject,
    mut v_00_u03b2_5883_: *mut leanh::LeanObject,
    mut v_inst_5884_: *mut leanh::LeanObject,
    mut v_inst_5885_: *mut leanh::LeanObject,
    mut v_t_5886_: *mut leanh::LeanObject,
    mut v_n_5887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5888_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_5885_,
        v_t_5886_,
        v_n_5887_,
    );
    return v___x_5888_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdx_x21___boxed(
    mut v_00_u03b1_5889_: *mut leanh::LeanObject,
    mut v_cmp_5890_: *mut leanh::LeanObject,
    mut v_00_u03b2_5891_: *mut leanh::LeanObject,
    mut v_inst_5892_: *mut leanh::LeanObject,
    mut v_inst_5893_: *mut leanh::LeanObject,
    mut v_t_5894_: *mut leanh::LeanObject,
    mut v_n_5895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5896_ = l_Std_ExtDTreeMap_Const_entryAtIdx_x21(
        v_00_u03b1_5889_,
        v_cmp_5890_,
        v_00_u03b2_5891_,
        v_inst_5892_,
        v_inst_5893_,
        v_t_5894_,
        v_n_5895_,
    );
    leanh::lean_dec(v_t_5894_);
    leanh::lean_dec_ref(v_inst_5893_);
    leanh::lean_dec_ref(v_cmp_5890_);
    return v_res_5896_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(
    mut v_t_5897_: *mut leanh::LeanObject,
    mut v_n_5898_: *mut leanh::LeanObject,
    mut v_fallback_5899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5900_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_5897_,
        v_n_5898_,
        v_fallback_5899_,
    );
    return v___x_5900_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg___boxed(
    mut v_t_5901_: *mut leanh::LeanObject,
    mut v_n_5902_: *mut leanh::LeanObject,
    mut v_fallback_5903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5904_ =
        l_Std_ExtDTreeMap_Const_entryAtIdxD___redArg(v_t_5901_, v_n_5902_, v_fallback_5903_);
    leanh::lean_dec_ref(v_fallback_5903_);
    leanh::lean_dec(v_t_5901_);
    return v_res_5904_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdxD(
    mut v_00_u03b1_5905_: *mut leanh::LeanObject,
    mut v_cmp_5906_: *mut leanh::LeanObject,
    mut v_00_u03b2_5907_: *mut leanh::LeanObject,
    mut v_inst_5908_: *mut leanh::LeanObject,
    mut v_t_5909_: *mut leanh::LeanObject,
    mut v_n_5910_: *mut leanh::LeanObject,
    mut v_fallback_5911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5912_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_5909_,
        v_n_5910_,
        v_fallback_5911_,
    );
    return v___x_5912_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_entryAtIdxD___boxed(
    mut v_00_u03b1_5913_: *mut leanh::LeanObject,
    mut v_cmp_5914_: *mut leanh::LeanObject,
    mut v_00_u03b2_5915_: *mut leanh::LeanObject,
    mut v_inst_5916_: *mut leanh::LeanObject,
    mut v_t_5917_: *mut leanh::LeanObject,
    mut v_n_5918_: *mut leanh::LeanObject,
    mut v_fallback_5919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5920_ = l_Std_ExtDTreeMap_Const_entryAtIdxD(
        v_00_u03b1_5913_,
        v_cmp_5914_,
        v_00_u03b2_5915_,
        v_inst_5916_,
        v_t_5917_,
        v_n_5918_,
        v_fallback_5919_,
    );
    leanh::lean_dec_ref(v_fallback_5919_);
    leanh::lean_dec(v_t_5917_);
    leanh::lean_dec_ref(v_cmp_5914_);
    return v_res_5920_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE_x3f___redArg(
    mut v_cmp_5921_: *mut leanh::LeanObject,
    mut v_t_5922_: *mut leanh::LeanObject,
    mut v_k_5923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5924_ = leanh::lean_box(0);
    v___x_5925_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_5921_,
        v_k_5923_,
        v___x_5924_,
        v_t_5922_,
    );
    return v___x_5925_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE_x3f(
    mut v_00_u03b1_5926_: *mut leanh::LeanObject,
    mut v_cmp_5927_: *mut leanh::LeanObject,
    mut v_00_u03b2_5928_: *mut leanh::LeanObject,
    mut v_inst_5929_: *mut leanh::LeanObject,
    mut v_t_5930_: *mut leanh::LeanObject,
    mut v_k_5931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5932_ = leanh::lean_box(0);
    v___x_5933_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_5927_,
        v_k_5931_,
        v___x_5932_,
        v_t_5930_,
    );
    return v___x_5933_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT_x3f___redArg(
    mut v_cmp_5934_: *mut leanh::LeanObject,
    mut v_t_5935_: *mut leanh::LeanObject,
    mut v_k_5936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5937_ = leanh::lean_box(0);
    v___x_5938_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_5934_,
        v_k_5936_,
        v___x_5937_,
        v_t_5935_,
    );
    return v___x_5938_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT_x3f(
    mut v_00_u03b1_5939_: *mut leanh::LeanObject,
    mut v_cmp_5940_: *mut leanh::LeanObject,
    mut v_00_u03b2_5941_: *mut leanh::LeanObject,
    mut v_inst_5942_: *mut leanh::LeanObject,
    mut v_t_5943_: *mut leanh::LeanObject,
    mut v_k_5944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5945_ = leanh::lean_box(0);
    v___x_5946_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_5940_,
        v_k_5944_,
        v___x_5945_,
        v_t_5943_,
    );
    return v___x_5946_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE_x3f___redArg(
    mut v_cmp_5947_: *mut leanh::LeanObject,
    mut v_t_5948_: *mut leanh::LeanObject,
    mut v_k_5949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5950_ = leanh::lean_box(0);
    v___x_5951_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_5947_,
        v_k_5949_,
        v___x_5950_,
        v_t_5948_,
    );
    return v___x_5951_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE_x3f(
    mut v_00_u03b1_5952_: *mut leanh::LeanObject,
    mut v_cmp_5953_: *mut leanh::LeanObject,
    mut v_00_u03b2_5954_: *mut leanh::LeanObject,
    mut v_inst_5955_: *mut leanh::LeanObject,
    mut v_t_5956_: *mut leanh::LeanObject,
    mut v_k_5957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5958_ = leanh::lean_box(0);
    v___x_5959_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_5953_,
        v_k_5957_,
        v___x_5958_,
        v_t_5956_,
    );
    return v___x_5959_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT_x3f___redArg(
    mut v_cmp_5960_: *mut leanh::LeanObject,
    mut v_t_5961_: *mut leanh::LeanObject,
    mut v_k_5962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5963_ = leanh::lean_box(0);
    v___x_5964_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_5960_,
        v_k_5962_,
        v___x_5963_,
        v_t_5961_,
    );
    return v___x_5964_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT_x3f(
    mut v_00_u03b1_5965_: *mut leanh::LeanObject,
    mut v_cmp_5966_: *mut leanh::LeanObject,
    mut v_00_u03b2_5967_: *mut leanh::LeanObject,
    mut v_inst_5968_: *mut leanh::LeanObject,
    mut v_t_5969_: *mut leanh::LeanObject,
    mut v_k_5970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5971_ = leanh::lean_box(0);
    v___x_5972_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_5966_,
        v_k_5970_,
        v___x_5971_,
        v_t_5969_,
    );
    return v___x_5972_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE___redArg(
    mut v_cmp_5973_: *mut leanh::LeanObject,
    mut v_t_5974_: *mut leanh::LeanObject,
    mut v_k_5975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5976_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_5973_, v_k_5975_, v_t_5974_);
    return v___x_5976_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE(
    mut v_00_u03b1_5977_: *mut leanh::LeanObject,
    mut v_cmp_5978_: *mut leanh::LeanObject,
    mut v_00_u03b2_5979_: *mut leanh::LeanObject,
    mut v_inst_5980_: *mut leanh::LeanObject,
    mut v_t_5981_: *mut leanh::LeanObject,
    mut v_k_5982_: *mut leanh::LeanObject,
    mut v_h_5983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5984_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_5978_, v_k_5982_, v_t_5981_);
    return v___x_5984_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT___redArg(
    mut v_cmp_5985_: *mut leanh::LeanObject,
    mut v_t_5986_: *mut leanh::LeanObject,
    mut v_k_5987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5988_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_5985_, v_k_5987_, v_t_5986_);
    return v___x_5988_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT(
    mut v_00_u03b1_5989_: *mut leanh::LeanObject,
    mut v_cmp_5990_: *mut leanh::LeanObject,
    mut v_00_u03b2_5991_: *mut leanh::LeanObject,
    mut v_inst_5992_: *mut leanh::LeanObject,
    mut v_t_5993_: *mut leanh::LeanObject,
    mut v_k_5994_: *mut leanh::LeanObject,
    mut v_h_5995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5996_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_5990_, v_k_5994_, v_t_5993_);
    return v___x_5996_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE___redArg(
    mut v_cmp_5997_: *mut leanh::LeanObject,
    mut v_t_5998_: *mut leanh::LeanObject,
    mut v_k_5999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6000_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_5997_, v_k_5999_, v_t_5998_);
    return v___x_6000_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE(
    mut v_00_u03b1_6001_: *mut leanh::LeanObject,
    mut v_cmp_6002_: *mut leanh::LeanObject,
    mut v_00_u03b2_6003_: *mut leanh::LeanObject,
    mut v_inst_6004_: *mut leanh::LeanObject,
    mut v_t_6005_: *mut leanh::LeanObject,
    mut v_k_6006_: *mut leanh::LeanObject,
    mut v_h_6007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6008_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_6002_, v_k_6006_, v_t_6005_);
    return v___x_6008_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT___redArg(
    mut v_cmp_6009_: *mut leanh::LeanObject,
    mut v_t_6010_: *mut leanh::LeanObject,
    mut v_k_6011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6012_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_6009_, v_k_6011_, v_t_6010_);
    return v___x_6012_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT(
    mut v_00_u03b1_6013_: *mut leanh::LeanObject,
    mut v_cmp_6014_: *mut leanh::LeanObject,
    mut v_00_u03b2_6015_: *mut leanh::LeanObject,
    mut v_inst_6016_: *mut leanh::LeanObject,
    mut v_t_6017_: *mut leanh::LeanObject,
    mut v_k_6018_: *mut leanh::LeanObject,
    mut v_h_6019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6020_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_6014_, v_k_6018_, v_t_6017_);
    return v___x_6020_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(
    mut v_cmp_6021_: *mut leanh::LeanObject,
    mut v_inst_6022_: *mut leanh::LeanObject,
    mut v_t_6023_: *mut leanh::LeanObject,
    mut v_k_6024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6025_ = leanh::lean_box(0);
    v___x_6026_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6021_,
        v_k_6024_,
        v___x_6025_,
        v_t_6023_,
    );
    if leanh::lean_obj_tag(v___x_6026_) == 0 {
        let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6027_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6028_ = l_panic___redArg(v_inst_6022_, v___x_6027_);
        return v___x_6028_;
    } else {
        let mut v_val_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6029_ = leanh::lean_ctor_get(v___x_6026_, 0);
        leanh::lean_inc(v_val_6029_);
        leanh::lean_dec_ref_known(v___x_6026_, 1);
        return v_val_6029_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg___boxed(
    mut v_cmp_6030_: *mut leanh::LeanObject,
    mut v_inst_6031_: *mut leanh::LeanObject,
    mut v_t_6032_: *mut leanh::LeanObject,
    mut v_k_6033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6034_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21___redArg(
        v_cmp_6030_,
        v_inst_6031_,
        v_t_6032_,
        v_k_6033_,
    );
    leanh::lean_dec_ref(v_inst_6031_);
    return v_res_6034_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE_x21(
    mut v_00_u03b1_6035_: *mut leanh::LeanObject,
    mut v_cmp_6036_: *mut leanh::LeanObject,
    mut v_00_u03b2_6037_: *mut leanh::LeanObject,
    mut v_inst_6038_: *mut leanh::LeanObject,
    mut v_inst_6039_: *mut leanh::LeanObject,
    mut v_t_6040_: *mut leanh::LeanObject,
    mut v_k_6041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6042_ = leanh::lean_box(0);
    v___x_6043_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6036_,
        v_k_6041_,
        v___x_6042_,
        v_t_6040_,
    );
    if leanh::lean_obj_tag(v___x_6043_) == 0 {
        let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6044_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6045_ = l_panic___redArg(v_inst_6039_, v___x_6044_);
        return v___x_6045_;
    } else {
        let mut v_val_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6046_ = leanh::lean_ctor_get(v___x_6043_, 0);
        leanh::lean_inc(v_val_6046_);
        leanh::lean_dec_ref_known(v___x_6043_, 1);
        return v_val_6046_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGE_x21___boxed(
    mut v_00_u03b1_6047_: *mut leanh::LeanObject,
    mut v_cmp_6048_: *mut leanh::LeanObject,
    mut v_00_u03b2_6049_: *mut leanh::LeanObject,
    mut v_inst_6050_: *mut leanh::LeanObject,
    mut v_inst_6051_: *mut leanh::LeanObject,
    mut v_t_6052_: *mut leanh::LeanObject,
    mut v_k_6053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6054_ = l_Std_ExtDTreeMap_Const_getEntryGE_x21(
        v_00_u03b1_6047_,
        v_cmp_6048_,
        v_00_u03b2_6049_,
        v_inst_6050_,
        v_inst_6051_,
        v_t_6052_,
        v_k_6053_,
    );
    leanh::lean_dec_ref(v_inst_6051_);
    return v_res_6054_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(
    mut v_cmp_6055_: *mut leanh::LeanObject,
    mut v_inst_6056_: *mut leanh::LeanObject,
    mut v_t_6057_: *mut leanh::LeanObject,
    mut v_k_6058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6059_ = leanh::lean_box(0);
    v___x_6060_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6055_,
        v_k_6058_,
        v___x_6059_,
        v_t_6057_,
    );
    if leanh::lean_obj_tag(v___x_6060_) == 0 {
        let mut v___x_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6061_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6062_ = l_panic___redArg(v_inst_6056_, v___x_6061_);
        return v___x_6062_;
    } else {
        let mut v_val_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6063_ = leanh::lean_ctor_get(v___x_6060_, 0);
        leanh::lean_inc(v_val_6063_);
        leanh::lean_dec_ref_known(v___x_6060_, 1);
        return v_val_6063_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg___boxed(
    mut v_cmp_6064_: *mut leanh::LeanObject,
    mut v_inst_6065_: *mut leanh::LeanObject,
    mut v_t_6066_: *mut leanh::LeanObject,
    mut v_k_6067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6068_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21___redArg(
        v_cmp_6064_,
        v_inst_6065_,
        v_t_6066_,
        v_k_6067_,
    );
    leanh::lean_dec_ref(v_inst_6065_);
    return v_res_6068_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT_x21(
    mut v_00_u03b1_6069_: *mut leanh::LeanObject,
    mut v_cmp_6070_: *mut leanh::LeanObject,
    mut v_00_u03b2_6071_: *mut leanh::LeanObject,
    mut v_inst_6072_: *mut leanh::LeanObject,
    mut v_inst_6073_: *mut leanh::LeanObject,
    mut v_t_6074_: *mut leanh::LeanObject,
    mut v_k_6075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6076_ = leanh::lean_box(0);
    v___x_6077_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6070_,
        v_k_6075_,
        v___x_6076_,
        v_t_6074_,
    );
    if leanh::lean_obj_tag(v___x_6077_) == 0 {
        let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6078_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6079_ = l_panic___redArg(v_inst_6073_, v___x_6078_);
        return v___x_6079_;
    } else {
        let mut v_val_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6080_ = leanh::lean_ctor_get(v___x_6077_, 0);
        leanh::lean_inc(v_val_6080_);
        leanh::lean_dec_ref_known(v___x_6077_, 1);
        return v_val_6080_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGT_x21___boxed(
    mut v_00_u03b1_6081_: *mut leanh::LeanObject,
    mut v_cmp_6082_: *mut leanh::LeanObject,
    mut v_00_u03b2_6083_: *mut leanh::LeanObject,
    mut v_inst_6084_: *mut leanh::LeanObject,
    mut v_inst_6085_: *mut leanh::LeanObject,
    mut v_t_6086_: *mut leanh::LeanObject,
    mut v_k_6087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6088_ = l_Std_ExtDTreeMap_Const_getEntryGT_x21(
        v_00_u03b1_6081_,
        v_cmp_6082_,
        v_00_u03b2_6083_,
        v_inst_6084_,
        v_inst_6085_,
        v_t_6086_,
        v_k_6087_,
    );
    leanh::lean_dec_ref(v_inst_6085_);
    return v_res_6088_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(
    mut v_cmp_6089_: *mut leanh::LeanObject,
    mut v_inst_6090_: *mut leanh::LeanObject,
    mut v_t_6091_: *mut leanh::LeanObject,
    mut v_k_6092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6093_ = leanh::lean_box(0);
    v___x_6094_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6089_,
        v_k_6092_,
        v___x_6093_,
        v_t_6091_,
    );
    if leanh::lean_obj_tag(v___x_6094_) == 0 {
        let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6095_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6096_ = l_panic___redArg(v_inst_6090_, v___x_6095_);
        return v___x_6096_;
    } else {
        let mut v_val_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6097_ = leanh::lean_ctor_get(v___x_6094_, 0);
        leanh::lean_inc(v_val_6097_);
        leanh::lean_dec_ref_known(v___x_6094_, 1);
        return v_val_6097_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg___boxed(
    mut v_cmp_6098_: *mut leanh::LeanObject,
    mut v_inst_6099_: *mut leanh::LeanObject,
    mut v_t_6100_: *mut leanh::LeanObject,
    mut v_k_6101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6102_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21___redArg(
        v_cmp_6098_,
        v_inst_6099_,
        v_t_6100_,
        v_k_6101_,
    );
    leanh::lean_dec_ref(v_inst_6099_);
    return v_res_6102_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE_x21(
    mut v_00_u03b1_6103_: *mut leanh::LeanObject,
    mut v_cmp_6104_: *mut leanh::LeanObject,
    mut v_00_u03b2_6105_: *mut leanh::LeanObject,
    mut v_inst_6106_: *mut leanh::LeanObject,
    mut v_inst_6107_: *mut leanh::LeanObject,
    mut v_t_6108_: *mut leanh::LeanObject,
    mut v_k_6109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6110_ = leanh::lean_box(0);
    v___x_6111_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6104_,
        v_k_6109_,
        v___x_6110_,
        v_t_6108_,
    );
    if leanh::lean_obj_tag(v___x_6111_) == 0 {
        let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6112_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6113_ = l_panic___redArg(v_inst_6107_, v___x_6112_);
        return v___x_6113_;
    } else {
        let mut v_val_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6114_ = leanh::lean_ctor_get(v___x_6111_, 0);
        leanh::lean_inc(v_val_6114_);
        leanh::lean_dec_ref_known(v___x_6111_, 1);
        return v_val_6114_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLE_x21___boxed(
    mut v_00_u03b1_6115_: *mut leanh::LeanObject,
    mut v_cmp_6116_: *mut leanh::LeanObject,
    mut v_00_u03b2_6117_: *mut leanh::LeanObject,
    mut v_inst_6118_: *mut leanh::LeanObject,
    mut v_inst_6119_: *mut leanh::LeanObject,
    mut v_t_6120_: *mut leanh::LeanObject,
    mut v_k_6121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6122_ = l_Std_ExtDTreeMap_Const_getEntryLE_x21(
        v_00_u03b1_6115_,
        v_cmp_6116_,
        v_00_u03b2_6117_,
        v_inst_6118_,
        v_inst_6119_,
        v_t_6120_,
        v_k_6121_,
    );
    leanh::lean_dec_ref(v_inst_6119_);
    return v_res_6122_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(
    mut v_cmp_6123_: *mut leanh::LeanObject,
    mut v_inst_6124_: *mut leanh::LeanObject,
    mut v_t_6125_: *mut leanh::LeanObject,
    mut v_k_6126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6127_ = leanh::lean_box(0);
    v___x_6128_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6123_,
        v_k_6126_,
        v___x_6127_,
        v_t_6125_,
    );
    if leanh::lean_obj_tag(v___x_6128_) == 0 {
        let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6129_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6130_ = l_panic___redArg(v_inst_6124_, v___x_6129_);
        return v___x_6130_;
    } else {
        let mut v_val_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6131_ = leanh::lean_ctor_get(v___x_6128_, 0);
        leanh::lean_inc(v_val_6131_);
        leanh::lean_dec_ref_known(v___x_6128_, 1);
        return v_val_6131_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg___boxed(
    mut v_cmp_6132_: *mut leanh::LeanObject,
    mut v_inst_6133_: *mut leanh::LeanObject,
    mut v_t_6134_: *mut leanh::LeanObject,
    mut v_k_6135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6136_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21___redArg(
        v_cmp_6132_,
        v_inst_6133_,
        v_t_6134_,
        v_k_6135_,
    );
    leanh::lean_dec_ref(v_inst_6133_);
    return v_res_6136_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT_x21(
    mut v_00_u03b1_6137_: *mut leanh::LeanObject,
    mut v_cmp_6138_: *mut leanh::LeanObject,
    mut v_00_u03b2_6139_: *mut leanh::LeanObject,
    mut v_inst_6140_: *mut leanh::LeanObject,
    mut v_inst_6141_: *mut leanh::LeanObject,
    mut v_t_6142_: *mut leanh::LeanObject,
    mut v_k_6143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6144_ = leanh::lean_box(0);
    v___x_6145_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6138_,
        v_k_6143_,
        v___x_6144_,
        v_t_6142_,
    );
    if leanh::lean_obj_tag(v___x_6145_) == 0 {
        let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6146_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_ExtDTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6147_ = l_panic___redArg(v_inst_6141_, v___x_6146_);
        return v___x_6147_;
    } else {
        let mut v_val_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6148_ = leanh::lean_ctor_get(v___x_6145_, 0);
        leanh::lean_inc(v_val_6148_);
        leanh::lean_dec_ref_known(v___x_6145_, 1);
        return v_val_6148_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLT_x21___boxed(
    mut v_00_u03b1_6149_: *mut leanh::LeanObject,
    mut v_cmp_6150_: *mut leanh::LeanObject,
    mut v_00_u03b2_6151_: *mut leanh::LeanObject,
    mut v_inst_6152_: *mut leanh::LeanObject,
    mut v_inst_6153_: *mut leanh::LeanObject,
    mut v_t_6154_: *mut leanh::LeanObject,
    mut v_k_6155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6156_ = l_Std_ExtDTreeMap_Const_getEntryLT_x21(
        v_00_u03b1_6149_,
        v_cmp_6150_,
        v_00_u03b2_6151_,
        v_inst_6152_,
        v_inst_6153_,
        v_t_6154_,
        v_k_6155_,
    );
    leanh::lean_dec_ref(v_inst_6153_);
    return v_res_6156_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGED___redArg(
    mut v_cmp_6157_: *mut leanh::LeanObject,
    mut v_t_6158_: *mut leanh::LeanObject,
    mut v_k_6159_: *mut leanh::LeanObject,
    mut v_fallback_6160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6161_ = leanh::lean_box(0);
    v___x_6162_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6157_,
        v_k_6159_,
        v___x_6161_,
        v_t_6158_,
    );
    if leanh::lean_obj_tag(v___x_6162_) == 0 {
        leanh::lean_inc_ref(v_fallback_6160_);
        return v_fallback_6160_;
    } else {
        let mut v_val_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6163_ = leanh::lean_ctor_get(v___x_6162_, 0);
        leanh::lean_inc(v_val_6163_);
        leanh::lean_dec_ref_known(v___x_6162_, 1);
        return v_val_6163_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGED___redArg___boxed(
    mut v_cmp_6164_: *mut leanh::LeanObject,
    mut v_t_6165_: *mut leanh::LeanObject,
    mut v_k_6166_: *mut leanh::LeanObject,
    mut v_fallback_6167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6168_ = l_Std_ExtDTreeMap_Const_getEntryGED___redArg(
        v_cmp_6164_,
        v_t_6165_,
        v_k_6166_,
        v_fallback_6167_,
    );
    leanh::lean_dec_ref(v_fallback_6167_);
    return v_res_6168_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGED(
    mut v_00_u03b1_6169_: *mut leanh::LeanObject,
    mut v_cmp_6170_: *mut leanh::LeanObject,
    mut v_00_u03b2_6171_: *mut leanh::LeanObject,
    mut v_inst_6172_: *mut leanh::LeanObject,
    mut v_t_6173_: *mut leanh::LeanObject,
    mut v_k_6174_: *mut leanh::LeanObject,
    mut v_fallback_6175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6176_ = leanh::lean_box(0);
    v___x_6177_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6170_,
        v_k_6174_,
        v___x_6176_,
        v_t_6173_,
    );
    if leanh::lean_obj_tag(v___x_6177_) == 0 {
        leanh::lean_inc_ref(v_fallback_6175_);
        return v_fallback_6175_;
    } else {
        let mut v_val_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6178_ = leanh::lean_ctor_get(v___x_6177_, 0);
        leanh::lean_inc(v_val_6178_);
        leanh::lean_dec_ref_known(v___x_6177_, 1);
        return v_val_6178_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGED___boxed(
    mut v_00_u03b1_6179_: *mut leanh::LeanObject,
    mut v_cmp_6180_: *mut leanh::LeanObject,
    mut v_00_u03b2_6181_: *mut leanh::LeanObject,
    mut v_inst_6182_: *mut leanh::LeanObject,
    mut v_t_6183_: *mut leanh::LeanObject,
    mut v_k_6184_: *mut leanh::LeanObject,
    mut v_fallback_6185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6186_ = l_Std_ExtDTreeMap_Const_getEntryGED(
        v_00_u03b1_6179_,
        v_cmp_6180_,
        v_00_u03b2_6181_,
        v_inst_6182_,
        v_t_6183_,
        v_k_6184_,
        v_fallback_6185_,
    );
    leanh::lean_dec_ref(v_fallback_6185_);
    return v_res_6186_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(
    mut v_cmp_6187_: *mut leanh::LeanObject,
    mut v_t_6188_: *mut leanh::LeanObject,
    mut v_k_6189_: *mut leanh::LeanObject,
    mut v_fallback_6190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6191_ = leanh::lean_box(0);
    v___x_6192_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6187_,
        v_k_6189_,
        v___x_6191_,
        v_t_6188_,
    );
    if leanh::lean_obj_tag(v___x_6192_) == 0 {
        leanh::lean_inc_ref(v_fallback_6190_);
        return v_fallback_6190_;
    } else {
        let mut v_val_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6193_ = leanh::lean_ctor_get(v___x_6192_, 0);
        leanh::lean_inc(v_val_6193_);
        leanh::lean_dec_ref_known(v___x_6192_, 1);
        return v_val_6193_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGTD___redArg___boxed(
    mut v_cmp_6194_: *mut leanh::LeanObject,
    mut v_t_6195_: *mut leanh::LeanObject,
    mut v_k_6196_: *mut leanh::LeanObject,
    mut v_fallback_6197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6198_ = l_Std_ExtDTreeMap_Const_getEntryGTD___redArg(
        v_cmp_6194_,
        v_t_6195_,
        v_k_6196_,
        v_fallback_6197_,
    );
    leanh::lean_dec_ref(v_fallback_6197_);
    return v_res_6198_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGTD(
    mut v_00_u03b1_6199_: *mut leanh::LeanObject,
    mut v_cmp_6200_: *mut leanh::LeanObject,
    mut v_00_u03b2_6201_: *mut leanh::LeanObject,
    mut v_inst_6202_: *mut leanh::LeanObject,
    mut v_t_6203_: *mut leanh::LeanObject,
    mut v_k_6204_: *mut leanh::LeanObject,
    mut v_fallback_6205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6206_ = leanh::lean_box(0);
    v___x_6207_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6200_,
        v_k_6204_,
        v___x_6206_,
        v_t_6203_,
    );
    if leanh::lean_obj_tag(v___x_6207_) == 0 {
        leanh::lean_inc_ref(v_fallback_6205_);
        return v_fallback_6205_;
    } else {
        let mut v_val_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6208_ = leanh::lean_ctor_get(v___x_6207_, 0);
        leanh::lean_inc(v_val_6208_);
        leanh::lean_dec_ref_known(v___x_6207_, 1);
        return v_val_6208_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryGTD___boxed(
    mut v_00_u03b1_6209_: *mut leanh::LeanObject,
    mut v_cmp_6210_: *mut leanh::LeanObject,
    mut v_00_u03b2_6211_: *mut leanh::LeanObject,
    mut v_inst_6212_: *mut leanh::LeanObject,
    mut v_t_6213_: *mut leanh::LeanObject,
    mut v_k_6214_: *mut leanh::LeanObject,
    mut v_fallback_6215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6216_ = l_Std_ExtDTreeMap_Const_getEntryGTD(
        v_00_u03b1_6209_,
        v_cmp_6210_,
        v_00_u03b2_6211_,
        v_inst_6212_,
        v_t_6213_,
        v_k_6214_,
        v_fallback_6215_,
    );
    leanh::lean_dec_ref(v_fallback_6215_);
    return v_res_6216_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLED___redArg(
    mut v_cmp_6217_: *mut leanh::LeanObject,
    mut v_t_6218_: *mut leanh::LeanObject,
    mut v_k_6219_: *mut leanh::LeanObject,
    mut v_fallback_6220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6221_ = leanh::lean_box(0);
    v___x_6222_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6217_,
        v_k_6219_,
        v___x_6221_,
        v_t_6218_,
    );
    if leanh::lean_obj_tag(v___x_6222_) == 0 {
        leanh::lean_inc_ref(v_fallback_6220_);
        return v_fallback_6220_;
    } else {
        let mut v_val_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6223_ = leanh::lean_ctor_get(v___x_6222_, 0);
        leanh::lean_inc(v_val_6223_);
        leanh::lean_dec_ref_known(v___x_6222_, 1);
        return v_val_6223_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLED___redArg___boxed(
    mut v_cmp_6224_: *mut leanh::LeanObject,
    mut v_t_6225_: *mut leanh::LeanObject,
    mut v_k_6226_: *mut leanh::LeanObject,
    mut v_fallback_6227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6228_ = l_Std_ExtDTreeMap_Const_getEntryLED___redArg(
        v_cmp_6224_,
        v_t_6225_,
        v_k_6226_,
        v_fallback_6227_,
    );
    leanh::lean_dec_ref(v_fallback_6227_);
    return v_res_6228_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLED(
    mut v_00_u03b1_6229_: *mut leanh::LeanObject,
    mut v_cmp_6230_: *mut leanh::LeanObject,
    mut v_00_u03b2_6231_: *mut leanh::LeanObject,
    mut v_inst_6232_: *mut leanh::LeanObject,
    mut v_t_6233_: *mut leanh::LeanObject,
    mut v_k_6234_: *mut leanh::LeanObject,
    mut v_fallback_6235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6236_ = leanh::lean_box(0);
    v___x_6237_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6230_,
        v_k_6234_,
        v___x_6236_,
        v_t_6233_,
    );
    if leanh::lean_obj_tag(v___x_6237_) == 0 {
        leanh::lean_inc_ref(v_fallback_6235_);
        return v_fallback_6235_;
    } else {
        let mut v_val_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6238_ = leanh::lean_ctor_get(v___x_6237_, 0);
        leanh::lean_inc(v_val_6238_);
        leanh::lean_dec_ref_known(v___x_6237_, 1);
        return v_val_6238_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLED___boxed(
    mut v_00_u03b1_6239_: *mut leanh::LeanObject,
    mut v_cmp_6240_: *mut leanh::LeanObject,
    mut v_00_u03b2_6241_: *mut leanh::LeanObject,
    mut v_inst_6242_: *mut leanh::LeanObject,
    mut v_t_6243_: *mut leanh::LeanObject,
    mut v_k_6244_: *mut leanh::LeanObject,
    mut v_fallback_6245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6246_ = l_Std_ExtDTreeMap_Const_getEntryLED(
        v_00_u03b1_6239_,
        v_cmp_6240_,
        v_00_u03b2_6241_,
        v_inst_6242_,
        v_t_6243_,
        v_k_6244_,
        v_fallback_6245_,
    );
    leanh::lean_dec_ref(v_fallback_6245_);
    return v_res_6246_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(
    mut v_cmp_6247_: *mut leanh::LeanObject,
    mut v_t_6248_: *mut leanh::LeanObject,
    mut v_k_6249_: *mut leanh::LeanObject,
    mut v_fallback_6250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6251_ = leanh::lean_box(0);
    v___x_6252_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6247_,
        v_k_6249_,
        v___x_6251_,
        v_t_6248_,
    );
    if leanh::lean_obj_tag(v___x_6252_) == 0 {
        leanh::lean_inc_ref(v_fallback_6250_);
        return v_fallback_6250_;
    } else {
        let mut v_val_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6253_ = leanh::lean_ctor_get(v___x_6252_, 0);
        leanh::lean_inc(v_val_6253_);
        leanh::lean_dec_ref_known(v___x_6252_, 1);
        return v_val_6253_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLTD___redArg___boxed(
    mut v_cmp_6254_: *mut leanh::LeanObject,
    mut v_t_6255_: *mut leanh::LeanObject,
    mut v_k_6256_: *mut leanh::LeanObject,
    mut v_fallback_6257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6258_ = l_Std_ExtDTreeMap_Const_getEntryLTD___redArg(
        v_cmp_6254_,
        v_t_6255_,
        v_k_6256_,
        v_fallback_6257_,
    );
    leanh::lean_dec_ref(v_fallback_6257_);
    return v_res_6258_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLTD(
    mut v_00_u03b1_6259_: *mut leanh::LeanObject,
    mut v_cmp_6260_: *mut leanh::LeanObject,
    mut v_00_u03b2_6261_: *mut leanh::LeanObject,
    mut v_inst_6262_: *mut leanh::LeanObject,
    mut v_t_6263_: *mut leanh::LeanObject,
    mut v_k_6264_: *mut leanh::LeanObject,
    mut v_fallback_6265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6266_ = leanh::lean_box(0);
    v___x_6267_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6260_,
        v_k_6264_,
        v___x_6266_,
        v_t_6263_,
    );
    if leanh::lean_obj_tag(v___x_6267_) == 0 {
        leanh::lean_inc_ref(v_fallback_6265_);
        return v_fallback_6265_;
    } else {
        let mut v_val_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6268_ = leanh::lean_ctor_get(v___x_6267_, 0);
        leanh::lean_inc(v_val_6268_);
        leanh::lean_dec_ref_known(v___x_6267_, 1);
        return v_val_6268_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_getEntryLTD___boxed(
    mut v_00_u03b1_6269_: *mut leanh::LeanObject,
    mut v_cmp_6270_: *mut leanh::LeanObject,
    mut v_00_u03b2_6271_: *mut leanh::LeanObject,
    mut v_inst_6272_: *mut leanh::LeanObject,
    mut v_t_6273_: *mut leanh::LeanObject,
    mut v_k_6274_: *mut leanh::LeanObject,
    mut v_fallback_6275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6276_ = l_Std_ExtDTreeMap_Const_getEntryLTD(
        v_00_u03b1_6269_,
        v_cmp_6270_,
        v_00_u03b2_6271_,
        v_inst_6272_,
        v_t_6273_,
        v_k_6274_,
        v_fallback_6275_,
    );
    leanh::lean_dec_ref(v_fallback_6275_);
    return v_res_6276_;
}
pub unsafe fn l_Std_ExtDTreeMap_filter___redArg(
    mut v_f_6277_: *mut leanh::LeanObject,
    mut v_t_6278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6279_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_6277_, v_t_6278_);
    return v___x_6279_;
}
pub unsafe fn l_Std_ExtDTreeMap_filter(
    mut v_00_u03b1_6280_: *mut leanh::LeanObject,
    mut v_00_u03b2_6281_: *mut leanh::LeanObject,
    mut v_cmp_6282_: *mut leanh::LeanObject,
    mut v_f_6283_: *mut leanh::LeanObject,
    mut v_t_6284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6285_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_6283_, v_t_6284_);
    return v___x_6285_;
}
pub unsafe fn l_Std_ExtDTreeMap_filter___boxed(
    mut v_00_u03b1_6286_: *mut leanh::LeanObject,
    mut v_00_u03b2_6287_: *mut leanh::LeanObject,
    mut v_cmp_6288_: *mut leanh::LeanObject,
    mut v_f_6289_: *mut leanh::LeanObject,
    mut v_t_6290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6291_ = l_Std_ExtDTreeMap_filter(
        v_00_u03b1_6286_,
        v_00_u03b2_6287_,
        v_cmp_6288_,
        v_f_6289_,
        v_t_6290_,
    );
    leanh::lean_dec_ref(v_cmp_6288_);
    return v_res_6291_;
}
pub unsafe fn l_Std_ExtDTreeMap_filterMap___redArg(
    mut v_f_6292_: *mut leanh::LeanObject,
    mut v_t_6293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6294_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_6292_, v_t_6293_);
    return v___x_6294_;
}
pub unsafe fn l_Std_ExtDTreeMap_filterMap(
    mut v_00_u03b1_6295_: *mut leanh::LeanObject,
    mut v_00_u03b2_6296_: *mut leanh::LeanObject,
    mut v_00_u03b3_6297_: *mut leanh::LeanObject,
    mut v_cmp_6298_: *mut leanh::LeanObject,
    mut v_f_6299_: *mut leanh::LeanObject,
    mut v_t_6300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6301_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_6299_, v_t_6300_);
    return v___x_6301_;
}
pub unsafe fn l_Std_ExtDTreeMap_filterMap___boxed(
    mut v_00_u03b1_6302_: *mut leanh::LeanObject,
    mut v_00_u03b2_6303_: *mut leanh::LeanObject,
    mut v_00_u03b3_6304_: *mut leanh::LeanObject,
    mut v_cmp_6305_: *mut leanh::LeanObject,
    mut v_f_6306_: *mut leanh::LeanObject,
    mut v_t_6307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6308_ = l_Std_ExtDTreeMap_filterMap(
        v_00_u03b1_6302_,
        v_00_u03b2_6303_,
        v_00_u03b3_6304_,
        v_cmp_6305_,
        v_f_6306_,
        v_t_6307_,
    );
    leanh::lean_dec_ref(v_cmp_6305_);
    return v_res_6308_;
}
pub unsafe fn l_Std_ExtDTreeMap_map___redArg(
    mut v_f_6309_: *mut leanh::LeanObject,
    mut v_t_6310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6311_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_6309_, v_t_6310_);
    return v___x_6311_;
}
pub unsafe fn l_Std_ExtDTreeMap_map(
    mut v_00_u03b1_6312_: *mut leanh::LeanObject,
    mut v_00_u03b2_6313_: *mut leanh::LeanObject,
    mut v_00_u03b3_6314_: *mut leanh::LeanObject,
    mut v_cmp_6315_: *mut leanh::LeanObject,
    mut v_f_6316_: *mut leanh::LeanObject,
    mut v_t_6317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6318_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_6316_, v_t_6317_);
    return v___x_6318_;
}
pub unsafe fn l_Std_ExtDTreeMap_map___boxed(
    mut v_00_u03b1_6319_: *mut leanh::LeanObject,
    mut v_00_u03b2_6320_: *mut leanh::LeanObject,
    mut v_00_u03b3_6321_: *mut leanh::LeanObject,
    mut v_cmp_6322_: *mut leanh::LeanObject,
    mut v_f_6323_: *mut leanh::LeanObject,
    mut v_t_6324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Std_ExtDTreeMap_map(
        v_00_u03b1_6319_,
        v_00_u03b2_6320_,
        v_00_u03b3_6321_,
        v_cmp_6322_,
        v_f_6323_,
        v_t_6324_,
    );
    leanh::lean_dec_ref(v_cmp_6322_);
    return v_res_6325_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldlM___redArg(
    mut v_inst_6326_: *mut leanh::LeanObject,
    mut v_f_6327_: *mut leanh::LeanObject,
    mut v_init_6328_: *mut leanh::LeanObject,
    mut v_t_6329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6330_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6326_,
        v_f_6327_,
        v_init_6328_,
        v_t_6329_,
    );
    return v___x_6330_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldlM(
    mut v_00_u03b1_6331_: *mut leanh::LeanObject,
    mut v_00_u03b2_6332_: *mut leanh::LeanObject,
    mut v_cmp_6333_: *mut leanh::LeanObject,
    mut v_00_u03b4_6334_: *mut leanh::LeanObject,
    mut v_m_6335_: *mut leanh::LeanObject,
    mut v_inst_6336_: *mut leanh::LeanObject,
    mut v_inst_6337_: *mut leanh::LeanObject,
    mut v_inst_6338_: *mut leanh::LeanObject,
    mut v_f_6339_: *mut leanh::LeanObject,
    mut v_init_6340_: *mut leanh::LeanObject,
    mut v_t_6341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6342_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6336_,
        v_f_6339_,
        v_init_6340_,
        v_t_6341_,
    );
    return v___x_6342_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldlM___boxed(
    mut v_00_u03b1_6343_: *mut leanh::LeanObject,
    mut v_00_u03b2_6344_: *mut leanh::LeanObject,
    mut v_cmp_6345_: *mut leanh::LeanObject,
    mut v_00_u03b4_6346_: *mut leanh::LeanObject,
    mut v_m_6347_: *mut leanh::LeanObject,
    mut v_inst_6348_: *mut leanh::LeanObject,
    mut v_inst_6349_: *mut leanh::LeanObject,
    mut v_inst_6350_: *mut leanh::LeanObject,
    mut v_f_6351_: *mut leanh::LeanObject,
    mut v_init_6352_: *mut leanh::LeanObject,
    mut v_t_6353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6354_ = l_Std_ExtDTreeMap_foldlM(
        v_00_u03b1_6343_,
        v_00_u03b2_6344_,
        v_cmp_6345_,
        v_00_u03b4_6346_,
        v_m_6347_,
        v_inst_6348_,
        v_inst_6349_,
        v_inst_6350_,
        v_f_6351_,
        v_init_6352_,
        v_t_6353_,
    );
    leanh::lean_dec_ref(v_cmp_6345_);
    return v_res_6354_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldl___redArg(
    mut v_f_6355_: *mut leanh::LeanObject,
    mut v_init_6356_: *mut leanh::LeanObject,
    mut v_t_6357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6358_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_6355_, v_init_6356_, v_t_6357_);
    return v___x_6358_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldl(
    mut v_00_u03b1_6359_: *mut leanh::LeanObject,
    mut v_00_u03b2_6360_: *mut leanh::LeanObject,
    mut v_cmp_6361_: *mut leanh::LeanObject,
    mut v_00_u03b4_6362_: *mut leanh::LeanObject,
    mut v_inst_6363_: *mut leanh::LeanObject,
    mut v_f_6364_: *mut leanh::LeanObject,
    mut v_init_6365_: *mut leanh::LeanObject,
    mut v_t_6366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6367_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_6364_, v_init_6365_, v_t_6366_);
    return v___x_6367_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldl___boxed(
    mut v_00_u03b1_6368_: *mut leanh::LeanObject,
    mut v_00_u03b2_6369_: *mut leanh::LeanObject,
    mut v_cmp_6370_: *mut leanh::LeanObject,
    mut v_00_u03b4_6371_: *mut leanh::LeanObject,
    mut v_inst_6372_: *mut leanh::LeanObject,
    mut v_f_6373_: *mut leanh::LeanObject,
    mut v_init_6374_: *mut leanh::LeanObject,
    mut v_t_6375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6376_ = l_Std_ExtDTreeMap_foldl(
        v_00_u03b1_6368_,
        v_00_u03b2_6369_,
        v_cmp_6370_,
        v_00_u03b4_6371_,
        v_inst_6372_,
        v_f_6373_,
        v_init_6374_,
        v_t_6375_,
    );
    leanh::lean_dec_ref(v_cmp_6370_);
    return v_res_6376_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldrM___redArg(
    mut v_inst_6377_: *mut leanh::LeanObject,
    mut v_f_6378_: *mut leanh::LeanObject,
    mut v_init_6379_: *mut leanh::LeanObject,
    mut v_t_6380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6381_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_6377_,
        v_f_6378_,
        v_init_6379_,
        v_t_6380_,
    );
    return v___x_6381_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldrM(
    mut v_00_u03b1_6382_: *mut leanh::LeanObject,
    mut v_00_u03b2_6383_: *mut leanh::LeanObject,
    mut v_cmp_6384_: *mut leanh::LeanObject,
    mut v_00_u03b4_6385_: *mut leanh::LeanObject,
    mut v_m_6386_: *mut leanh::LeanObject,
    mut v_inst_6387_: *mut leanh::LeanObject,
    mut v_inst_6388_: *mut leanh::LeanObject,
    mut v_inst_6389_: *mut leanh::LeanObject,
    mut v_f_6390_: *mut leanh::LeanObject,
    mut v_init_6391_: *mut leanh::LeanObject,
    mut v_t_6392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6393_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_6387_,
        v_f_6390_,
        v_init_6391_,
        v_t_6392_,
    );
    return v___x_6393_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldrM___boxed(
    mut v_00_u03b1_6394_: *mut leanh::LeanObject,
    mut v_00_u03b2_6395_: *mut leanh::LeanObject,
    mut v_cmp_6396_: *mut leanh::LeanObject,
    mut v_00_u03b4_6397_: *mut leanh::LeanObject,
    mut v_m_6398_: *mut leanh::LeanObject,
    mut v_inst_6399_: *mut leanh::LeanObject,
    mut v_inst_6400_: *mut leanh::LeanObject,
    mut v_inst_6401_: *mut leanh::LeanObject,
    mut v_f_6402_: *mut leanh::LeanObject,
    mut v_init_6403_: *mut leanh::LeanObject,
    mut v_t_6404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6405_ = l_Std_ExtDTreeMap_foldrM(
        v_00_u03b1_6394_,
        v_00_u03b2_6395_,
        v_cmp_6396_,
        v_00_u03b4_6397_,
        v_m_6398_,
        v_inst_6399_,
        v_inst_6400_,
        v_inst_6401_,
        v_f_6402_,
        v_init_6403_,
        v_t_6404_,
    );
    leanh::lean_dec_ref(v_cmp_6396_);
    return v_res_6405_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldr___redArg___lam__0(
    mut v_f_6406_: *mut leanh::LeanObject,
    mut v_x1_6407_: *mut leanh::LeanObject,
    mut v_x2_6408_: *mut leanh::LeanObject,
    mut v_x3_6409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6410_ = leanh::lean_apply_3(v_f_6406_, v_x1_6407_, v_x2_6408_, v_x3_6409_);
    return v___x_6410_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldr___redArg(
    mut v_f_6430_: *mut leanh::LeanObject,
    mut v_init_6431_: *mut leanh::LeanObject,
    mut v_t_6432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6433_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6433_, 0, v_f_6430_);
    v___x_6434_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6435_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6434_,
        v___f_6433_,
        v_init_6431_,
        v_t_6432_,
    );
    return v___x_6435_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldr(
    mut v_00_u03b1_6436_: *mut leanh::LeanObject,
    mut v_00_u03b2_6437_: *mut leanh::LeanObject,
    mut v_cmp_6438_: *mut leanh::LeanObject,
    mut v_00_u03b4_6439_: *mut leanh::LeanObject,
    mut v_inst_6440_: *mut leanh::LeanObject,
    mut v_f_6441_: *mut leanh::LeanObject,
    mut v_init_6442_: *mut leanh::LeanObject,
    mut v_t_6443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6444_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6444_, 0, v_f_6441_);
    v___x_6445_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6446_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6445_,
        v___f_6444_,
        v_init_6442_,
        v_t_6443_,
    );
    return v___x_6446_;
}
pub unsafe fn l_Std_ExtDTreeMap_foldr___boxed(
    mut v_00_u03b1_6447_: *mut leanh::LeanObject,
    mut v_00_u03b2_6448_: *mut leanh::LeanObject,
    mut v_cmp_6449_: *mut leanh::LeanObject,
    mut v_00_u03b4_6450_: *mut leanh::LeanObject,
    mut v_inst_6451_: *mut leanh::LeanObject,
    mut v_f_6452_: *mut leanh::LeanObject,
    mut v_init_6453_: *mut leanh::LeanObject,
    mut v_t_6454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6455_ = l_Std_ExtDTreeMap_foldr(
        v_00_u03b1_6447_,
        v_00_u03b2_6448_,
        v_cmp_6449_,
        v_00_u03b4_6450_,
        v_inst_6451_,
        v_f_6452_,
        v_init_6453_,
        v_t_6454_,
    );
    leanh::lean_dec_ref(v_cmp_6449_);
    return v_res_6455_;
}
pub unsafe fn l_Std_ExtDTreeMap_partition___redArg___lam__0(
    mut v_f_6456_: *mut leanh::LeanObject,
    mut v_cmp_6457_: *mut leanh::LeanObject,
    mut v_x_6458_: *mut leanh::LeanObject,
    mut v_a_6459_: *mut leanh::LeanObject,
    mut v_b_6460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6465_: u8 = 0;
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: u8 = 0;
    let mut v___x_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6476_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6461_ = leanh::lean_ctor_get(v_x_6458_, 0);
                v_snd_6462_ = leanh::lean_ctor_get(v_x_6458_, 1);
                v_isSharedCheck_6476_ = (!leanh::lean_is_exclusive(v_x_6458_)) as u8;
                if v_isSharedCheck_6476_ == 0 {
                    v___x_6464_ = v_x_6458_;
                    v_isShared_6465_ = v_isSharedCheck_6476_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6462_);
                    leanh::lean_inc(v_fst_6461_);
                    leanh::lean_dec(v_x_6458_);
                    v___x_6464_ = leanh::lean_box(0);
                    v_isShared_6465_ = v_isSharedCheck_6476_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_b_6460_);
                leanh::lean_inc(v_a_6459_);
                v___x_6466_ = leanh::lean_apply_2(v_f_6456_, v_a_6459_, v_b_6460_);
                v___x_6467_ = (leanh::lean_unbox(v___x_6466_) as u8);
                if v___x_6467_ == 0 {
                    v___x_6468_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_6457_,
                        v_a_6459_,
                        v_b_6460_,
                        v_snd_6462_,
                    );
                    if v_isShared_6465_ == 0 {
                        leanh::lean_ctor_set(v___x_6464_, 1, v___x_6468_);
                        v___x_6470_ = v___x_6464_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6471_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_fst_6461_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6471_, 1, v___x_6468_);
                        v___x_6470_ = v_reuseFailAlloc_6471_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6472_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_6457_,
                        v_a_6459_,
                        v_b_6460_,
                        v_fst_6461_,
                    );
                    if v_isShared_6465_ == 0 {
                        leanh::lean_ctor_set(v___x_6464_, 0, v___x_6472_);
                        v___x_6474_ = v___x_6464_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6475_, 0, v___x_6472_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6475_, 1, v_snd_6462_);
                        v___x_6474_ = v_reuseFailAlloc_6475_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6470_;
            }
            3 => {
                return v___x_6474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_partition___redArg(
    mut v_cmp_6479_: *mut leanh::LeanObject,
    mut v_f_6480_: *mut leanh::LeanObject,
    mut v_t_6481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6482_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_6482_, 0, v_f_6480_);
    leanh::lean_closure_set(v___f_6482_, 1, v_cmp_6479_);
    v___x_6483_ = l_Std_ExtDTreeMap_partition___redArg___closed__0;
    v___x_6484_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_6482_, v___x_6483_, v_t_6481_);
    return v___x_6484_;
}
pub unsafe fn l_Std_ExtDTreeMap_partition(
    mut v_00_u03b1_6485_: *mut leanh::LeanObject,
    mut v_00_u03b2_6486_: *mut leanh::LeanObject,
    mut v_cmp_6487_: *mut leanh::LeanObject,
    mut v_inst_6488_: *mut leanh::LeanObject,
    mut v_f_6489_: *mut leanh::LeanObject,
    mut v_t_6490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6491_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_6491_, 0, v_f_6489_);
    leanh::lean_closure_set(v___f_6491_, 1, v_cmp_6487_);
    v___x_6492_ = l_Std_ExtDTreeMap_partition___redArg___closed__0;
    v___x_6493_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_6491_, v___x_6492_, v_t_6490_);
    return v___x_6493_;
}
pub unsafe fn l_Std_ExtDTreeMap_forM___redArg___lam__0(
    mut v_f_6494_: *mut leanh::LeanObject,
    mut v_x_6495_: *mut leanh::LeanObject,
    mut v_k_6496_: *mut leanh::LeanObject,
    mut v_v_6497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6498_ = leanh::lean_apply_2(v_f_6494_, v_k_6496_, v_v_6497_);
    return v___x_6498_;
}
pub unsafe fn l_Std_ExtDTreeMap_forM___redArg(
    mut v_inst_6499_: *mut leanh::LeanObject,
    mut v_f_6500_: *mut leanh::LeanObject,
    mut v_t_6501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6502_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6502_, 0, v_f_6500_);
    v___x_6503_ = leanh::lean_box(0);
    v___x_6504_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6499_,
        v___f_6502_,
        v___x_6503_,
        v_t_6501_,
    );
    return v___x_6504_;
}
pub unsafe fn l_Std_ExtDTreeMap_forM(
    mut v_00_u03b1_6505_: *mut leanh::LeanObject,
    mut v_00_u03b2_6506_: *mut leanh::LeanObject,
    mut v_cmp_6507_: *mut leanh::LeanObject,
    mut v_m_6508_: *mut leanh::LeanObject,
    mut v_inst_6509_: *mut leanh::LeanObject,
    mut v_inst_6510_: *mut leanh::LeanObject,
    mut v_inst_6511_: *mut leanh::LeanObject,
    mut v_f_6512_: *mut leanh::LeanObject,
    mut v_t_6513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6514_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6514_, 0, v_f_6512_);
    v___x_6515_ = leanh::lean_box(0);
    v___x_6516_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6509_,
        v___f_6514_,
        v___x_6515_,
        v_t_6513_,
    );
    return v___x_6516_;
}
pub unsafe fn l_Std_ExtDTreeMap_forM___boxed(
    mut v_00_u03b1_6517_: *mut leanh::LeanObject,
    mut v_00_u03b2_6518_: *mut leanh::LeanObject,
    mut v_cmp_6519_: *mut leanh::LeanObject,
    mut v_m_6520_: *mut leanh::LeanObject,
    mut v_inst_6521_: *mut leanh::LeanObject,
    mut v_inst_6522_: *mut leanh::LeanObject,
    mut v_inst_6523_: *mut leanh::LeanObject,
    mut v_f_6524_: *mut leanh::LeanObject,
    mut v_t_6525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6526_ = l_Std_ExtDTreeMap_forM(
        v_00_u03b1_6517_,
        v_00_u03b2_6518_,
        v_cmp_6519_,
        v_m_6520_,
        v_inst_6521_,
        v_inst_6522_,
        v_inst_6523_,
        v_f_6524_,
        v_t_6525_,
    );
    leanh::lean_dec_ref(v_cmp_6519_);
    return v_res_6526_;
}
pub unsafe fn l_Std_ExtDTreeMap_forIn___redArg___lam__0(
    mut v_toPure_6527_: *mut leanh::LeanObject,
    mut v_____do__lift_6528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_6529_ = leanh::lean_ctor_get(v_____do__lift_6528_, 0);
    leanh::lean_inc(v_a_6529_);
    leanh::lean_dec_ref(v_____do__lift_6528_);
    v___x_6530_ = leanh::lean_apply_2(v_toPure_6527_, leanh::lean_box(0), v_a_6529_);
    return v___x_6530_;
}
pub unsafe fn l_Std_ExtDTreeMap_forIn___redArg(
    mut v_inst_6531_: *mut leanh::LeanObject,
    mut v_f_6532_: *mut leanh::LeanObject,
    mut v_init_6533_: *mut leanh::LeanObject,
    mut v_t_6534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6535_ = leanh::lean_ctor_get(v_inst_6531_, 0);
    v_toBind_6536_ = leanh::lean_ctor_get(v_inst_6531_, 1);
    leanh::lean_inc(v_toBind_6536_);
    v_toPure_6537_ = leanh::lean_ctor_get(v_toApplicative_6535_, 1);
    leanh::lean_inc(v_toPure_6537_);
    v___x_6538_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_6531_,
        v_f_6532_,
        v_init_6533_,
        v_t_6534_,
    );
    v___f_6539_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6539_, 0, v_toPure_6537_);
    v___x_6540_ = leanh::lean_apply_4(
        v_toBind_6536_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6538_,
        v___f_6539_,
    );
    return v___x_6540_;
}
pub unsafe fn l_Std_ExtDTreeMap_forIn(
    mut v_00_u03b1_6541_: *mut leanh::LeanObject,
    mut v_00_u03b2_6542_: *mut leanh::LeanObject,
    mut v_cmp_6543_: *mut leanh::LeanObject,
    mut v_00_u03b4_6544_: *mut leanh::LeanObject,
    mut v_m_6545_: *mut leanh::LeanObject,
    mut v_inst_6546_: *mut leanh::LeanObject,
    mut v_inst_6547_: *mut leanh::LeanObject,
    mut v_inst_6548_: *mut leanh::LeanObject,
    mut v_f_6549_: *mut leanh::LeanObject,
    mut v_init_6550_: *mut leanh::LeanObject,
    mut v_t_6551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6552_ = leanh::lean_ctor_get(v_inst_6546_, 0);
    v_toBind_6553_ = leanh::lean_ctor_get(v_inst_6546_, 1);
    leanh::lean_inc(v_toBind_6553_);
    v_toPure_6554_ = leanh::lean_ctor_get(v_toApplicative_6552_, 1);
    leanh::lean_inc(v_toPure_6554_);
    v___x_6555_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_6546_,
        v_f_6549_,
        v_init_6550_,
        v_t_6551_,
    );
    v___f_6556_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6556_, 0, v_toPure_6554_);
    v___x_6557_ = leanh::lean_apply_4(
        v_toBind_6553_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6555_,
        v___f_6556_,
    );
    return v___x_6557_;
}
pub unsafe fn l_Std_ExtDTreeMap_forIn___boxed(
    mut v_00_u03b1_6558_: *mut leanh::LeanObject,
    mut v_00_u03b2_6559_: *mut leanh::LeanObject,
    mut v_cmp_6560_: *mut leanh::LeanObject,
    mut v_00_u03b4_6561_: *mut leanh::LeanObject,
    mut v_m_6562_: *mut leanh::LeanObject,
    mut v_inst_6563_: *mut leanh::LeanObject,
    mut v_inst_6564_: *mut leanh::LeanObject,
    mut v_inst_6565_: *mut leanh::LeanObject,
    mut v_f_6566_: *mut leanh::LeanObject,
    mut v_init_6567_: *mut leanh::LeanObject,
    mut v_t_6568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6569_ = l_Std_ExtDTreeMap_forIn(
        v_00_u03b1_6558_,
        v_00_u03b2_6559_,
        v_cmp_6560_,
        v_00_u03b4_6561_,
        v_m_6562_,
        v_inst_6563_,
        v_inst_6564_,
        v_inst_6565_,
        v_f_6566_,
        v_init_6567_,
        v_t_6568_,
    );
    leanh::lean_dec_ref(v_cmp_6560_);
    return v_res_6569_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(
    mut v_f_6570_: *mut leanh::LeanObject,
    mut v_x_6571_: *mut leanh::LeanObject,
    mut v_k_6572_: *mut leanh::LeanObject,
    mut v_v_6573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6574_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6574_, 0, v_k_6572_);
    leanh::lean_ctor_set(v___x_6574_, 1, v_v_6573_);
    v___x_6575_ = leanh::lean_apply_1(v_f_6570_, v___x_6574_);
    return v___x_6575_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1(
    mut v_inst_6576_: *mut leanh::LeanObject,
    mut v_t_6577_: *mut leanh::LeanObject,
    mut v_f_6578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6579_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6579_, 0, v_f_6578_);
    v___x_6580_ = leanh::lean_box(0);
    v___x_6581_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6576_,
        v___f_6579_,
        v___x_6580_,
        v_t_6577_,
    );
    return v___x_6581_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_6582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6583_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_6583_, 0, v_inst_6582_);
    return v___f_6583_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_6584_: *mut leanh::LeanObject,
    mut v_00_u03b2_6585_: *mut leanh::LeanObject,
    mut v_cmp_6586_: *mut leanh::LeanObject,
    mut v_m_6587_: *mut leanh::LeanObject,
    mut v_inst_6588_: *mut leanh::LeanObject,
    mut v_inst_6589_: *mut leanh::LeanObject,
    mut v_inst_6590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6591_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_6591_, 0, v_inst_6589_);
    return v___f_6591_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_6592_: *mut leanh::LeanObject,
    mut v_00_u03b2_6593_: *mut leanh::LeanObject,
    mut v_cmp_6594_: *mut leanh::LeanObject,
    mut v_m_6595_: *mut leanh::LeanObject,
    mut v_inst_6596_: *mut leanh::LeanObject,
    mut v_inst_6597_: *mut leanh::LeanObject,
    mut v_inst_6598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6599_ = l_Std_ExtDTreeMap_instForMSigmaOfTransCmpOfLawfulMonad(
        v_00_u03b1_6592_,
        v_00_u03b2_6593_,
        v_cmp_6594_,
        v_m_6595_,
        v_inst_6596_,
        v_inst_6597_,
        v_inst_6598_,
    );
    leanh::lean_dec_ref(v_cmp_6594_);
    return v_res_6599_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0(
    mut v_f_6600_: *mut leanh::LeanObject,
    mut v_a_6601_: *mut leanh::LeanObject,
    mut v_b_6602_: *mut leanh::LeanObject,
    mut v_acc_6603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6604_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6604_, 0, v_a_6601_);
    leanh::lean_ctor_set(v___x_6604_, 1, v_b_6602_);
    v___x_6605_ = leanh::lean_apply_2(v_f_6600_, v___x_6604_, v_acc_6603_);
    return v___x_6605_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2(
    mut v_inst_6606_: *mut leanh::LeanObject,
    mut v_00_u03b2_6607_: *mut leanh::LeanObject,
    mut v_m_6608_: *mut leanh::LeanObject,
    mut v_init_6609_: *mut leanh::LeanObject,
    mut v_f_6610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6611_ = leanh::lean_ctor_get(v_inst_6606_, 0);
    v_toBind_6612_ = leanh::lean_ctor_get(v_inst_6606_, 1);
    leanh::lean_inc(v_toBind_6612_);
    v_toPure_6613_ = leanh::lean_ctor_get(v_toApplicative_6611_, 1);
    leanh::lean_inc(v_toPure_6613_);
    v___f_6614_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6614_, 0, v_f_6610_);
    v___x_6615_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_6606_,
        v___f_6614_,
        v_init_6609_,
        v_m_6608_,
    );
    v___f_6616_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6616_, 0, v_toPure_6613_);
    v___x_6617_ = leanh::lean_apply_4(
        v_toBind_6612_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6615_,
        v___f_6616_,
    );
    return v___x_6617_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg(
    mut v_inst_6618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6619_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_6619_, 0, v_inst_6618_);
    return v___f_6619_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(
    mut v_00_u03b1_6620_: *mut leanh::LeanObject,
    mut v_00_u03b2_6621_: *mut leanh::LeanObject,
    mut v_cmp_6622_: *mut leanh::LeanObject,
    mut v_m_6623_: *mut leanh::LeanObject,
    mut v_inst_6624_: *mut leanh::LeanObject,
    mut v_inst_6625_: *mut leanh::LeanObject,
    mut v_inst_6626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6627_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_6627_, 0, v_inst_6625_);
    return v___f_6627_;
}
pub unsafe fn l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad___boxed(
    mut v_00_u03b1_6628_: *mut leanh::LeanObject,
    mut v_00_u03b2_6629_: *mut leanh::LeanObject,
    mut v_cmp_6630_: *mut leanh::LeanObject,
    mut v_m_6631_: *mut leanh::LeanObject,
    mut v_inst_6632_: *mut leanh::LeanObject,
    mut v_inst_6633_: *mut leanh::LeanObject,
    mut v_inst_6634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6635_ = l_Std_ExtDTreeMap_instForInSigmaOfTransCmpOfLawfulMonad(
        v_00_u03b1_6628_,
        v_00_u03b2_6629_,
        v_cmp_6630_,
        v_m_6631_,
        v_inst_6632_,
        v_inst_6633_,
        v_inst_6634_,
    );
    leanh::lean_dec_ref(v_cmp_6630_);
    return v_res_6635_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0(
    mut v_f_6636_: *mut leanh::LeanObject,
    mut v_x_6637_: *mut leanh::LeanObject,
    mut v_k_6638_: *mut leanh::LeanObject,
    mut v_v_6639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6640_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6640_, 0, v_k_6638_);
    leanh::lean_ctor_set(v___x_6640_, 1, v_v_6639_);
    v___x_6641_ = leanh::lean_apply_1(v_f_6636_, v___x_6640_);
    return v___x_6641_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forMUncurried___redArg(
    mut v_inst_6642_: *mut leanh::LeanObject,
    mut v_f_6643_: *mut leanh::LeanObject,
    mut v_t_6644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6645_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6645_, 0, v_f_6643_);
    v___x_6646_ = leanh::lean_box(0);
    v___x_6647_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6642_,
        v___f_6645_,
        v___x_6646_,
        v_t_6644_,
    );
    return v___x_6647_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forMUncurried(
    mut v_00_u03b1_6648_: *mut leanh::LeanObject,
    mut v_cmp_6649_: *mut leanh::LeanObject,
    mut v_m_6650_: *mut leanh::LeanObject,
    mut v_inst_6651_: *mut leanh::LeanObject,
    mut v_inst_6652_: *mut leanh::LeanObject,
    mut v_00_u03b2_6653_: *mut leanh::LeanObject,
    mut v_inst_6654_: *mut leanh::LeanObject,
    mut v_f_6655_: *mut leanh::LeanObject,
    mut v_t_6656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6657_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6657_, 0, v_f_6655_);
    v___x_6658_ = leanh::lean_box(0);
    v___x_6659_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6651_,
        v___f_6657_,
        v___x_6658_,
        v_t_6656_,
    );
    return v___x_6659_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forMUncurried___boxed(
    mut v_00_u03b1_6660_: *mut leanh::LeanObject,
    mut v_cmp_6661_: *mut leanh::LeanObject,
    mut v_m_6662_: *mut leanh::LeanObject,
    mut v_inst_6663_: *mut leanh::LeanObject,
    mut v_inst_6664_: *mut leanh::LeanObject,
    mut v_00_u03b2_6665_: *mut leanh::LeanObject,
    mut v_inst_6666_: *mut leanh::LeanObject,
    mut v_f_6667_: *mut leanh::LeanObject,
    mut v_t_6668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6669_ = l_Std_ExtDTreeMap_Const_forMUncurried(
        v_00_u03b1_6660_,
        v_cmp_6661_,
        v_m_6662_,
        v_inst_6663_,
        v_inst_6664_,
        v_00_u03b2_6665_,
        v_inst_6666_,
        v_f_6667_,
        v_t_6668_,
    );
    leanh::lean_dec_ref(v_cmp_6661_);
    return v_res_6669_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0(
    mut v_f_6670_: *mut leanh::LeanObject,
    mut v_a_6671_: *mut leanh::LeanObject,
    mut v_b_6672_: *mut leanh::LeanObject,
    mut v_acc_6673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6674_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6674_, 0, v_a_6671_);
    leanh::lean_ctor_set(v___x_6674_, 1, v_b_6672_);
    v___x_6675_ = leanh::lean_apply_2(v_f_6670_, v___x_6674_, v_acc_6673_);
    return v___x_6675_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forInUncurried___redArg(
    mut v_inst_6676_: *mut leanh::LeanObject,
    mut v_f_6677_: *mut leanh::LeanObject,
    mut v_init_6678_: *mut leanh::LeanObject,
    mut v_t_6679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6680_ = leanh::lean_ctor_get(v_inst_6676_, 0);
    v_toBind_6681_ = leanh::lean_ctor_get(v_inst_6676_, 1);
    leanh::lean_inc(v_toBind_6681_);
    v_toPure_6682_ = leanh::lean_ctor_get(v_toApplicative_6680_, 1);
    leanh::lean_inc(v_toPure_6682_);
    v___f_6683_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6683_, 0, v_f_6677_);
    v___x_6684_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_6676_,
        v___f_6683_,
        v_init_6678_,
        v_t_6679_,
    );
    v___f_6685_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6685_, 0, v_toPure_6682_);
    v___x_6686_ = leanh::lean_apply_4(
        v_toBind_6681_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6684_,
        v___f_6685_,
    );
    return v___x_6686_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forInUncurried(
    mut v_00_u03b1_6687_: *mut leanh::LeanObject,
    mut v_cmp_6688_: *mut leanh::LeanObject,
    mut v_00_u03b4_6689_: *mut leanh::LeanObject,
    mut v_m_6690_: *mut leanh::LeanObject,
    mut v_inst_6691_: *mut leanh::LeanObject,
    mut v_inst_6692_: *mut leanh::LeanObject,
    mut v_00_u03b2_6693_: *mut leanh::LeanObject,
    mut v_inst_6694_: *mut leanh::LeanObject,
    mut v_f_6695_: *mut leanh::LeanObject,
    mut v_init_6696_: *mut leanh::LeanObject,
    mut v_t_6697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6698_ = leanh::lean_ctor_get(v_inst_6691_, 0);
    v_toBind_6699_ = leanh::lean_ctor_get(v_inst_6691_, 1);
    leanh::lean_inc(v_toBind_6699_);
    v_toPure_6700_ = leanh::lean_ctor_get(v_toApplicative_6698_, 1);
    leanh::lean_inc(v_toPure_6700_);
    v___f_6701_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6701_, 0, v_f_6695_);
    v___x_6702_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_6691_,
        v___f_6701_,
        v_init_6696_,
        v_t_6697_,
    );
    v___f_6703_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6703_, 0, v_toPure_6700_);
    v___x_6704_ = leanh::lean_apply_4(
        v_toBind_6699_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6702_,
        v___f_6703_,
    );
    return v___x_6704_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_forInUncurried___boxed(
    mut v_00_u03b1_6705_: *mut leanh::LeanObject,
    mut v_cmp_6706_: *mut leanh::LeanObject,
    mut v_00_u03b4_6707_: *mut leanh::LeanObject,
    mut v_m_6708_: *mut leanh::LeanObject,
    mut v_inst_6709_: *mut leanh::LeanObject,
    mut v_inst_6710_: *mut leanh::LeanObject,
    mut v_00_u03b2_6711_: *mut leanh::LeanObject,
    mut v_inst_6712_: *mut leanh::LeanObject,
    mut v_f_6713_: *mut leanh::LeanObject,
    mut v_init_6714_: *mut leanh::LeanObject,
    mut v_t_6715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6716_ = l_Std_ExtDTreeMap_Const_forInUncurried(
        v_00_u03b1_6705_,
        v_cmp_6706_,
        v_00_u03b4_6707_,
        v_m_6708_,
        v_inst_6709_,
        v_inst_6710_,
        v_00_u03b2_6711_,
        v_inst_6712_,
        v_f_6713_,
        v_init_6714_,
        v_t_6715_,
    );
    leanh::lean_dec_ref(v_cmp_6706_);
    return v_res_6716_;
}
pub unsafe fn l_Std_ExtDTreeMap_any___redArg___lam__0(
    mut v_p_6717_: *mut leanh::LeanObject,
    mut v___x_6718_: *mut leanh::LeanObject,
    mut v___x_6719_: *mut leanh::LeanObject,
    mut v_a_6720_: *mut leanh::LeanObject,
    mut v_b_6721_: *mut leanh::LeanObject,
    mut v_acc_6722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: u8 = 0;
    v___x_6723_ = leanh::lean_apply_2(v_p_6717_, v_a_6720_, v_b_6721_);
    v___x_6724_ = (leanh::lean_unbox(v___x_6723_) as u8);
    if v___x_6724_ == 0 {
        let mut v___x_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6725_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6725_, 0, v___x_6718_);
        return v___x_6725_;
    } else {
        let mut v___x_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_6718_);
        v___x_6726_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6726_, 0, v___x_6723_);
        v___x_6727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6727_, 0, v___x_6726_);
        leanh::lean_ctor_set(v___x_6727_, 1, v___x_6719_);
        v___x_6728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6728_, 0, v___x_6727_);
        return v___x_6728_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_any___redArg___lam__0___boxed(
    mut v_p_6729_: *mut leanh::LeanObject,
    mut v___x_6730_: *mut leanh::LeanObject,
    mut v___x_6731_: *mut leanh::LeanObject,
    mut v_a_6732_: *mut leanh::LeanObject,
    mut v_b_6733_: *mut leanh::LeanObject,
    mut v_acc_6734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6735_ = l_Std_ExtDTreeMap_any___redArg___lam__0(
        v_p_6729_,
        v___x_6730_,
        v___x_6731_,
        v_a_6732_,
        v_b_6733_,
        v_acc_6734_,
    );
    leanh::lean_dec_ref(v_acc_6734_);
    return v_res_6735_;
}
pub unsafe fn l_Std_ExtDTreeMap_any___redArg(
    mut v_t_6739_: *mut leanh::LeanObject,
    mut v_p_6740_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: u8 = 0;
    let mut v_val_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: u8 = 0;
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6747_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
                v___x_6748_ = leanh::lean_box(0);
                v___x_6749_ = l_Std_ExtDTreeMap_any___redArg___closed__0;
                v___f_6750_ = leanh::lean_alloc_closure(
                    l_Std_ExtDTreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_6750_, 0, v_p_6740_);
                leanh::lean_closure_set(v___f_6750_, 1, v___x_6749_);
                leanh::lean_closure_set(v___f_6750_, 2, v___x_6748_);
                v___x_6751_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_6747_,
                    v___f_6750_,
                    v___x_6749_,
                    v_t_6739_,
                );
                v_a_6752_ = leanh::lean_ctor_get(v___x_6751_, 0);
                leanh::lean_inc(v_a_6752_);
                leanh::lean_dec(v___x_6751_);
                v___y_6742_ = v_a_6752_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_6743_ = leanh::lean_ctor_get(v___y_6742_, 0);
                leanh::lean_inc(v_fst_6743_);
                leanh::lean_dec_ref(v___y_6742_);
                if leanh::lean_obj_tag(v_fst_6743_) == 0 {
                    v___x_6744_ = 0;
                    return v___x_6744_;
                } else {
                    v_val_6745_ = leanh::lean_ctor_get(v_fst_6743_, 0);
                    leanh::lean_inc(v_val_6745_);
                    leanh::lean_dec_ref_known(v_fst_6743_, 1);
                    v___x_6746_ = (leanh::lean_unbox(v_val_6745_) as u8);
                    leanh::lean_dec(v_val_6745_);
                    return v___x_6746_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_any___redArg___boxed(
    mut v_t_6753_: *mut leanh::LeanObject,
    mut v_p_6754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6755_: u8 = 0;
    let mut v_r_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6755_ = l_Std_ExtDTreeMap_any___redArg(v_t_6753_, v_p_6754_);
    v_r_6756_ = leanh::lean_box((v_res_6755_) as usize);
    return v_r_6756_;
}
pub unsafe fn l_Std_ExtDTreeMap_any(
    mut v_00_u03b1_6757_: *mut leanh::LeanObject,
    mut v_00_u03b2_6758_: *mut leanh::LeanObject,
    mut v_cmp_6759_: *mut leanh::LeanObject,
    mut v_inst_6760_: *mut leanh::LeanObject,
    mut v_t_6761_: *mut leanh::LeanObject,
    mut v_p_6762_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: u8 = 0;
    let mut v_val_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: u8 = 0;
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6769_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
                v___x_6770_ = leanh::lean_box(0);
                v___x_6771_ = l_Std_ExtDTreeMap_any___redArg___closed__0;
                v___f_6772_ = leanh::lean_alloc_closure(
                    l_Std_ExtDTreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_6772_, 0, v_p_6762_);
                leanh::lean_closure_set(v___f_6772_, 1, v___x_6771_);
                leanh::lean_closure_set(v___f_6772_, 2, v___x_6770_);
                v___x_6773_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_6769_,
                    v___f_6772_,
                    v___x_6771_,
                    v_t_6761_,
                );
                v_a_6774_ = leanh::lean_ctor_get(v___x_6773_, 0);
                leanh::lean_inc(v_a_6774_);
                leanh::lean_dec(v___x_6773_);
                v___y_6764_ = v_a_6774_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_6765_ = leanh::lean_ctor_get(v___y_6764_, 0);
                leanh::lean_inc(v_fst_6765_);
                leanh::lean_dec_ref(v___y_6764_);
                if leanh::lean_obj_tag(v_fst_6765_) == 0 {
                    v___x_6766_ = 0;
                    return v___x_6766_;
                } else {
                    v_val_6767_ = leanh::lean_ctor_get(v_fst_6765_, 0);
                    leanh::lean_inc(v_val_6767_);
                    leanh::lean_dec_ref_known(v_fst_6765_, 1);
                    v___x_6768_ = (leanh::lean_unbox(v_val_6767_) as u8);
                    leanh::lean_dec(v_val_6767_);
                    return v___x_6768_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_any___boxed(
    mut v_00_u03b1_6775_: *mut leanh::LeanObject,
    mut v_00_u03b2_6776_: *mut leanh::LeanObject,
    mut v_cmp_6777_: *mut leanh::LeanObject,
    mut v_inst_6778_: *mut leanh::LeanObject,
    mut v_t_6779_: *mut leanh::LeanObject,
    mut v_p_6780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6781_: u8 = 0;
    let mut v_r_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6781_ = l_Std_ExtDTreeMap_any(
        v_00_u03b1_6775_,
        v_00_u03b2_6776_,
        v_cmp_6777_,
        v_inst_6778_,
        v_t_6779_,
        v_p_6780_,
    );
    leanh::lean_dec_ref(v_cmp_6777_);
    v_r_6782_ = leanh::lean_box((v_res_6781_) as usize);
    return v_r_6782_;
}
pub unsafe fn l_Std_ExtDTreeMap_all___redArg___lam__0(
    mut v_p_6783_: *mut leanh::LeanObject,
    mut v___x_6784_: *mut leanh::LeanObject,
    mut v___x_6785_: *mut leanh::LeanObject,
    mut v_a_6786_: *mut leanh::LeanObject,
    mut v_b_6787_: *mut leanh::LeanObject,
    mut v_acc_6788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: u8 = 0;
    v___x_6789_ = leanh::lean_apply_2(v_p_6783_, v_a_6786_, v_b_6787_);
    v___x_6790_ = (leanh::lean_unbox(v___x_6789_) as u8);
    if v___x_6790_ == 0 {
        let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_6785_);
        v___x_6791_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6791_, 0, v___x_6789_);
        v___x_6792_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6792_, 0, v___x_6791_);
        leanh::lean_ctor_set(v___x_6792_, 1, v___x_6784_);
        v___x_6793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6793_, 0, v___x_6792_);
        return v___x_6793_;
    } else {
        let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6794_, 0, v___x_6785_);
        return v___x_6794_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_all___redArg___lam__0___boxed(
    mut v_p_6795_: *mut leanh::LeanObject,
    mut v___x_6796_: *mut leanh::LeanObject,
    mut v___x_6797_: *mut leanh::LeanObject,
    mut v_a_6798_: *mut leanh::LeanObject,
    mut v_b_6799_: *mut leanh::LeanObject,
    mut v_acc_6800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6801_ = l_Std_ExtDTreeMap_all___redArg___lam__0(
        v_p_6795_,
        v___x_6796_,
        v___x_6797_,
        v_a_6798_,
        v_b_6799_,
        v_acc_6800_,
    );
    leanh::lean_dec_ref(v_acc_6800_);
    return v_res_6801_;
}
pub unsafe fn l_Std_ExtDTreeMap_all___redArg(
    mut v_t_6802_: *mut leanh::LeanObject,
    mut v_p_6803_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_6805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    let mut v_val_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: u8 = 0;
    let mut v___x_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6810_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
                v___x_6811_ = leanh::lean_box(0);
                v___x_6812_ = l_Std_ExtDTreeMap_any___redArg___closed__0;
                v___f_6813_ = leanh::lean_alloc_closure(
                    l_Std_ExtDTreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_6813_, 0, v_p_6803_);
                leanh::lean_closure_set(v___f_6813_, 1, v___x_6811_);
                leanh::lean_closure_set(v___f_6813_, 2, v___x_6812_);
                v___x_6814_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_6810_,
                    v___f_6813_,
                    v___x_6812_,
                    v_t_6802_,
                );
                v_a_6815_ = leanh::lean_ctor_get(v___x_6814_, 0);
                leanh::lean_inc(v_a_6815_);
                leanh::lean_dec(v___x_6814_);
                v___y_6805_ = v_a_6815_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_6806_ = leanh::lean_ctor_get(v___y_6805_, 0);
                leanh::lean_inc(v_fst_6806_);
                leanh::lean_dec_ref(v___y_6805_);
                if leanh::lean_obj_tag(v_fst_6806_) == 0 {
                    v___x_6807_ = 1;
                    return v___x_6807_;
                } else {
                    v_val_6808_ = leanh::lean_ctor_get(v_fst_6806_, 0);
                    leanh::lean_inc(v_val_6808_);
                    leanh::lean_dec_ref_known(v_fst_6806_, 1);
                    v___x_6809_ = (leanh::lean_unbox(v_val_6808_) as u8);
                    leanh::lean_dec(v_val_6808_);
                    return v___x_6809_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_all___redArg___boxed(
    mut v_t_6816_: *mut leanh::LeanObject,
    mut v_p_6817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6818_: u8 = 0;
    let mut v_r_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6818_ = l_Std_ExtDTreeMap_all___redArg(v_t_6816_, v_p_6817_);
    v_r_6819_ = leanh::lean_box((v_res_6818_) as usize);
    return v_r_6819_;
}
pub unsafe fn l_Std_ExtDTreeMap_all(
    mut v_00_u03b1_6820_: *mut leanh::LeanObject,
    mut v_00_u03b2_6821_: *mut leanh::LeanObject,
    mut v_cmp_6822_: *mut leanh::LeanObject,
    mut v_inst_6823_: *mut leanh::LeanObject,
    mut v_t_6824_: *mut leanh::LeanObject,
    mut v_p_6825_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: u8 = 0;
    let mut v_val_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: u8 = 0;
    let mut v___x_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6832_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
                v___x_6833_ = leanh::lean_box(0);
                v___x_6834_ = l_Std_ExtDTreeMap_any___redArg___closed__0;
                v___f_6835_ = leanh::lean_alloc_closure(
                    l_Std_ExtDTreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_6835_, 0, v_p_6825_);
                leanh::lean_closure_set(v___f_6835_, 1, v___x_6833_);
                leanh::lean_closure_set(v___f_6835_, 2, v___x_6834_);
                v___x_6836_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_6832_,
                    v___f_6835_,
                    v___x_6834_,
                    v_t_6824_,
                );
                v_a_6837_ = leanh::lean_ctor_get(v___x_6836_, 0);
                leanh::lean_inc(v_a_6837_);
                leanh::lean_dec(v___x_6836_);
                v___y_6827_ = v_a_6837_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_6828_ = leanh::lean_ctor_get(v___y_6827_, 0);
                leanh::lean_inc(v_fst_6828_);
                leanh::lean_dec_ref(v___y_6827_);
                if leanh::lean_obj_tag(v_fst_6828_) == 0 {
                    v___x_6829_ = 1;
                    return v___x_6829_;
                } else {
                    v_val_6830_ = leanh::lean_ctor_get(v_fst_6828_, 0);
                    leanh::lean_inc(v_val_6830_);
                    leanh::lean_dec_ref_known(v_fst_6828_, 1);
                    v___x_6831_ = (leanh::lean_unbox(v_val_6830_) as u8);
                    leanh::lean_dec(v_val_6830_);
                    return v___x_6831_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_all___boxed(
    mut v_00_u03b1_6838_: *mut leanh::LeanObject,
    mut v_00_u03b2_6839_: *mut leanh::LeanObject,
    mut v_cmp_6840_: *mut leanh::LeanObject,
    mut v_inst_6841_: *mut leanh::LeanObject,
    mut v_t_6842_: *mut leanh::LeanObject,
    mut v_p_6843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6844_: u8 = 0;
    let mut v_r_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6844_ = l_Std_ExtDTreeMap_all(
        v_00_u03b1_6838_,
        v_00_u03b2_6839_,
        v_cmp_6840_,
        v_inst_6841_,
        v_t_6842_,
        v_p_6843_,
    );
    leanh::lean_dec_ref(v_cmp_6840_);
    v_r_6845_ = leanh::lean_box((v_res_6844_) as usize);
    return v_r_6845_;
}
pub unsafe fn l_Std_ExtDTreeMap_keys___redArg___lam__0(
    mut v_x1_6846_: *mut leanh::LeanObject,
    mut v_x2_6847_: *mut leanh::LeanObject,
    mut v_x3_6848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6849_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6849_, 0, v_x1_6846_);
    leanh::lean_ctor_set(v___x_6849_, 1, v_x3_6848_);
    return v___x_6849_;
}
pub unsafe fn l_Std_ExtDTreeMap_keys___redArg___lam__0___boxed(
    mut v_x1_6850_: *mut leanh::LeanObject,
    mut v_x2_6851_: *mut leanh::LeanObject,
    mut v_x3_6852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6853_ = l_Std_ExtDTreeMap_keys___redArg___lam__0(v_x1_6850_, v_x2_6851_, v_x3_6852_);
    leanh::lean_dec(v_x2_6851_);
    return v_res_6853_;
}
pub unsafe fn l_Std_ExtDTreeMap_keys___redArg(
    mut v_t_6855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6856_ = l_Std_ExtDTreeMap_keys___redArg___closed__0;
    v___x_6857_ = leanh::lean_box(0);
    v___x_6858_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6859_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6858_,
        v___f_6856_,
        v___x_6857_,
        v_t_6855_,
    );
    return v___x_6859_;
}
pub unsafe fn l_Std_ExtDTreeMap_keys(
    mut v_00_u03b1_6860_: *mut leanh::LeanObject,
    mut v_00_u03b2_6861_: *mut leanh::LeanObject,
    mut v_cmp_6862_: *mut leanh::LeanObject,
    mut v_inst_6863_: *mut leanh::LeanObject,
    mut v_t_6864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6865_ = l_Std_ExtDTreeMap_keys___redArg___closed__0;
    v___x_6866_ = leanh::lean_box(0);
    v___x_6867_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6868_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6867_,
        v___f_6865_,
        v___x_6866_,
        v_t_6864_,
    );
    return v___x_6868_;
}
pub unsafe fn l_Std_ExtDTreeMap_keys___boxed(
    mut v_00_u03b1_6869_: *mut leanh::LeanObject,
    mut v_00_u03b2_6870_: *mut leanh::LeanObject,
    mut v_cmp_6871_: *mut leanh::LeanObject,
    mut v_inst_6872_: *mut leanh::LeanObject,
    mut v_t_6873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6874_ = l_Std_ExtDTreeMap_keys(
        v_00_u03b1_6869_,
        v_00_u03b2_6870_,
        v_cmp_6871_,
        v_inst_6872_,
        v_t_6873_,
    );
    leanh::lean_dec_ref(v_cmp_6871_);
    return v_res_6874_;
}
pub unsafe fn l_Std_ExtDTreeMap_keysArray___redArg___lam__0(
    mut v_l_6875_: *mut leanh::LeanObject,
    mut v_k_6876_: *mut leanh::LeanObject,
    mut v_x_6877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6878_ = lean_array_push(v_l_6875_, v_k_6876_);
    return v___x_6878_;
}
pub unsafe fn l_Std_ExtDTreeMap_keysArray___redArg___lam__0___boxed(
    mut v_l_6879_: *mut leanh::LeanObject,
    mut v_k_6880_: *mut leanh::LeanObject,
    mut v_x_6881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6882_ = l_Std_ExtDTreeMap_keysArray___redArg___lam__0(v_l_6879_, v_k_6880_, v_x_6881_);
    leanh::lean_dec(v_x_6881_);
    return v_res_6882_;
}
pub unsafe fn l_Std_ExtDTreeMap_keysArray___redArg(
    mut v_t_6884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6885_ = l_Std_ExtDTreeMap_keysArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_6884_) == 0 {
                    v_size_6890_ = leanh::lean_ctor_get(v_t_6884_, 0);
                    leanh::lean_inc(v_size_6890_);
                    v___y_6887_ = v_size_6890_;
                    state = 1;
                    continue;
                } else {
                    v___x_6891_ = leanh::lean_unsigned_to_nat(0);
                    v___y_6887_ = v___x_6891_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6888_ = lean_mk_empty_array_with_capacity(v___y_6887_);
                leanh::lean_dec(v___y_6887_);
                v___x_6889_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_6885_,
                    v___x_6888_,
                    v_t_6884_,
                );
                return v___x_6889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_keysArray(
    mut v_00_u03b1_6892_: *mut leanh::LeanObject,
    mut v_00_u03b2_6893_: *mut leanh::LeanObject,
    mut v_cmp_6894_: *mut leanh::LeanObject,
    mut v_inst_6895_: *mut leanh::LeanObject,
    mut v_t_6896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6897_ = l_Std_ExtDTreeMap_keysArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_6896_) == 0 {
                    v_size_6902_ = leanh::lean_ctor_get(v_t_6896_, 0);
                    leanh::lean_inc(v_size_6902_);
                    v___y_6899_ = v_size_6902_;
                    state = 1;
                    continue;
                } else {
                    v___x_6903_ = leanh::lean_unsigned_to_nat(0);
                    v___y_6899_ = v___x_6903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6900_ = lean_mk_empty_array_with_capacity(v___y_6899_);
                leanh::lean_dec(v___y_6899_);
                v___x_6901_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_6897_,
                    v___x_6900_,
                    v_t_6896_,
                );
                return v___x_6901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_keysArray___boxed(
    mut v_00_u03b1_6904_: *mut leanh::LeanObject,
    mut v_00_u03b2_6905_: *mut leanh::LeanObject,
    mut v_cmp_6906_: *mut leanh::LeanObject,
    mut v_inst_6907_: *mut leanh::LeanObject,
    mut v_t_6908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6909_ = l_Std_ExtDTreeMap_keysArray(
        v_00_u03b1_6904_,
        v_00_u03b2_6905_,
        v_cmp_6906_,
        v_inst_6907_,
        v_t_6908_,
    );
    leanh::lean_dec_ref(v_cmp_6906_);
    return v_res_6909_;
}
pub unsafe fn l_Std_ExtDTreeMap_values___redArg___lam__0(
    mut v_x1_6910_: *mut leanh::LeanObject,
    mut v_x2_6911_: *mut leanh::LeanObject,
    mut v_x3_6912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6913_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6913_, 0, v_x2_6911_);
    leanh::lean_ctor_set(v___x_6913_, 1, v_x3_6912_);
    return v___x_6913_;
}
pub unsafe fn l_Std_ExtDTreeMap_values___redArg___lam__0___boxed(
    mut v_x1_6914_: *mut leanh::LeanObject,
    mut v_x2_6915_: *mut leanh::LeanObject,
    mut v_x3_6916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6917_ = l_Std_ExtDTreeMap_values___redArg___lam__0(v_x1_6914_, v_x2_6915_, v_x3_6916_);
    leanh::lean_dec(v_x1_6914_);
    return v_res_6917_;
}
pub unsafe fn l_Std_ExtDTreeMap_values___redArg(
    mut v_t_6919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6920_ = l_Std_ExtDTreeMap_values___redArg___closed__0;
    v___x_6921_ = leanh::lean_box(0);
    v___x_6922_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6923_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6922_,
        v___f_6920_,
        v___x_6921_,
        v_t_6919_,
    );
    return v___x_6923_;
}
pub unsafe fn l_Std_ExtDTreeMap_values(
    mut v_00_u03b1_6924_: *mut leanh::LeanObject,
    mut v_cmp_6925_: *mut leanh::LeanObject,
    mut v_inst_6926_: *mut leanh::LeanObject,
    mut v_00_u03b2_6927_: *mut leanh::LeanObject,
    mut v_t_6928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6929_ = l_Std_ExtDTreeMap_values___redArg___closed__0;
    v___x_6930_ = leanh::lean_box(0);
    v___x_6931_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6932_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6931_,
        v___f_6929_,
        v___x_6930_,
        v_t_6928_,
    );
    return v___x_6932_;
}
pub unsafe fn l_Std_ExtDTreeMap_values___boxed(
    mut v_00_u03b1_6933_: *mut leanh::LeanObject,
    mut v_cmp_6934_: *mut leanh::LeanObject,
    mut v_inst_6935_: *mut leanh::LeanObject,
    mut v_00_u03b2_6936_: *mut leanh::LeanObject,
    mut v_t_6937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6938_ = l_Std_ExtDTreeMap_values(
        v_00_u03b1_6933_,
        v_cmp_6934_,
        v_inst_6935_,
        v_00_u03b2_6936_,
        v_t_6937_,
    );
    leanh::lean_dec_ref(v_cmp_6934_);
    return v_res_6938_;
}
pub unsafe fn l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(
    mut v_l_6939_: *mut leanh::LeanObject,
    mut v_x_6940_: *mut leanh::LeanObject,
    mut v_v_6941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6942_ = lean_array_push(v_l_6939_, v_v_6941_);
    return v___x_6942_;
}
pub unsafe fn l_Std_ExtDTreeMap_valuesArray___redArg___lam__0___boxed(
    mut v_l_6943_: *mut leanh::LeanObject,
    mut v_x_6944_: *mut leanh::LeanObject,
    mut v_v_6945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6946_ = l_Std_ExtDTreeMap_valuesArray___redArg___lam__0(v_l_6943_, v_x_6944_, v_v_6945_);
    leanh::lean_dec(v_x_6944_);
    return v_res_6946_;
}
pub unsafe fn l_Std_ExtDTreeMap_valuesArray___redArg(
    mut v_t_6948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6949_ = l_Std_ExtDTreeMap_valuesArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_6948_) == 0 {
                    v_size_6954_ = leanh::lean_ctor_get(v_t_6948_, 0);
                    leanh::lean_inc(v_size_6954_);
                    v___y_6951_ = v_size_6954_;
                    state = 1;
                    continue;
                } else {
                    v___x_6955_ = leanh::lean_unsigned_to_nat(0);
                    v___y_6951_ = v___x_6955_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6952_ = lean_mk_empty_array_with_capacity(v___y_6951_);
                leanh::lean_dec(v___y_6951_);
                v___x_6953_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_6949_,
                    v___x_6952_,
                    v_t_6948_,
                );
                return v___x_6953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_valuesArray(
    mut v_00_u03b1_6956_: *mut leanh::LeanObject,
    mut v_cmp_6957_: *mut leanh::LeanObject,
    mut v_inst_6958_: *mut leanh::LeanObject,
    mut v_00_u03b2_6959_: *mut leanh::LeanObject,
    mut v_t_6960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6961_ = l_Std_ExtDTreeMap_valuesArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_6960_) == 0 {
                    v_size_6966_ = leanh::lean_ctor_get(v_t_6960_, 0);
                    leanh::lean_inc(v_size_6966_);
                    v___y_6963_ = v_size_6966_;
                    state = 1;
                    continue;
                } else {
                    v___x_6967_ = leanh::lean_unsigned_to_nat(0);
                    v___y_6963_ = v___x_6967_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6964_ = lean_mk_empty_array_with_capacity(v___y_6963_);
                leanh::lean_dec(v___y_6963_);
                v___x_6965_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_6961_,
                    v___x_6964_,
                    v_t_6960_,
                );
                return v___x_6965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_valuesArray___boxed(
    mut v_00_u03b1_6968_: *mut leanh::LeanObject,
    mut v_cmp_6969_: *mut leanh::LeanObject,
    mut v_inst_6970_: *mut leanh::LeanObject,
    mut v_00_u03b2_6971_: *mut leanh::LeanObject,
    mut v_t_6972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6973_ = l_Std_ExtDTreeMap_valuesArray(
        v_00_u03b1_6968_,
        v_cmp_6969_,
        v_inst_6970_,
        v_00_u03b2_6971_,
        v_t_6972_,
    );
    leanh::lean_dec_ref(v_cmp_6969_);
    return v_res_6973_;
}
pub unsafe fn l_Std_ExtDTreeMap_toList___redArg___lam__0(
    mut v_x1_6974_: *mut leanh::LeanObject,
    mut v_x2_6975_: *mut leanh::LeanObject,
    mut v_x3_6976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6977_, 0, v_x1_6974_);
    leanh::lean_ctor_set(v___x_6977_, 1, v_x2_6975_);
    v___x_6978_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6978_, 0, v___x_6977_);
    leanh::lean_ctor_set(v___x_6978_, 1, v_x3_6976_);
    return v___x_6978_;
}
pub unsafe fn l_Std_ExtDTreeMap_toList___redArg(
    mut v_t_6980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6981_ = l_Std_ExtDTreeMap_toList___redArg___closed__0;
    v___x_6982_ = leanh::lean_box(0);
    v___x_6983_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6984_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6983_,
        v___f_6981_,
        v___x_6982_,
        v_t_6980_,
    );
    return v___x_6984_;
}
pub unsafe fn l_Std_ExtDTreeMap_toList(
    mut v_00_u03b1_6985_: *mut leanh::LeanObject,
    mut v_00_u03b2_6986_: *mut leanh::LeanObject,
    mut v_cmp_6987_: *mut leanh::LeanObject,
    mut v_inst_6988_: *mut leanh::LeanObject,
    mut v_t_6989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6990_ = l_Std_ExtDTreeMap_toList___redArg___closed__0;
    v___x_6991_ = leanh::lean_box(0);
    v___x_6992_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_6993_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_6992_,
        v___f_6990_,
        v___x_6991_,
        v_t_6989_,
    );
    return v___x_6993_;
}
pub unsafe fn l_Std_ExtDTreeMap_toList___boxed(
    mut v_00_u03b1_6994_: *mut leanh::LeanObject,
    mut v_00_u03b2_6995_: *mut leanh::LeanObject,
    mut v_cmp_6996_: *mut leanh::LeanObject,
    mut v_inst_6997_: *mut leanh::LeanObject,
    mut v_t_6998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6999_ = l_Std_ExtDTreeMap_toList(
        v_00_u03b1_6994_,
        v_00_u03b2_6995_,
        v_cmp_6996_,
        v_inst_6997_,
        v_t_6998_,
    );
    leanh::lean_dec_ref(v_cmp_6996_);
    return v_res_6999_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap_ofList___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7000_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__26,
    );
    return v___x_7000_;
}
pub unsafe fn l_Std_ExtDTreeMap_ofList___redArg___lam__0(
    mut v_cmp_7001_: *mut leanh::LeanObject,
    mut v_a_7002_: *mut leanh::LeanObject,
    mut v_x_7003_: *mut leanh::LeanObject,
    mut v___y_7004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_7005_ = leanh::lean_ctor_get(v_a_7002_, 0);
    leanh::lean_inc(v_fst_7005_);
    v_snd_7006_ = leanh::lean_ctor_get(v_a_7002_, 1);
    leanh::lean_inc(v_snd_7006_);
    leanh::lean_dec_ref(v_a_7002_);
    v_r_7007_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_7001_,
        v_fst_7005_,
        v_snd_7006_,
        v___y_7004_,
    );
    v___x_7008_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7008_, 0, v_r_7007_);
    return v___x_7008_;
}
pub unsafe fn l_Std_ExtDTreeMap_ofList___redArg(
    mut v_l_7009_: *mut leanh::LeanObject,
    mut v_cmp_7010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7011_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7011_, 0, v_cmp_7010_);
    v___x_7012_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7013_ = leanh::lean_box(1);
    v___x_7014_ = l_List_forIn_x27_loop___redArg(v___x_7012_, v___f_7011_, v_l_7009_, v_r_7013_);
    return v___x_7014_;
}
pub unsafe fn l_Std_ExtDTreeMap_ofList___redArg___boxed(
    mut v_l_7015_: *mut leanh::LeanObject,
    mut v_cmp_7016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7017_ = l_Std_ExtDTreeMap_ofList___redArg(v_l_7015_, v_cmp_7016_);
    leanh::lean_dec(v_l_7015_);
    return v_res_7017_;
}
pub unsafe fn l_Std_ExtDTreeMap_ofList(
    mut v_00_u03b1_7018_: *mut leanh::LeanObject,
    mut v_00_u03b2_7019_: *mut leanh::LeanObject,
    mut v_l_7020_: *mut leanh::LeanObject,
    mut v_cmp_7021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7022_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7022_, 0, v_cmp_7021_);
    v___x_7023_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7024_ = leanh::lean_box(1);
    v___x_7025_ = l_List_forIn_x27_loop___redArg(v___x_7023_, v___f_7022_, v_l_7020_, v_r_7024_);
    return v___x_7025_;
}
pub unsafe fn l_Std_ExtDTreeMap_ofList___boxed(
    mut v_00_u03b1_7026_: *mut leanh::LeanObject,
    mut v_00_u03b2_7027_: *mut leanh::LeanObject,
    mut v_l_7028_: *mut leanh::LeanObject,
    mut v_cmp_7029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7030_ =
        l_Std_ExtDTreeMap_ofList(v_00_u03b1_7026_, v_00_u03b2_7027_, v_l_7028_, v_cmp_7029_);
    leanh::lean_dec(v_l_7028_);
    return v_res_7030_;
}
pub unsafe fn l_Std_ExtDTreeMap_toArray___redArg___lam__0(
    mut v_l_7031_: *mut leanh::LeanObject,
    mut v_k_7032_: *mut leanh::LeanObject,
    mut v_v_7033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7034_, 0, v_k_7032_);
    leanh::lean_ctor_set(v___x_7034_, 1, v_v_7033_);
    v___x_7035_ = lean_array_push(v_l_7031_, v___x_7034_);
    return v___x_7035_;
}
pub unsafe fn l_Std_ExtDTreeMap_toArray___redArg(
    mut v_t_7037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7038_ = l_Std_ExtDTreeMap_toArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_7037_) == 0 {
                    v_size_7043_ = leanh::lean_ctor_get(v_t_7037_, 0);
                    leanh::lean_inc(v_size_7043_);
                    v___y_7040_ = v_size_7043_;
                    state = 1;
                    continue;
                } else {
                    v___x_7044_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7040_ = v___x_7044_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7041_ = lean_mk_empty_array_with_capacity(v___y_7040_);
                leanh::lean_dec(v___y_7040_);
                v___x_7042_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7038_,
                    v___x_7041_,
                    v_t_7037_,
                );
                return v___x_7042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_toArray(
    mut v_00_u03b1_7045_: *mut leanh::LeanObject,
    mut v_00_u03b2_7046_: *mut leanh::LeanObject,
    mut v_cmp_7047_: *mut leanh::LeanObject,
    mut v_inst_7048_: *mut leanh::LeanObject,
    mut v_t_7049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7050_ = l_Std_ExtDTreeMap_toArray___redArg___closed__0;
                if leanh::lean_obj_tag(v_t_7049_) == 0 {
                    v_size_7055_ = leanh::lean_ctor_get(v_t_7049_, 0);
                    leanh::lean_inc(v_size_7055_);
                    v___y_7052_ = v_size_7055_;
                    state = 1;
                    continue;
                } else {
                    v___x_7056_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7052_ = v___x_7056_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7053_ = lean_mk_empty_array_with_capacity(v___y_7052_);
                leanh::lean_dec(v___y_7052_);
                v___x_7054_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7050_,
                    v___x_7053_,
                    v_t_7049_,
                );
                return v___x_7054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_toArray___boxed(
    mut v_00_u03b1_7057_: *mut leanh::LeanObject,
    mut v_00_u03b2_7058_: *mut leanh::LeanObject,
    mut v_cmp_7059_: *mut leanh::LeanObject,
    mut v_inst_7060_: *mut leanh::LeanObject,
    mut v_t_7061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7062_ = l_Std_ExtDTreeMap_toArray(
        v_00_u03b1_7057_,
        v_00_u03b2_7058_,
        v_cmp_7059_,
        v_inst_7060_,
        v_t_7061_,
    );
    leanh::lean_dec_ref(v_cmp_7059_);
    return v_res_7062_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap_ofArray___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7063_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__26,
    );
    return v___x_7063_;
}
pub unsafe fn l_Std_ExtDTreeMap_ofArray___redArg(
    mut v_a_7064_: *mut leanh::LeanObject,
    mut v_cmp_7065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7069_: usize = 0;
    let mut v___x_7070_: usize = 0;
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7066_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7066_, 0, v_cmp_7065_);
    v___x_7067_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7068_ = leanh::lean_box(1);
    v_sz_7069_ = lean_array_size(v_a_7064_);
    v___x_7070_ = 0usize;
    v___x_7071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7067_,
        v_a_7064_,
        v___f_7066_,
        v_sz_7069_,
        v___x_7070_,
        v_r_7068_,
    );
    return v___x_7071_;
}
pub unsafe fn l_Std_ExtDTreeMap_ofArray(
    mut v_00_u03b1_7072_: *mut leanh::LeanObject,
    mut v_00_u03b2_7073_: *mut leanh::LeanObject,
    mut v_a_7074_: *mut leanh::LeanObject,
    mut v_cmp_7075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7079_: usize = 0;
    let mut v___x_7080_: usize = 0;
    let mut v___x_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7076_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7076_, 0, v_cmp_7075_);
    v___x_7077_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7078_ = leanh::lean_box(1);
    v_sz_7079_ = lean_array_size(v_a_7074_);
    v___x_7080_ = 0usize;
    v___x_7081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7077_,
        v_a_7074_,
        v___f_7076_,
        v_sz_7079_,
        v___x_7080_,
        v_r_7078_,
    );
    return v___x_7081_;
}
pub unsafe fn l_Std_ExtDTreeMap_modify___redArg(
    mut v_cmp_7082_: *mut leanh::LeanObject,
    mut v_t_7083_: *mut leanh::LeanObject,
    mut v_a_7084_: *mut leanh::LeanObject,
    mut v_f_7085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7086_ =
        l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_7082_, v_a_7084_, v_f_7085_, v_t_7083_);
    return v___x_7086_;
}
pub unsafe fn l_Std_ExtDTreeMap_modify(
    mut v_00_u03b1_7087_: *mut leanh::LeanObject,
    mut v_00_u03b2_7088_: *mut leanh::LeanObject,
    mut v_cmp_7089_: *mut leanh::LeanObject,
    mut v_inst_7090_: *mut leanh::LeanObject,
    mut v_inst_7091_: *mut leanh::LeanObject,
    mut v_t_7092_: *mut leanh::LeanObject,
    mut v_a_7093_: *mut leanh::LeanObject,
    mut v_f_7094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7095_ =
        l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_7089_, v_a_7093_, v_f_7094_, v_t_7092_);
    return v___x_7095_;
}
pub unsafe fn l_Std_ExtDTreeMap_alter___redArg(
    mut v_cmp_7096_: *mut leanh::LeanObject,
    mut v_t_7097_: *mut leanh::LeanObject,
    mut v_a_7098_: *mut leanh::LeanObject,
    mut v_f_7099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7100_ =
        l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_7096_, v_a_7098_, v_f_7099_, v_t_7097_);
    return v___x_7100_;
}
pub unsafe fn l_Std_ExtDTreeMap_alter(
    mut v_00_u03b1_7101_: *mut leanh::LeanObject,
    mut v_00_u03b2_7102_: *mut leanh::LeanObject,
    mut v_cmp_7103_: *mut leanh::LeanObject,
    mut v_inst_7104_: *mut leanh::LeanObject,
    mut v_inst_7105_: *mut leanh::LeanObject,
    mut v_t_7106_: *mut leanh::LeanObject,
    mut v_a_7107_: *mut leanh::LeanObject,
    mut v_f_7108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7109_ =
        l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_7103_, v_a_7107_, v_f_7108_, v_t_7106_);
    return v___x_7109_;
}
pub unsafe fn l_Std_ExtDTreeMap_mergeWith___redArg___lam__0(
    mut v_b_u2082_7110_: *mut leanh::LeanObject,
    mut v_mergeFn_7111_: *mut leanh::LeanObject,
    mut v_a_7112_: *mut leanh::LeanObject,
    mut v_x_7113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7118_: u8 = 0;
    let mut v___x_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7113_) == 0 {
                    leanh::lean_dec(v_a_7112_);
                    leanh::lean_dec(v_mergeFn_7111_);
                    v___x_7114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7114_, 0, v_b_u2082_7110_);
                    return v___x_7114_;
                } else {
                    v_val_7115_ = leanh::lean_ctor_get(v_x_7113_, 0);
                    v_isSharedCheck_7123_ = (!leanh::lean_is_exclusive(v_x_7113_)) as u8;
                    if v_isSharedCheck_7123_ == 0 {
                        v___x_7117_ = v_x_7113_;
                        v_isShared_7118_ = v_isSharedCheck_7123_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7115_);
                        leanh::lean_dec(v_x_7113_);
                        v___x_7117_ = leanh::lean_box(0);
                        v_isShared_7118_ = v_isSharedCheck_7123_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7119_ = leanh::lean_apply_3(
                    v_mergeFn_7111_,
                    v_a_7112_,
                    v_val_7115_,
                    v_b_u2082_7110_,
                );
                if v_isShared_7118_ == 0 {
                    leanh::lean_ctor_set(v___x_7117_, 0, v___x_7119_);
                    v___x_7121_ = v___x_7117_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7122_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7122_, 0, v___x_7119_);
                    v___x_7121_ = v_reuseFailAlloc_7122_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtDTreeMap_mergeWith___redArg___lam__1(
    mut v_mergeFn_7124_: *mut leanh::LeanObject,
    mut v_cmp_7125_: *mut leanh::LeanObject,
    mut v_t_7126_: *mut leanh::LeanObject,
    mut v_a_7127_: *mut leanh::LeanObject,
    mut v_b_u2082_7128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_7127_);
    v___f_7129_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_mergeWith___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_7129_, 0, v_b_u2082_7128_);
    leanh::lean_closure_set(v___f_7129_, 1, v_mergeFn_7124_);
    leanh::lean_closure_set(v___f_7129_, 2, v_a_7127_);
    v___x_7130_ =
        l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_7125_, v_a_7127_, v___f_7129_, v_t_7126_);
    return v___x_7130_;
}
pub unsafe fn l_Std_ExtDTreeMap_mergeWith___redArg(
    mut v_cmp_7131_: *mut leanh::LeanObject,
    mut v_mergeFn_7132_: *mut leanh::LeanObject,
    mut v_t_u2081_7133_: *mut leanh::LeanObject,
    mut v_t_u2082_7134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7135_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_7135_, 0, v_mergeFn_7132_);
    leanh::lean_closure_set(v___f_7135_, 1, v_cmp_7131_);
    v___x_7136_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7135_, v_t_u2081_7133_, v_t_u2082_7134_);
    return v___x_7136_;
}
pub unsafe fn l_Std_ExtDTreeMap_mergeWith(
    mut v_00_u03b1_7137_: *mut leanh::LeanObject,
    mut v_00_u03b2_7138_: *mut leanh::LeanObject,
    mut v_cmp_7139_: *mut leanh::LeanObject,
    mut v_inst_7140_: *mut leanh::LeanObject,
    mut v_inst_7141_: *mut leanh::LeanObject,
    mut v_mergeFn_7142_: *mut leanh::LeanObject,
    mut v_t_u2081_7143_: *mut leanh::LeanObject,
    mut v_t_u2082_7144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7145_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_7145_, 0, v_mergeFn_7142_);
    leanh::lean_closure_set(v___f_7145_, 1, v_cmp_7139_);
    v___x_7146_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7145_, v_t_u2081_7143_, v_t_u2082_7144_);
    return v___x_7146_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toList___redArg___lam__0(
    mut v_x1_7147_: *mut leanh::LeanObject,
    mut v_x2_7148_: *mut leanh::LeanObject,
    mut v_x3_7149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7150_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7150_, 0, v_x1_7147_);
    leanh::lean_ctor_set(v___x_7150_, 1, v_x2_7148_);
    v___x_7151_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7151_, 0, v___x_7150_);
    leanh::lean_ctor_set(v___x_7151_, 1, v_x3_7149_);
    return v___x_7151_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toList___redArg(
    mut v_t_7153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7154_ = l_Std_ExtDTreeMap_Const_toList___redArg___closed__0;
    v___x_7155_ = leanh::lean_box(0);
    v___x_7156_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_7157_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7156_,
        v___f_7154_,
        v___x_7155_,
        v_t_7153_,
    );
    return v___x_7157_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toList(
    mut v_00_u03b1_7158_: *mut leanh::LeanObject,
    mut v_cmp_7159_: *mut leanh::LeanObject,
    mut v_00_u03b2_7160_: *mut leanh::LeanObject,
    mut v_inst_7161_: *mut leanh::LeanObject,
    mut v_t_7162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7163_ = l_Std_ExtDTreeMap_Const_toList___redArg___closed__0;
    v___x_7164_ = leanh::lean_box(0);
    v___x_7165_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_7166_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7165_,
        v___f_7163_,
        v___x_7164_,
        v_t_7162_,
    );
    return v___x_7166_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toList___boxed(
    mut v_00_u03b1_7167_: *mut leanh::LeanObject,
    mut v_cmp_7168_: *mut leanh::LeanObject,
    mut v_00_u03b2_7169_: *mut leanh::LeanObject,
    mut v_inst_7170_: *mut leanh::LeanObject,
    mut v_t_7171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7172_ = l_Std_ExtDTreeMap_Const_toList(
        v_00_u03b1_7167_,
        v_cmp_7168_,
        v_00_u03b2_7169_,
        v_inst_7170_,
        v_t_7171_,
    );
    leanh::lean_dec_ref(v_cmp_7168_);
    return v_res_7172_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap_Const_ofList___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7173_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__26,
    );
    return v___x_7173_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0(
    mut v_cmp_7174_: *mut leanh::LeanObject,
    mut v_a_7175_: *mut leanh::LeanObject,
    mut v_x_7176_: *mut leanh::LeanObject,
    mut v___y_7177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_7178_ = leanh::lean_ctor_get(v_a_7175_, 0);
    leanh::lean_inc(v_fst_7178_);
    v_snd_7179_ = leanh::lean_ctor_get(v_a_7175_, 1);
    leanh::lean_inc(v_snd_7179_);
    leanh::lean_dec_ref(v_a_7175_);
    v_r_7180_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_7174_,
        v_fst_7178_,
        v_snd_7179_,
        v___y_7177_,
    );
    v___x_7181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7181_, 0, v_r_7180_);
    return v___x_7181_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_ofList___redArg(
    mut v_l_7182_: *mut leanh::LeanObject,
    mut v_cmp_7183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7184_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7184_, 0, v_cmp_7183_);
    v___x_7185_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7186_ = leanh::lean_box(1);
    v___x_7187_ = l_List_forIn_x27_loop___redArg(v___x_7185_, v___f_7184_, v_l_7182_, v_r_7186_);
    return v___x_7187_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_ofList___redArg___boxed(
    mut v_l_7188_: *mut leanh::LeanObject,
    mut v_cmp_7189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7190_ = l_Std_ExtDTreeMap_Const_ofList___redArg(v_l_7188_, v_cmp_7189_);
    leanh::lean_dec(v_l_7188_);
    return v_res_7190_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_ofList(
    mut v_00_u03b1_7191_: *mut leanh::LeanObject,
    mut v_00_u03b2_7192_: *mut leanh::LeanObject,
    mut v_l_7193_: *mut leanh::LeanObject,
    mut v_cmp_7194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7195_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7195_, 0, v_cmp_7194_);
    v___x_7196_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7197_ = leanh::lean_box(1);
    v___x_7198_ = l_List_forIn_x27_loop___redArg(v___x_7196_, v___f_7195_, v_l_7193_, v_r_7197_);
    return v___x_7198_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_ofList___boxed(
    mut v_00_u03b1_7199_: *mut leanh::LeanObject,
    mut v_00_u03b2_7200_: *mut leanh::LeanObject,
    mut v_l_7201_: *mut leanh::LeanObject,
    mut v_cmp_7202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7203_ =
        l_Std_ExtDTreeMap_Const_ofList(v_00_u03b1_7199_, v_00_u03b2_7200_, v_l_7201_, v_cmp_7202_);
    leanh::lean_dec(v_l_7201_);
    return v_res_7203_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toArray___redArg___lam__0(
    mut v_acc_7204_: *mut leanh::LeanObject,
    mut v_k_7205_: *mut leanh::LeanObject,
    mut v_v_7206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7207_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7207_, 0, v_k_7205_);
    leanh::lean_ctor_set(v___x_7207_, 1, v_v_7206_);
    v___x_7208_ = lean_array_push(v_acc_7204_, v___x_7207_);
    return v___x_7208_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toArray___redArg(
    mut v_t_7212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7213_ = l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0;
    v___x_7214_ = l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1;
    v___x_7215_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7213_, v___x_7214_, v_t_7212_);
    return v___x_7215_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toArray(
    mut v_00_u03b1_7216_: *mut leanh::LeanObject,
    mut v_cmp_7217_: *mut leanh::LeanObject,
    mut v_00_u03b2_7218_: *mut leanh::LeanObject,
    mut v_inst_7219_: *mut leanh::LeanObject,
    mut v_t_7220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7221_ = l_Std_ExtDTreeMap_Const_toArray___redArg___closed__0;
    v___x_7222_ = l_Std_ExtDTreeMap_Const_toArray___redArg___closed__1;
    v___x_7223_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7221_, v___x_7222_, v_t_7220_);
    return v___x_7223_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_toArray___boxed(
    mut v_00_u03b1_7224_: *mut leanh::LeanObject,
    mut v_cmp_7225_: *mut leanh::LeanObject,
    mut v_00_u03b2_7226_: *mut leanh::LeanObject,
    mut v_inst_7227_: *mut leanh::LeanObject,
    mut v_t_7228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7229_ = l_Std_ExtDTreeMap_Const_toArray(
        v_00_u03b1_7224_,
        v_cmp_7225_,
        v_00_u03b2_7226_,
        v_inst_7227_,
        v_t_7228_,
    );
    leanh::lean_dec_ref(v_cmp_7225_);
    return v_res_7229_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7230_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__26,
    );
    return v___x_7230_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_ofArray___redArg(
    mut v_a_7231_: *mut leanh::LeanObject,
    mut v_cmp_7232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7236_: usize = 0;
    let mut v___x_7237_: usize = 0;
    let mut v___x_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7233_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7233_, 0, v_cmp_7232_);
    v___x_7234_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7235_ = leanh::lean_box(1);
    v_sz_7236_ = lean_array_size(v_a_7231_);
    v___x_7237_ = 0usize;
    v___x_7238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7234_,
        v_a_7231_,
        v___f_7233_,
        v_sz_7236_,
        v___x_7237_,
        v_r_7235_,
    );
    return v___x_7238_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_ofArray(
    mut v_00_u03b1_7239_: *mut leanh::LeanObject,
    mut v_00_u03b2_7240_: *mut leanh::LeanObject,
    mut v_a_7241_: *mut leanh::LeanObject,
    mut v_cmp_7242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7246_: usize = 0;
    let mut v___x_7247_: usize = 0;
    let mut v___x_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7243_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7243_, 0, v_cmp_7242_);
    v___x_7244_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7245_ = leanh::lean_box(1);
    v_sz_7246_ = lean_array_size(v_a_7241_);
    v___x_7247_ = 0usize;
    v___x_7248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7244_,
        v_a_7241_,
        v___f_7243_,
        v_sz_7246_,
        v___x_7247_,
        v_r_7245_,
    );
    return v___x_7248_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1() -> *mut leanh::LeanObject
{
    let mut v___x_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7249_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__26,
    );
    return v___x_7249_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0(
    mut v_cmp_7250_: *mut leanh::LeanObject,
    mut v_a_7251_: *mut leanh::LeanObject,
    mut v_x_7252_: *mut leanh::LeanObject,
    mut v___y_7253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7254_: u8 = 0;
    leanh::lean_inc(v___y_7253_);
    leanh::lean_inc(v_a_7251_);
    leanh::lean_inc_ref(v_cmp_7250_);
    v___x_7254_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_7250_, v_a_7251_, v___y_7253_);
    if v___x_7254_ == 0 {
        let mut v___x_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7255_ = leanh::lean_box(0);
        v___x_7256_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_7250_,
            v_a_7251_,
            v___x_7255_,
            v___y_7253_,
        );
        v___x_7257_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7257_, 0, v___x_7256_);
        return v___x_7257_;
    } else {
        let mut v___x_7258_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_7251_);
        leanh::lean_dec_ref(v_cmp_7250_);
        v___x_7258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7258_, 0, v___y_7253_);
        return v___x_7258_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_unitOfList___redArg(
    mut v_l_7259_: *mut leanh::LeanObject,
    mut v_cmp_7260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7261_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7261_, 0, v_cmp_7260_);
    v___x_7262_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7263_ = leanh::lean_box(1);
    v___x_7264_ = l_List_forIn_x27_loop___redArg(v___x_7262_, v___f_7261_, v_l_7259_, v_r_7263_);
    return v___x_7264_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_unitOfList___redArg___boxed(
    mut v_l_7265_: *mut leanh::LeanObject,
    mut v_cmp_7266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7267_ = l_Std_ExtDTreeMap_Const_unitOfList___redArg(v_l_7265_, v_cmp_7266_);
    leanh::lean_dec(v_l_7265_);
    return v_res_7267_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_unitOfList(
    mut v_00_u03b1_7268_: *mut leanh::LeanObject,
    mut v_l_7269_: *mut leanh::LeanObject,
    mut v_cmp_7270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7271_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7271_, 0, v_cmp_7270_);
    v___x_7272_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7273_ = leanh::lean_box(1);
    v___x_7274_ = l_List_forIn_x27_loop___redArg(v___x_7272_, v___f_7271_, v_l_7269_, v_r_7273_);
    return v___x_7274_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_unitOfList___boxed(
    mut v_00_u03b1_7275_: *mut leanh::LeanObject,
    mut v_l_7276_: *mut leanh::LeanObject,
    mut v_cmp_7277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7278_ = l_Std_ExtDTreeMap_Const_unitOfList(v_00_u03b1_7275_, v_l_7276_, v_cmp_7277_);
    leanh::lean_dec(v_l_7276_);
    return v_res_7278_;
}
pub unsafe fn _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1() -> *mut leanh::LeanObject
{
    let mut v___x_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7279_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_ExtDTreeMap___auto__1___closed__26_once),
        _init_l_Std_ExtDTreeMap___auto__1___closed__26,
    );
    return v___x_7279_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_unitOfArray___redArg(
    mut v_a_7280_: *mut leanh::LeanObject,
    mut v_cmp_7281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7285_: usize = 0;
    let mut v___x_7286_: usize = 0;
    let mut v___x_7287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7282_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7282_, 0, v_cmp_7281_);
    v___x_7283_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7284_ = leanh::lean_box(1);
    v_sz_7285_ = lean_array_size(v_a_7280_);
    v___x_7286_ = 0usize;
    v___x_7287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7283_,
        v_a_7280_,
        v___f_7282_,
        v_sz_7285_,
        v___x_7286_,
        v_r_7284_,
    );
    return v___x_7287_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_unitOfArray(
    mut v_00_u03b1_7288_: *mut leanh::LeanObject,
    mut v_a_7289_: *mut leanh::LeanObject,
    mut v_cmp_7290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7294_: usize = 0;
    let mut v___x_7295_: usize = 0;
    let mut v___x_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7291_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_7291_, 0, v_cmp_7290_);
    v___x_7292_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v_r_7293_ = leanh::lean_box(1);
    v_sz_7294_ = lean_array_size(v_a_7289_);
    v___x_7295_ = 0usize;
    v___x_7296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7292_,
        v_a_7289_,
        v___f_7291_,
        v_sz_7294_,
        v___x_7295_,
        v_r_7293_,
    );
    return v___x_7296_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_modify___redArg(
    mut v_cmp_7297_: *mut leanh::LeanObject,
    mut v_t_7298_: *mut leanh::LeanObject,
    mut v_a_7299_: *mut leanh::LeanObject,
    mut v_f_7300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7301_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_7297_,
        v_a_7299_,
        v_f_7300_,
        v_t_7298_,
    );
    return v___x_7301_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_modify(
    mut v_00_u03b1_7302_: *mut leanh::LeanObject,
    mut v_cmp_7303_: *mut leanh::LeanObject,
    mut v_00_u03b2_7304_: *mut leanh::LeanObject,
    mut v_inst_7305_: *mut leanh::LeanObject,
    mut v_t_7306_: *mut leanh::LeanObject,
    mut v_a_7307_: *mut leanh::LeanObject,
    mut v_f_7308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7309_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_7303_,
        v_a_7307_,
        v_f_7308_,
        v_t_7306_,
    );
    return v___x_7309_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_alter___redArg(
    mut v_cmp_7310_: *mut leanh::LeanObject,
    mut v_t_7311_: *mut leanh::LeanObject,
    mut v_a_7312_: *mut leanh::LeanObject,
    mut v_f_7313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7314_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_7310_,
        v_a_7312_,
        v_f_7313_,
        v_t_7311_,
    );
    return v___x_7314_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_alter(
    mut v_00_u03b1_7315_: *mut leanh::LeanObject,
    mut v_cmp_7316_: *mut leanh::LeanObject,
    mut v_00_u03b2_7317_: *mut leanh::LeanObject,
    mut v_inst_7318_: *mut leanh::LeanObject,
    mut v_t_7319_: *mut leanh::LeanObject,
    mut v_a_7320_: *mut leanh::LeanObject,
    mut v_f_7321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7322_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_7316_,
        v_a_7320_,
        v_f_7321_,
        v_t_7319_,
    );
    return v___x_7322_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1(
    mut v_mergeFn_7323_: *mut leanh::LeanObject,
    mut v_cmp_7324_: *mut leanh::LeanObject,
    mut v_t_7325_: *mut leanh::LeanObject,
    mut v_a_7326_: *mut leanh::LeanObject,
    mut v_b_u2082_7327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7329_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_7326_);
    v___f_7328_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_mergeWith___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_7328_, 0, v_b_u2082_7327_);
    leanh::lean_closure_set(v___f_7328_, 1, v_mergeFn_7323_);
    leanh::lean_closure_set(v___f_7328_, 2, v_a_7326_);
    v___x_7329_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_7324_,
        v_a_7326_,
        v___f_7328_,
        v_t_7325_,
    );
    return v___x_7329_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_mergeWith___redArg(
    mut v_cmp_7330_: *mut leanh::LeanObject,
    mut v_mergeFn_7331_: *mut leanh::LeanObject,
    mut v_t_u2081_7332_: *mut leanh::LeanObject,
    mut v_t_u2082_7333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7334_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_7334_, 0, v_mergeFn_7331_);
    leanh::lean_closure_set(v___f_7334_, 1, v_cmp_7330_);
    v___x_7335_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7334_, v_t_u2081_7332_, v_t_u2082_7333_);
    return v___x_7335_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_mergeWith(
    mut v_00_u03b1_7336_: *mut leanh::LeanObject,
    mut v_cmp_7337_: *mut leanh::LeanObject,
    mut v_00_u03b2_7338_: *mut leanh::LeanObject,
    mut v_inst_7339_: *mut leanh::LeanObject,
    mut v_mergeFn_7340_: *mut leanh::LeanObject,
    mut v_t_u2081_7341_: *mut leanh::LeanObject,
    mut v_t_u2082_7342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7343_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_7343_, 0, v_mergeFn_7340_);
    leanh::lean_closure_set(v___f_7343_, 1, v_cmp_7337_);
    v___x_7344_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7343_, v_t_u2081_7341_, v_t_u2082_7342_);
    return v___x_7344_;
}
pub unsafe fn l_Std_ExtDTreeMap_insertMany___redArg___lam__0(
    mut v_cmp_7345_: *mut leanh::LeanObject,
    mut v_x_7346_: *mut leanh::LeanObject,
    mut v_____s_7347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_7348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_7348_ = leanh::lean_ctor_get(v_x_7346_, 0);
    leanh::lean_inc(v_fst_7348_);
    v_snd_7349_ = leanh::lean_ctor_get(v_x_7346_, 1);
    leanh::lean_inc(v_snd_7349_);
    leanh::lean_dec_ref(v_x_7346_);
    v_acc_7350_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_7345_,
        v_fst_7348_,
        v_snd_7349_,
        v_____s_7347_,
    );
    v___x_7351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7351_, 0, v_acc_7350_);
    return v___x_7351_;
}
pub unsafe fn l_Std_ExtDTreeMap_insertMany___redArg(
    mut v_cmp_7352_: *mut leanh::LeanObject,
    mut v_inst_7353_: *mut leanh::LeanObject,
    mut v_t_7354_: *mut leanh::LeanObject,
    mut v_l_7355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7356_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7356_, 0, v_cmp_7352_);
    v___x_7357_ = leanh::lean_apply_4(
        v_inst_7353_,
        leanh::lean_box(0),
        v_l_7355_,
        v_t_7354_,
        v___f_7356_,
    );
    return v___x_7357_;
}
pub unsafe fn l_Std_ExtDTreeMap_insertMany(
    mut v_00_u03b1_7358_: *mut leanh::LeanObject,
    mut v_00_u03b2_7359_: *mut leanh::LeanObject,
    mut v_cmp_7360_: *mut leanh::LeanObject,
    mut v_inst_7361_: *mut leanh::LeanObject,
    mut v_00_u03c1_7362_: *mut leanh::LeanObject,
    mut v_inst_7363_: *mut leanh::LeanObject,
    mut v_t_7364_: *mut leanh::LeanObject,
    mut v_l_7365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7366_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7366_, 0, v_cmp_7360_);
    v___x_7367_ = leanh::lean_apply_4(
        v_inst_7363_,
        leanh::lean_box(0),
        v_l_7365_,
        v_t_7364_,
        v___f_7366_,
    );
    return v___x_7367_;
}
pub unsafe fn l_Std_ExtDTreeMap_eraseMany___redArg___lam__0(
    mut v_cmp_7368_: *mut leanh::LeanObject,
    mut v_a_7369_: *mut leanh::LeanObject,
    mut v_____s_7370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_acc_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_acc_7371_ =
        l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_7368_, v_a_7369_, v_____s_7370_);
    v___x_7372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7372_, 0, v_acc_7371_);
    return v___x_7372_;
}
pub unsafe fn l_Std_ExtDTreeMap_eraseMany___redArg(
    mut v_cmp_7373_: *mut leanh::LeanObject,
    mut v_inst_7374_: *mut leanh::LeanObject,
    mut v_t_7375_: *mut leanh::LeanObject,
    mut v_l_7376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7377_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7377_, 0, v_cmp_7373_);
    v___x_7378_ = leanh::lean_apply_4(
        v_inst_7374_,
        leanh::lean_box(0),
        v_l_7376_,
        v_t_7375_,
        v___f_7377_,
    );
    return v___x_7378_;
}
pub unsafe fn l_Std_ExtDTreeMap_eraseMany(
    mut v_00_u03b1_7379_: *mut leanh::LeanObject,
    mut v_00_u03b2_7380_: *mut leanh::LeanObject,
    mut v_cmp_7381_: *mut leanh::LeanObject,
    mut v_inst_7382_: *mut leanh::LeanObject,
    mut v_00_u03c1_7383_: *mut leanh::LeanObject,
    mut v_inst_7384_: *mut leanh::LeanObject,
    mut v_t_7385_: *mut leanh::LeanObject,
    mut v_l_7386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7387_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7387_, 0, v_cmp_7381_);
    v___x_7388_ = leanh::lean_apply_4(
        v_inst_7384_,
        leanh::lean_box(0),
        v_l_7386_,
        v_t_7385_,
        v___f_7387_,
    );
    return v___x_7388_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0(
    mut v_cmp_7389_: *mut leanh::LeanObject,
    mut v_x_7390_: *mut leanh::LeanObject,
    mut v_____s_7391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_7394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_7392_ = leanh::lean_ctor_get(v_x_7390_, 0);
    leanh::lean_inc(v_fst_7392_);
    v_snd_7393_ = leanh::lean_ctor_get(v_x_7390_, 1);
    leanh::lean_inc(v_snd_7393_);
    leanh::lean_dec_ref(v_x_7390_);
    v_acc_7394_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_7389_,
        v_fst_7392_,
        v_snd_7393_,
        v_____s_7391_,
    );
    v___x_7395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7395_, 0, v_acc_7394_);
    return v___x_7395_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_insertMany___redArg(
    mut v_cmp_7396_: *mut leanh::LeanObject,
    mut v_inst_7397_: *mut leanh::LeanObject,
    mut v_t_7398_: *mut leanh::LeanObject,
    mut v_l_7399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7400_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7400_, 0, v_cmp_7396_);
    v___x_7401_ = leanh::lean_apply_4(
        v_inst_7397_,
        leanh::lean_box(0),
        v_l_7399_,
        v_t_7398_,
        v___f_7400_,
    );
    return v___x_7401_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_insertMany(
    mut v_00_u03b1_7402_: *mut leanh::LeanObject,
    mut v_cmp_7403_: *mut leanh::LeanObject,
    mut v_00_u03b2_7404_: *mut leanh::LeanObject,
    mut v_inst_7405_: *mut leanh::LeanObject,
    mut v_00_u03c1_7406_: *mut leanh::LeanObject,
    mut v_inst_7407_: *mut leanh::LeanObject,
    mut v_t_7408_: *mut leanh::LeanObject,
    mut v_l_7409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7410_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7410_, 0, v_cmp_7403_);
    v___x_7411_ = leanh::lean_apply_4(
        v_inst_7407_,
        leanh::lean_box(0),
        v_l_7409_,
        v_t_7408_,
        v___f_7410_,
    );
    return v___x_7411_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(
    mut v_cmp_7412_: *mut leanh::LeanObject,
    mut v_a_7413_: *mut leanh::LeanObject,
    mut v_____s_7414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7415_: u8 = 0;
    leanh::lean_inc(v_____s_7414_);
    leanh::lean_inc(v_a_7413_);
    leanh::lean_inc_ref(v_cmp_7412_);
    v___x_7415_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_7412_, v_a_7413_, v_____s_7414_);
    if v___x_7415_ == 0 {
        let mut v___x_7416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7416_ = leanh::lean_box(0);
        v___x_7417_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_7412_,
            v_a_7413_,
            v___x_7416_,
            v_____s_7414_,
        );
        v___x_7418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7418_, 0, v___x_7417_);
        return v___x_7418_;
    } else {
        let mut v___x_7419_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_7413_);
        leanh::lean_dec_ref(v_cmp_7412_);
        v___x_7419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7419_, 0, v_____s_7414_);
        return v___x_7419_;
    }
}
pub unsafe fn l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg(
    mut v_cmp_7420_: *mut leanh::LeanObject,
    mut v_inst_7421_: *mut leanh::LeanObject,
    mut v_t_7422_: *mut leanh::LeanObject,
    mut v_l_7423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7424_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7424_, 0, v_cmp_7420_);
    v___x_7425_ = leanh::lean_apply_4(
        v_inst_7421_,
        leanh::lean_box(0),
        v_l_7423_,
        v_t_7422_,
        v___f_7424_,
    );
    return v___x_7425_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_insertManyIfNewUnit(
    mut v_00_u03b1_7426_: *mut leanh::LeanObject,
    mut v_cmp_7427_: *mut leanh::LeanObject,
    mut v_inst_7428_: *mut leanh::LeanObject,
    mut v_00_u03c1_7429_: *mut leanh::LeanObject,
    mut v_inst_7430_: *mut leanh::LeanObject,
    mut v_t_7431_: *mut leanh::LeanObject,
    mut v_l_7432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7433_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_7433_, 0, v_cmp_7427_);
    v___x_7434_ = leanh::lean_apply_4(
        v_inst_7430_,
        leanh::lean_box(0),
        v_l_7432_,
        v_t_7431_,
        v___f_7433_,
    );
    return v___x_7434_;
}
pub unsafe fn l_Std_ExtDTreeMap_union___redArg(
    mut v_cmp_7435_: *mut leanh::LeanObject,
    mut v_m_u2081_7436_: *mut leanh::LeanObject,
    mut v_m_u2082_7437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7438_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_7435_,
        v_m_u2081_7436_,
        v_m_u2082_7437_,
    );
    return v___x_7438_;
}
pub unsafe fn l_Std_ExtDTreeMap_union(
    mut v_00_u03b1_7439_: *mut leanh::LeanObject,
    mut v_00_u03b2_7440_: *mut leanh::LeanObject,
    mut v_cmp_7441_: *mut leanh::LeanObject,
    mut v_inst_7442_: *mut leanh::LeanObject,
    mut v_m_u2081_7443_: *mut leanh::LeanObject,
    mut v_m_u2082_7444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7445_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_7441_,
        v_m_u2081_7443_,
        v_m_u2082_7444_,
    );
    return v___x_7445_;
}
pub unsafe fn l_Std_ExtDTreeMap_instUnionOfTransCmp___redArg(
    mut v_cmp_7446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7447_ =
        leanh::lean_alloc_closure(l_Std_ExtDTreeMap_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_7447_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7447_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7447_, 2, v_cmp_7446_);
    leanh::lean_closure_set(v___x_7447_, 3, leanh::lean_box(0));
    return v___x_7447_;
}
pub unsafe fn l_Std_ExtDTreeMap_instUnionOfTransCmp(
    mut v_00_u03b1_7448_: *mut leanh::LeanObject,
    mut v_00_u03b2_7449_: *mut leanh::LeanObject,
    mut v_cmp_7450_: *mut leanh::LeanObject,
    mut v_inst_7451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7452_ =
        leanh::lean_alloc_closure(l_Std_ExtDTreeMap_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_7452_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7452_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7452_, 2, v_cmp_7450_);
    leanh::lean_closure_set(v___x_7452_, 3, leanh::lean_box(0));
    return v___x_7452_;
}
pub unsafe fn l_Std_ExtDTreeMap_inter___redArg(
    mut v_cmp_7453_: *mut leanh::LeanObject,
    mut v_m_u2081_7454_: *mut leanh::LeanObject,
    mut v_m_u2082_7455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7456_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_7453_,
        v_m_u2081_7454_,
        v_m_u2082_7455_,
    );
    return v___x_7456_;
}
pub unsafe fn l_Std_ExtDTreeMap_inter(
    mut v_00_u03b1_7457_: *mut leanh::LeanObject,
    mut v_00_u03b2_7458_: *mut leanh::LeanObject,
    mut v_cmp_7459_: *mut leanh::LeanObject,
    mut v_inst_7460_: *mut leanh::LeanObject,
    mut v_m_u2081_7461_: *mut leanh::LeanObject,
    mut v_m_u2082_7462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7463_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_7459_,
        v_m_u2081_7461_,
        v_m_u2082_7462_,
    );
    return v___x_7463_;
}
pub unsafe fn l_Std_ExtDTreeMap_instInterOfTransCmp___redArg(
    mut v_cmp_7464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7465_ =
        leanh::lean_alloc_closure(l_Std_ExtDTreeMap_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_7465_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7465_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7465_, 2, v_cmp_7464_);
    leanh::lean_closure_set(v___x_7465_, 3, leanh::lean_box(0));
    return v___x_7465_;
}
pub unsafe fn l_Std_ExtDTreeMap_instInterOfTransCmp(
    mut v_00_u03b1_7466_: *mut leanh::LeanObject,
    mut v_00_u03b2_7467_: *mut leanh::LeanObject,
    mut v_cmp_7468_: *mut leanh::LeanObject,
    mut v_inst_7469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7470_ =
        leanh::lean_alloc_closure(l_Std_ExtDTreeMap_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_7470_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7470_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7470_, 2, v_cmp_7468_);
    leanh::lean_closure_set(v___x_7470_, 3, leanh::lean_box(0));
    return v___x_7470_;
}
pub unsafe fn l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(
    mut v_cmp_7471_: *mut leanh::LeanObject,
    mut v_inst_7472_: *mut leanh::LeanObject,
    mut v_x_7473_: *mut leanh::LeanObject,
    mut v_y_7474_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7475_: u8 = 0;
    v___x_7475_ =
        l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_7471_, v_inst_7472_, v_x_7473_, v_y_7474_);
    return v___x_7475_;
}
pub unsafe fn l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed(
    mut v_cmp_7476_: *mut leanh::LeanObject,
    mut v_inst_7477_: *mut leanh::LeanObject,
    mut v_x_7478_: *mut leanh::LeanObject,
    mut v_y_7479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7480_: u8 = 0;
    let mut v_r_7481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7480_ = l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0(
        v_cmp_7476_,
        v_inst_7477_,
        v_x_7478_,
        v_y_7479_,
    );
    v_r_7481_ = leanh::lean_box((v_res_7480_) as usize);
    return v_r_7481_;
}
pub unsafe fn l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(
    mut v_cmp_7482_: *mut leanh::LeanObject,
    mut v_inst_7483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_cmp_7482_);
    v___f_7484_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_7484_, 0, v_cmp_7482_);
    leanh::lean_closure_set(v___f_7484_, 1, v_inst_7483_);
    v___x_7485_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_lift_u2082___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_7485_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7485_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7485_, 2, v_cmp_7482_);
    leanh::lean_closure_set(v___x_7485_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7485_, 4, v___f_7484_);
    leanh::lean_closure_set(v___x_7485_, 5, leanh::lean_box(0));
    return v___x_7485_;
}
pub unsafe fn l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp(
    mut v_00_u03b1_7486_: *mut leanh::LeanObject,
    mut v_00_u03b2_7487_: *mut leanh::LeanObject,
    mut v_cmp_7488_: *mut leanh::LeanObject,
    mut v_inst_7489_: *mut leanh::LeanObject,
    mut v_inst_7490_: *mut leanh::LeanObject,
    mut v_inst_7491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7492_ =
        l_Std_ExtDTreeMap_instBEqOfLawfulEqCmpOfTransCmp___redArg(v_cmp_7488_, v_inst_7491_);
    return v___x_7492_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
    mut v_cmp_7493_: *mut leanh::LeanObject,
    mut v_inst_7494_: *mut leanh::LeanObject,
    mut v_x_7495_: *mut leanh::LeanObject,
    mut v_x_7496_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7497_: u8 = 0;
    v___x_7497_ =
        l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_7493_, v_inst_7494_, v_x_7495_, v_x_7496_);
    return v___x_7497_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg___boxed(
    mut v_cmp_7498_: *mut leanh::LeanObject,
    mut v_inst_7499_: *mut leanh::LeanObject,
    mut v_x_7500_: *mut leanh::LeanObject,
    mut v_x_7501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7502_: u8 = 0;
    let mut v_r_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7502_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(
        v_cmp_7498_,
        v_inst_7499_,
        v_x_7500_,
        v_x_7501_,
    );
    v_r_7503_ = leanh::lean_box((v_res_7502_) as usize);
    return v_r_7503_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(
    mut v_00_u03b1_7504_: *mut leanh::LeanObject,
    mut v_00_u03b2_7505_: *mut leanh::LeanObject,
    mut v_cmp_7506_: *mut leanh::LeanObject,
    mut v_inst_7507_: *mut leanh::LeanObject,
    mut v_inst_7508_: *mut leanh::LeanObject,
    mut v_inst_7509_: *mut leanh::LeanObject,
    mut v_inst_7510_: *mut leanh::LeanObject,
    mut v_x_7511_: *mut leanh::LeanObject,
    mut v_x_7512_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7513_: u8 = 0;
    v___x_7513_ =
        l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_7506_, v_inst_7509_, v_x_7511_, v_x_7512_);
    return v___x_7513_;
}
pub unsafe fn l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq___boxed(
    mut v_00_u03b1_7514_: *mut leanh::LeanObject,
    mut v_00_u03b2_7515_: *mut leanh::LeanObject,
    mut v_cmp_7516_: *mut leanh::LeanObject,
    mut v_inst_7517_: *mut leanh::LeanObject,
    mut v_inst_7518_: *mut leanh::LeanObject,
    mut v_inst_7519_: *mut leanh::LeanObject,
    mut v_inst_7520_: *mut leanh::LeanObject,
    mut v_x_7521_: *mut leanh::LeanObject,
    mut v_x_7522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7523_: u8 = 0;
    let mut v_r_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7523_ = l_Std_ExtDTreeMap_instDecidableEqOfTransCmpOfLawfulEqCmpOfLawfulBEq(
        v_00_u03b1_7514_,
        v_00_u03b2_7515_,
        v_cmp_7516_,
        v_inst_7517_,
        v_inst_7518_,
        v_inst_7519_,
        v_inst_7520_,
        v_x_7521_,
        v_x_7522_,
    );
    v_r_7524_ = leanh::lean_box((v_res_7523_) as usize);
    return v_r_7524_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_beq___redArg(
    mut v_cmp_7525_: *mut leanh::LeanObject,
    mut v_inst_7526_: *mut leanh::LeanObject,
    mut v_m_u2081_7527_: *mut leanh::LeanObject,
    mut v_m_u2082_7528_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7529_: u8 = 0;
    v___x_7529_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_7525_,
        v_inst_7526_,
        v_m_u2081_7527_,
        v_m_u2082_7528_,
    );
    return v___x_7529_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_beq___redArg___boxed(
    mut v_cmp_7530_: *mut leanh::LeanObject,
    mut v_inst_7531_: *mut leanh::LeanObject,
    mut v_m_u2081_7532_: *mut leanh::LeanObject,
    mut v_m_u2082_7533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7534_: u8 = 0;
    let mut v_r_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7534_ = l_Std_ExtDTreeMap_Const_beq___redArg(
        v_cmp_7530_,
        v_inst_7531_,
        v_m_u2081_7532_,
        v_m_u2082_7533_,
    );
    v_r_7535_ = leanh::lean_box((v_res_7534_) as usize);
    return v_r_7535_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_beq(
    mut v_00_u03b1_7536_: *mut leanh::LeanObject,
    mut v_cmp_7537_: *mut leanh::LeanObject,
    mut v_00_u03b2_7538_: *mut leanh::LeanObject,
    mut v_inst_7539_: *mut leanh::LeanObject,
    mut v_inst_7540_: *mut leanh::LeanObject,
    mut v_m_u2081_7541_: *mut leanh::LeanObject,
    mut v_m_u2082_7542_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7543_: u8 = 0;
    v___x_7543_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_7537_,
        v_inst_7540_,
        v_m_u2081_7541_,
        v_m_u2082_7542_,
    );
    return v___x_7543_;
}
pub unsafe fn l_Std_ExtDTreeMap_Const_beq___boxed(
    mut v_00_u03b1_7544_: *mut leanh::LeanObject,
    mut v_cmp_7545_: *mut leanh::LeanObject,
    mut v_00_u03b2_7546_: *mut leanh::LeanObject,
    mut v_inst_7547_: *mut leanh::LeanObject,
    mut v_inst_7548_: *mut leanh::LeanObject,
    mut v_m_u2081_7549_: *mut leanh::LeanObject,
    mut v_m_u2082_7550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7551_: u8 = 0;
    let mut v_r_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7551_ = l_Std_ExtDTreeMap_Const_beq(
        v_00_u03b1_7544_,
        v_cmp_7545_,
        v_00_u03b2_7546_,
        v_inst_7547_,
        v_inst_7548_,
        v_m_u2081_7549_,
        v_m_u2082_7550_,
    );
    v_r_7552_ = leanh::lean_box((v_res_7551_) as usize);
    return v_r_7552_;
}
pub unsafe fn l_Std_ExtDTreeMap_diff___redArg(
    mut v_cmp_7553_: *mut leanh::LeanObject,
    mut v_m_u2081_7554_: *mut leanh::LeanObject,
    mut v_m_u2082_7555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7556_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_7553_,
        v_m_u2081_7554_,
        v_m_u2082_7555_,
    );
    return v___x_7556_;
}
pub unsafe fn l_Std_ExtDTreeMap_diff(
    mut v_00_u03b1_7557_: *mut leanh::LeanObject,
    mut v_00_u03b2_7558_: *mut leanh::LeanObject,
    mut v_cmp_7559_: *mut leanh::LeanObject,
    mut v_inst_7560_: *mut leanh::LeanObject,
    mut v_m_u2081_7561_: *mut leanh::LeanObject,
    mut v_m_u2082_7562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7563_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_7559_,
        v_m_u2081_7561_,
        v_m_u2082_7562_,
    );
    return v___x_7563_;
}
pub unsafe fn l_Std_ExtDTreeMap_instSDiffOfTransCmp___redArg(
    mut v_cmp_7564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7565_ =
        leanh::lean_alloc_closure(l_Std_ExtDTreeMap_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_7565_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7565_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7565_, 2, v_cmp_7564_);
    leanh::lean_closure_set(v___x_7565_, 3, leanh::lean_box(0));
    return v___x_7565_;
}
pub unsafe fn l_Std_ExtDTreeMap_instSDiffOfTransCmp(
    mut v_00_u03b1_7566_: *mut leanh::LeanObject,
    mut v_00_u03b2_7567_: *mut leanh::LeanObject,
    mut v_cmp_7568_: *mut leanh::LeanObject,
    mut v_inst_7569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7570_ =
        leanh::lean_alloc_closure(l_Std_ExtDTreeMap_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_7570_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7570_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7570_, 2, v_cmp_7568_);
    leanh::lean_closure_set(v___x_7570_, 3, leanh::lean_box(0));
    return v___x_7570_;
}
pub unsafe fn l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(
    mut v___f_7574_: *mut leanh::LeanObject,
    mut v___x_7575_: *mut leanh::LeanObject,
    mut v_m_7576_: *mut leanh::LeanObject,
    mut v_prec_7577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7578_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___closed__1;
    v___x_7579_ = leanh::lean_box(0);
    v___x_7580_ = l_Std_ExtDTreeMap_foldr___redArg___closed__9;
    v___x_7581_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7580_,
        v___f_7574_,
        v___x_7579_,
        v_m_7576_,
    );
    v___x_7582_ = l_List_repr___redArg(v___x_7575_, v___x_7581_);
    v___x_7583_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7583_, 0, v___x_7578_);
    leanh::lean_ctor_set(v___x_7583_, 1, v___x_7582_);
    v___x_7584_ = l_Repr_addAppParen(v___x_7583_, v_prec_7577_);
    return v___x_7584_;
}
pub unsafe fn l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed(
    mut v___f_7585_: *mut leanh::LeanObject,
    mut v___x_7586_: *mut leanh::LeanObject,
    mut v_m_7587_: *mut leanh::LeanObject,
    mut v_prec_7588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7589_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1(
        v___f_7585_,
        v___x_7586_,
        v_m_7587_,
        v_prec_7588_,
    );
    leanh::lean_dec(v_prec_7588_);
    return v_res_7589_;
}
pub unsafe fn l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(
    mut v_inst_7590_: *mut leanh::LeanObject,
    mut v_inst_7591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7592_ = l_Std_ExtDTreeMap_toList___redArg___closed__0;
    v___x_7593_ =
        leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_7593_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7593_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_7593_, 2, v_inst_7590_);
    leanh::lean_closure_set(v___x_7593_, 3, v_inst_7591_);
    v___f_7594_ = leanh::lean_alloc_closure(
        l_Std_ExtDTreeMap_instReprOfTransCmp___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_7594_, 0, v___f_7592_);
    leanh::lean_closure_set(v___f_7594_, 1, v___x_7593_);
    return v___f_7594_;
}
pub unsafe fn l_Std_ExtDTreeMap_instReprOfTransCmp(
    mut v_00_u03b1_7595_: *mut leanh::LeanObject,
    mut v_00_u03b2_7596_: *mut leanh::LeanObject,
    mut v_cmp_7597_: *mut leanh::LeanObject,
    mut v_inst_7598_: *mut leanh::LeanObject,
    mut v_inst_7599_: *mut leanh::LeanObject,
    mut v_inst_7600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7601_ = l_Std_ExtDTreeMap_instReprOfTransCmp___redArg(v_inst_7599_, v_inst_7600_);
    return v___x_7601_;
}
pub unsafe fn l_Std_ExtDTreeMap_instReprOfTransCmp___boxed(
    mut v_00_u03b1_7602_: *mut leanh::LeanObject,
    mut v_00_u03b2_7603_: *mut leanh::LeanObject,
    mut v_cmp_7604_: *mut leanh::LeanObject,
    mut v_inst_7605_: *mut leanh::LeanObject,
    mut v_inst_7606_: *mut leanh::LeanObject,
    mut v_inst_7607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7608_ = l_Std_ExtDTreeMap_instReprOfTransCmp(
        v_00_u03b1_7602_,
        v_00_u03b2_7603_,
        v_cmp_7604_,
        v_inst_7605_,
        v_inst_7606_,
        v_inst_7607_,
    );
    leanh::lean_dec_ref(v_cmp_7604_);
    return v_res_7608_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtDTreeMap_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtDTreeMap_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_ExtDTreeMap___auto__1 = _init_l_Std_ExtDTreeMap___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtDTreeMap___auto__1);
    l_Std_ExtDTreeMap_ofList___auto__1 = _init_l_Std_ExtDTreeMap_ofList___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtDTreeMap_ofList___auto__1);
    l_Std_ExtDTreeMap_ofArray___auto__1 = _init_l_Std_ExtDTreeMap_ofArray___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtDTreeMap_ofArray___auto__1);
    l_Std_ExtDTreeMap_Const_ofList___auto__1 = _init_l_Std_ExtDTreeMap_Const_ofList___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtDTreeMap_Const_ofList___auto__1);
    l_Std_ExtDTreeMap_Const_ofArray___auto__1 = _init_l_Std_ExtDTreeMap_Const_ofArray___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtDTreeMap_Const_ofArray___auto__1);
    l_Std_ExtDTreeMap_Const_unitOfList___auto__1 =
        _init_l_Std_ExtDTreeMap_Const_unitOfList___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtDTreeMap_Const_unitOfList___auto__1);
    l_Std_ExtDTreeMap_Const_unitOfArray___auto__1 =
        _init_l_Std_ExtDTreeMap_Const_unitOfArray___auto__1();
    leanh::lean_mark_persistent(l_Std_ExtDTreeMap_Const_unitOfArray___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ExtDTreeMap_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtDTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtDTreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_ExtDTreeMap_Basic(builtin);
}