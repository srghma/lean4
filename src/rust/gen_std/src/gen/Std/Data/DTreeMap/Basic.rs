// Lean compiler output
// Module: Std.Data.DTreeMap.Basic
// Imports: Std.Data.DTreeMap.Internal.WF.Defs
use crate::ffi::{
    lean_array_push, lean_array_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_string_utf8_byte_size,
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
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_Lean_replaceRef, l_String_toRawSubstring_x27, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_alter___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_beq___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_modify___redArg,
    l_Std_DTreeMap_Internal_Impl_alter___redArg, l_Std_DTreeMap_Internal_Impl_beq___redArg,
    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg,
    l_Std_DTreeMap_Internal_Impl_erase___redArg, l_Std_DTreeMap_Internal_Impl_filter___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___redArg, l_Std_DTreeMap_Internal_Impl_link___redArg,
    l_Std_DTreeMap_Internal_Impl_link2___redArg, l_Std_DTreeMap_Internal_Impl_maxView___redArg,
    l_Std_DTreeMap_Internal_Impl_minView___redArg, l_Std_DTreeMap_Internal_Impl_modify___redArg,
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
    l_Std_DTreeMap_Internal_Impl_contains___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg, l_Std_DTreeMap_Internal_Impl_foldl___redArg,
    l_Std_DTreeMap_Internal_Impl_foldlM___redArg, l_Std_DTreeMap_Internal_Impl_foldrM___redArg,
    l_Std_DTreeMap_Internal_Impl_forInStep___redArg, l_Std_DTreeMap_Internal_Impl_get___redArg,
    l_Std_DTreeMap_Internal_Impl_get_x3f___redArg, l_Std_DTreeMap_Internal_Impl_get_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_getD___redArg, l_Std_DTreeMap_Internal_Impl_getEntry___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryD___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKey___redArg, l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyD___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg,
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
use crate::r#gen::Std::Data::DTreeMap::Internal::WF::Defs::{
    initialize_Std_Data_DTreeMap_Internal_WF_Defs,
    runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs,
};
pub static l_Std_DTreeMap___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DTreeMap___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_DTreeMap___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DTreeMap___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DTreeMap___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap___auto__1___closed__14_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap___auto__1___closed__17_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16710690322389477741 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DTreeMap___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_DTreeMap___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [68, 84, 114, 101, 101, 77, 97, 112, 0],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            2223199789710442946 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DTreeMap_term___x7em___00__closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            3431088055262456620 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__4_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__6_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__8_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DTreeMap_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,2223199789710442946 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,13529677889046400365 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_foldr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_foldr___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_foldr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_foldr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_partition___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_partition___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_partition___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_any___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DTreeMap_any___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_any___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_keys___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DTreeMap_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_keys___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_keys___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_keysArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DTreeMap_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_keysArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_keysArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_values___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DTreeMap_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_values___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_values___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_valuesArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_valuesArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_valuesArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DTreeMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DTreeMap_ofList___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DTreeMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DTreeMap_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DTreeMap_ofArray___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Const_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Const_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Const_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Const_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DTreeMap_Const_ofList___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Const_toArray___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DTreeMap_Const_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Const_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Const_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Const_toArray___redArg___closed__1_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_DTreeMap_Const_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Const_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DTreeMap_Const_ofArray___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_DTreeMap_Const_unitOfList___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_DTreeMap_Const_unitOfArray___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32,
        0,
    ],
};
static mut l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4747_ = l_Std_DTreeMap___auto__1___closed__10;
    v___x_4748_ = l_Lean_mkAtom(v___x_4747_);
    return v___x_4748_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4749_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__12_once),
        _init_l_Std_DTreeMap___auto__1___closed__12,
    );
    v___x_4750_ = l_Std_DTreeMap___auto__1___closed__5;
    v___x_4751_ = lean_array_push(v___x_4750_, v___x_4749_);
    return v___x_4751_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4753_ = l_Std_DTreeMap___auto__1___closed__14;
    v___x_4754_ = lean_string_utf8_byte_size(v___x_4753_);
    return v___x_4754_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4755_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__15_once),
        _init_l_Std_DTreeMap___auto__1___closed__15,
    );
    v___x_4756_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4757_ = l_Std_DTreeMap___auto__1___closed__14;
    v___x_4758_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4758_, 0, v___x_4757_);
    crate::leanh::lean_ctor_set(v___x_4758_, 1, v___x_4756_);
    crate::leanh::lean_ctor_set(v___x_4758_, 2, v___x_4755_);
    return v___x_4758_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4761_ = crate::leanh::lean_box(0);
    v___x_4762_ = l_Std_DTreeMap___auto__1___closed__17;
    v___x_4763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__16_once),
        _init_l_Std_DTreeMap___auto__1___closed__16,
    );
    v___x_4764_ = crate::leanh::lean_box(2);
    v___x_4765_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4765_, 0, v___x_4764_);
    crate::leanh::lean_ctor_set(v___x_4765_, 1, v___x_4763_);
    crate::leanh::lean_ctor_set(v___x_4765_, 2, v___x_4762_);
    crate::leanh::lean_ctor_set(v___x_4765_, 3, v___x_4761_);
    return v___x_4765_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__18_once),
        _init_l_Std_DTreeMap___auto__1___closed__18,
    );
    v___x_4767_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__13_once),
        _init_l_Std_DTreeMap___auto__1___closed__13,
    );
    v___x_4768_ = lean_array_push(v___x_4767_, v___x_4766_);
    return v___x_4768_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4769_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__19_once),
        _init_l_Std_DTreeMap___auto__1___closed__19,
    );
    v___x_4770_ = l_Std_DTreeMap___auto__1___closed__11;
    v___x_4771_ = crate::leanh::lean_box(2);
    v___x_4772_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4772_, 0, v___x_4771_);
    crate::leanh::lean_ctor_set(v___x_4772_, 1, v___x_4770_);
    crate::leanh::lean_ctor_set(v___x_4772_, 2, v___x_4769_);
    return v___x_4772_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4773_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__20_once),
        _init_l_Std_DTreeMap___auto__1___closed__20,
    );
    v___x_4774_ = l_Std_DTreeMap___auto__1___closed__5;
    v___x_4775_ = lean_array_push(v___x_4774_, v___x_4773_);
    return v___x_4775_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__21_once),
        _init_l_Std_DTreeMap___auto__1___closed__21,
    );
    v___x_4777_ = l_Std_DTreeMap___auto__1___closed__9;
    v___x_4778_ = crate::leanh::lean_box(2);
    v___x_4779_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4779_, 0, v___x_4778_);
    crate::leanh::lean_ctor_set(v___x_4779_, 1, v___x_4777_);
    crate::leanh::lean_ctor_set(v___x_4779_, 2, v___x_4776_);
    return v___x_4779_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__22_once),
        _init_l_Std_DTreeMap___auto__1___closed__22,
    );
    v___x_4781_ = l_Std_DTreeMap___auto__1___closed__5;
    v___x_4782_ = lean_array_push(v___x_4781_, v___x_4780_);
    return v___x_4782_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__23_once),
        _init_l_Std_DTreeMap___auto__1___closed__23,
    );
    v___x_4784_ = l_Std_DTreeMap___auto__1___closed__7;
    v___x_4785_ = crate::leanh::lean_box(2);
    v___x_4786_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4786_, 0, v___x_4785_);
    crate::leanh::lean_ctor_set(v___x_4786_, 1, v___x_4784_);
    crate::leanh::lean_ctor_set(v___x_4786_, 2, v___x_4783_);
    return v___x_4786_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__24_once),
        _init_l_Std_DTreeMap___auto__1___closed__24,
    );
    v___x_4788_ = l_Std_DTreeMap___auto__1___closed__5;
    v___x_4789_ = lean_array_push(v___x_4788_, v___x_4787_);
    return v___x_4789_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4790_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__25_once),
        _init_l_Std_DTreeMap___auto__1___closed__25,
    );
    v___x_4791_ = l_Std_DTreeMap___auto__1___closed__4;
    v___x_4792_ = crate::leanh::lean_box(2);
    v___x_4793_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4793_, 0, v___x_4792_);
    crate::leanh::lean_ctor_set(v___x_4793_, 1, v___x_4791_);
    crate::leanh::lean_ctor_set(v___x_4793_, 2, v___x_4790_);
    return v___x_4793_;
}
pub unsafe fn _init_l_Std_DTreeMap___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4794_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26_once),
        _init_l_Std_DTreeMap___auto__1___closed__26,
    );
    return v___x_4794_;
}
pub unsafe fn l_Std_DTreeMap_instCoeTypeForall(
    mut v_00_u03b1_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = crate::leanh::lean_box(0);
    return v___x_4796_;
}
pub unsafe fn l_Std_DTreeMap_empty(
    mut v_00_u03b1_4797_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4798_: *mut crate::leanh::LeanObject,
    mut v_cmp_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = crate::leanh::lean_box(1);
    return v___x_4800_;
}
pub unsafe fn l_Std_DTreeMap_empty___boxed(
    mut v_00_u03b1_4801_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4802_: *mut crate::leanh::LeanObject,
    mut v_cmp_4803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4804_ = l_Std_DTreeMap_empty(v_00_u03b1_4801_, v_00_u03b2_4802_, v_cmp_4803_);
    crate::leanh::lean_dec_ref(v_cmp_4803_);
    return v_res_4804_;
}
pub unsafe fn l_Std_DTreeMap_instEmptyCollection(
    mut v_00_u03b1_4805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4806_: *mut crate::leanh::LeanObject,
    mut v_cmp_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4808_ = crate::leanh::lean_box(1);
    return v___x_4808_;
}
pub unsafe fn l_Std_DTreeMap_instEmptyCollection___boxed(
    mut v_00_u03b1_4809_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4810_: *mut crate::leanh::LeanObject,
    mut v_cmp_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4812_ =
        l_Std_DTreeMap_instEmptyCollection(v_00_u03b1_4809_, v_00_u03b2_4810_, v_cmp_4811_);
    crate::leanh::lean_dec_ref(v_cmp_4811_);
    return v_res_4812_;
}
pub unsafe fn l_Std_DTreeMap_instInhabited(
    mut v_00_u03b1_4813_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4814_: *mut crate::leanh::LeanObject,
    mut v_cmp_4815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4816_ = crate::leanh::lean_box(1);
    return v___x_4816_;
}
pub unsafe fn l_Std_DTreeMap_instInhabited___boxed(
    mut v_00_u03b1_4817_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4818_: *mut crate::leanh::LeanObject,
    mut v_cmp_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4820_ = l_Std_DTreeMap_instInhabited(v_00_u03b1_4817_, v_00_u03b2_4818_, v_cmp_4819_);
    crate::leanh::lean_dec_ref(v_cmp_4819_);
    return v_res_4820_;
}
pub unsafe fn _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4858_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__3;
    v___x_4859_ = l_String_toRawSubstring_x27(v___x_4858_);
    return v___x_4859_;
}
pub unsafe fn l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(
    mut v_x_4877_: *mut crate::leanh::LeanObject,
    mut v_a_4878_: *mut crate::leanh::LeanObject,
    mut v_a_4879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: u8 = 0;
    v___x_4880_ = l_Std_DTreeMap_term___x7em___00__closed__3;
    crate::leanh::lean_inc(v_x_4877_);
    v___x_4881_ = l_Lean_Syntax_isOfKind(v_x_4877_, v___x_4880_);
    if v___x_4881_ == 0 {
        let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4877_);
        v___x_4882_ = crate::leanh::lean_box(1);
        v___x_4883_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4883_, 0, v___x_4882_);
        crate::leanh::lean_ctor_set(v___x_4883_, 1, v_a_4879_);
        return v___x_4883_;
    } else {
        let mut v_quotContext_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4891_: u8 = 0;
        let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_4884_ = crate::leanh::lean_ctor_get(v_a_4878_, 1);
        v_currMacroScope_4885_ = crate::leanh::lean_ctor_get(v_a_4878_, 2);
        v_ref_4886_ = crate::leanh::lean_ctor_get(v_a_4878_, 5);
        v___x_4887_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4888_ = l_Lean_Syntax_getArg(v_x_4877_, v___x_4887_);
        v___x_4889_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_4890_ = l_Lean_Syntax_getArg(v_x_4877_, v___x_4889_);
        crate::leanh::lean_dec(v_x_4877_);
        v___x_4891_ = 0;
        v___x_4892_ = l_Lean_SourceInfo_fromRef(v_ref_4886_, v___x_4891_);
        v___x_4893_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2;
        v___x_4894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4_once), _init_l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__4);
        v___x_4895_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__5;
        crate::leanh::lean_inc(v_currMacroScope_4885_);
        crate::leanh::lean_inc(v_quotContext_4884_);
        v___x_4896_ =
            l_Lean_addMacroScope(v_quotContext_4884_, v___x_4895_, v_currMacroScope_4885_);
        v___x_4897_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__10;
        crate::leanh::lean_inc_n(v___x_4892_, 2);
        v___x_4898_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4898_, 0, v___x_4892_);
        crate::leanh::lean_ctor_set(v___x_4898_, 1, v___x_4894_);
        crate::leanh::lean_ctor_set(v___x_4898_, 2, v___x_4896_);
        crate::leanh::lean_ctor_set(v___x_4898_, 3, v___x_4897_);
        v___x_4899_ = l_Std_DTreeMap___auto__1___closed__9;
        v___x_4900_ = l_Lean_Syntax_node2(v___x_4892_, v___x_4899_, v___x_4888_, v___x_4890_);
        v___x_4901_ = l_Lean_Syntax_node2(v___x_4892_, v___x_4893_, v___x_4898_, v___x_4900_);
        v___x_4902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4902_, 0, v___x_4901_);
        crate::leanh::lean_ctor_set(v___x_4902_, 1, v_a_4879_);
        return v___x_4902_;
    }
}
pub unsafe fn l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___boxed(
    mut v_x_4903_: *mut crate::leanh::LeanObject,
    mut v_a_4904_: *mut crate::leanh::LeanObject,
    mut v_a_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4906_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1(v_x_4903_, v_a_4904_, v_a_4905_);
    crate::leanh::lean_dec_ref(v_a_4904_);
    return v_res_4906_;
}
pub unsafe fn l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(
    mut v_x_4910_: *mut crate::leanh::LeanObject,
    mut v_a_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: u8 = 0;
    v___x_4913_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______macroRules__Std__DTreeMap__term___x7em____1___closed__2;
    crate::leanh::lean_inc(v_x_4910_);
    v___x_4914_ = l_Lean_Syntax_isOfKind(v_x_4910_, v___x_4913_);
    if v___x_4914_ == 0 {
        let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4910_);
        v___x_4915_ = crate::leanh::lean_box(0);
        v___x_4916_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4916_, 0, v___x_4915_);
        crate::leanh::lean_ctor_set(v___x_4916_, 1, v_a_4912_);
        return v___x_4916_;
    } else {
        let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4920_: u8 = 0;
        v___x_4917_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4918_ = l_Lean_Syntax_getArg(v_x_4910_, v___x_4917_);
        v___x_4919_ = l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_4918_);
        v___x_4920_ = l_Lean_Syntax_isOfKind(v___x_4918_, v___x_4919_);
        if v___x_4920_ == 0 {
            let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4918_);
            crate::leanh::lean_dec(v_x_4910_);
            v___x_4921_ = crate::leanh::lean_box(0);
            v___x_4922_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4922_, 0, v___x_4921_);
            crate::leanh::lean_ctor_set(v___x_4922_, 1, v_a_4912_);
            return v___x_4922_;
        } else {
            let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4926_: u8 = 0;
            v___x_4923_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4924_ = l_Lean_Syntax_getArg(v_x_4910_, v___x_4923_);
            crate::leanh::lean_dec(v_x_4910_);
            v___x_4925_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_4924_);
            v___x_4926_ = l_Lean_Syntax_matchesNull(v___x_4924_, v___x_4925_);
            if v___x_4926_ == 0 {
                let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_4924_);
                crate::leanh::lean_dec(v___x_4918_);
                v___x_4927_ = crate::leanh::lean_box(0);
                v___x_4928_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4928_, 0, v___x_4927_);
                crate::leanh::lean_ctor_set(v___x_4928_, 1, v_a_4912_);
                return v___x_4928_;
            } else {
                let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4932_: u8 = 0;
                let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4929_ = l_Lean_Syntax_getArg(v___x_4924_, v___x_4917_);
                v___x_4930_ = l_Lean_Syntax_getArg(v___x_4924_, v___x_4923_);
                crate::leanh::lean_dec(v___x_4924_);
                v_ref_4931_ = l_Lean_replaceRef(v___x_4918_, v_a_4911_);
                crate::leanh::lean_dec(v___x_4918_);
                v___x_4932_ = 0;
                v___x_4933_ = l_Lean_SourceInfo_fromRef(v_ref_4931_, v___x_4932_);
                crate::leanh::lean_dec(v_ref_4931_);
                v___x_4934_ = l_Std_DTreeMap_term___x7em___00__closed__3;
                v___x_4935_ = l_Std_DTreeMap_term___x7em___00__closed__6;
                crate::leanh::lean_inc(v___x_4933_);
                v___x_4936_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4936_, 0, v___x_4933_);
                crate::leanh::lean_ctor_set(v___x_4936_, 1, v___x_4935_);
                v___x_4937_ = l_Lean_Syntax_node3(
                    v___x_4933_,
                    v___x_4934_,
                    v___x_4929_,
                    v___x_4936_,
                    v___x_4930_,
                );
                v___x_4938_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4938_, 0, v___x_4937_);
                crate::leanh::lean_ctor_set(v___x_4938_, 1, v_a_4912_);
                return v___x_4938_;
            }
        }
    }
}
pub unsafe fn l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1___boxed(
    mut v_x_4939_: *mut crate::leanh::LeanObject,
    mut v_a_4940_: *mut crate::leanh::LeanObject,
    mut v_a_4941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4942_ =
        l_Std_DTreeMap___aux__Std__Data__DTreeMap__Basic______unexpand__Std__DTreeMap__Equiv__1(
            v_x_4939_, v_a_4940_, v_a_4941_,
        );
    crate::leanh::lean_dec(v_a_4940_);
    return v_res_4942_;
}
pub unsafe fn l_Std_DTreeMap_insert___redArg(
    mut v_cmp_4943_: *mut crate::leanh::LeanObject,
    mut v_t_4944_: *mut crate::leanh::LeanObject,
    mut v_a_4945_: *mut crate::leanh::LeanObject,
    mut v_b_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4947_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4943_, v_a_4945_, v_b_4946_, v_t_4944_);
    return v___x_4947_;
}
pub unsafe fn l_Std_DTreeMap_insert(
    mut v_00_u03b1_4948_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4949_: *mut crate::leanh::LeanObject,
    mut v_cmp_4950_: *mut crate::leanh::LeanObject,
    mut v_t_4951_: *mut crate::leanh::LeanObject,
    mut v_a_4952_: *mut crate::leanh::LeanObject,
    mut v_b_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4954_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_4950_, v_a_4952_, v_b_4953_, v_t_4951_);
    return v___x_4954_;
}
pub unsafe fn l_Std_DTreeMap_instSingletonSigma___redArg___lam__0(
    mut v_cmp_4955_: *mut crate::leanh::LeanObject,
    mut v_e_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4957_ = crate::leanh::lean_ctor_get(v_e_4956_, 0);
    crate::leanh::lean_inc(v_fst_4957_);
    v_snd_4958_ = crate::leanh::lean_ctor_get(v_e_4956_, 1);
    crate::leanh::lean_inc(v_snd_4958_);
    crate::leanh::lean_dec_ref(v_e_4956_);
    v___x_4959_ = crate::leanh::lean_box(1);
    v___x_4960_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_4955_,
        v_fst_4957_,
        v_snd_4958_,
        v___x_4959_,
    );
    return v___x_4960_;
}
pub unsafe fn l_Std_DTreeMap_instSingletonSigma___redArg(
    mut v_cmp_4961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4962_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instSingletonSigma___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4962_, 0, v_cmp_4961_);
    return v___f_4962_;
}
pub unsafe fn l_Std_DTreeMap_instSingletonSigma(
    mut v_00_u03b1_4963_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4964_: *mut crate::leanh::LeanObject,
    mut v_cmp_4965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4966_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instSingletonSigma___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4966_, 0, v_cmp_4965_);
    return v___f_4966_;
}
pub unsafe fn l_Std_DTreeMap_instInsertSigma___redArg___lam__0(
    mut v_cmp_4967_: *mut crate::leanh::LeanObject,
    mut v_e_4968_: *mut crate::leanh::LeanObject,
    mut v_s_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4970_ = crate::leanh::lean_ctor_get(v_e_4968_, 0);
    crate::leanh::lean_inc(v_fst_4970_);
    v_snd_4971_ = crate::leanh::lean_ctor_get(v_e_4968_, 1);
    crate::leanh::lean_inc(v_snd_4971_);
    crate::leanh::lean_dec_ref(v_e_4968_);
    v___x_4972_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_4967_,
        v_fst_4970_,
        v_snd_4971_,
        v_s_4969_,
    );
    return v___x_4972_;
}
pub unsafe fn l_Std_DTreeMap_instInsertSigma___redArg(
    mut v_cmp_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4974_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instInsertSigma___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4974_, 0, v_cmp_4973_);
    return v___f_4974_;
}
pub unsafe fn l_Std_DTreeMap_instInsertSigma(
    mut v_00_u03b1_4975_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4976_: *mut crate::leanh::LeanObject,
    mut v_cmp_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4978_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instInsertSigma___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4978_, 0, v_cmp_4977_);
    return v___f_4978_;
}
pub unsafe fn l_Std_DTreeMap_insertIfNew___redArg(
    mut v_cmp_4979_: *mut crate::leanh::LeanObject,
    mut v_t_4980_: *mut crate::leanh::LeanObject,
    mut v_a_4981_: *mut crate::leanh::LeanObject,
    mut v_b_4982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4983_: u8 = 0;
    crate::leanh::lean_inc(v_t_4980_);
    crate::leanh::lean_inc(v_a_4981_);
    crate::leanh::lean_inc_ref(v_cmp_4979_);
    v___x_4983_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4979_, v_a_4981_, v_t_4980_);
    if v___x_4983_ == 0 {
        let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4984_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4979_,
            v_a_4981_,
            v_b_4982_,
            v_t_4980_,
        );
        return v___x_4984_;
    } else {
        crate::leanh::lean_dec(v_b_4982_);
        crate::leanh::lean_dec(v_a_4981_);
        crate::leanh::lean_dec_ref(v_cmp_4979_);
        return v_t_4980_;
    }
}
pub unsafe fn l_Std_DTreeMap_insertIfNew(
    mut v_00_u03b1_4985_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4986_: *mut crate::leanh::LeanObject,
    mut v_cmp_4987_: *mut crate::leanh::LeanObject,
    mut v_t_4988_: *mut crate::leanh::LeanObject,
    mut v_a_4989_: *mut crate::leanh::LeanObject,
    mut v_b_4990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4991_: u8 = 0;
    crate::leanh::lean_inc(v_t_4988_);
    crate::leanh::lean_inc(v_a_4989_);
    crate::leanh::lean_inc_ref(v_cmp_4987_);
    v___x_4991_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4987_, v_a_4989_, v_t_4988_);
    if v___x_4991_ == 0 {
        let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4992_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4987_,
            v_a_4989_,
            v_b_4990_,
            v_t_4988_,
        );
        return v___x_4992_;
    } else {
        crate::leanh::lean_dec(v_b_4990_);
        crate::leanh::lean_dec(v_a_4989_);
        crate::leanh::lean_dec_ref(v_cmp_4987_);
        return v_t_4988_;
    }
}
pub unsafe fn l_Std_DTreeMap_containsThenInsert___redArg(
    mut v_cmp_4993_: *mut crate::leanh::LeanObject,
    mut v_t_4994_: *mut crate::leanh::LeanObject,
    mut v_a_4995_: *mut crate::leanh::LeanObject,
    mut v_b_4996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: u8 = 0;
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4997_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_4994_);
                v_m_4998_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_4993_,
                    v_a_4995_,
                    v_b_4996_,
                    v_t_4994_,
                );
                if crate::leanh::lean_obj_tag(v_m_4998_) == 0 {
                    v_size_5004_ = crate::leanh::lean_ctor_get(v_m_4998_, 0);
                    crate::leanh::lean_inc(v_size_5004_);
                    v___y_5000_ = v_size_5004_;
                    state = 1;
                    continue;
                } else {
                    v___x_5005_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5000_ = v___x_5005_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5001_ = lean_nat_dec_eq(v_sz_4997_, v___y_5000_);
                crate::leanh::lean_dec(v___y_5000_);
                crate::leanh::lean_dec(v_sz_4997_);
                v___x_5002_ = crate::leanh::lean_box((v___x_5001_) as usize);
                v___x_5003_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5003_, 0, v___x_5002_);
                crate::leanh::lean_ctor_set(v___x_5003_, 1, v_m_4998_);
                return v___x_5003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_containsThenInsert(
    mut v_00_u03b1_5006_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5007_: *mut crate::leanh::LeanObject,
    mut v_cmp_5008_: *mut crate::leanh::LeanObject,
    mut v_t_5009_: *mut crate::leanh::LeanObject,
    mut v_a_5010_: *mut crate::leanh::LeanObject,
    mut v_b_5011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_5012_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_size___redArg(v_t_5009_);
                v_m_5013_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_5008_,
                    v_a_5010_,
                    v_b_5011_,
                    v_t_5009_,
                );
                if crate::leanh::lean_obj_tag(v_m_5013_) == 0 {
                    v_size_5019_ = crate::leanh::lean_ctor_get(v_m_5013_, 0);
                    crate::leanh::lean_inc(v_size_5019_);
                    v___y_5015_ = v_size_5019_;
                    state = 1;
                    continue;
                } else {
                    v___x_5020_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5015_ = v___x_5020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5016_ = lean_nat_dec_eq(v_sz_5012_, v___y_5015_);
                crate::leanh::lean_dec(v___y_5015_);
                crate::leanh::lean_dec(v_sz_5012_);
                v___x_5017_ = crate::leanh::lean_box((v___x_5016_) as usize);
                v___x_5018_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5018_, 0, v___x_5017_);
                crate::leanh::lean_ctor_set(v___x_5018_, 1, v_m_5013_);
                return v___x_5018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_containsThenInsertIfNew___redArg(
    mut v_cmp_5021_: *mut crate::leanh::LeanObject,
    mut v_t_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_b_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5025_: u8 = 0;
    crate::leanh::lean_inc(v_t_5022_);
    crate::leanh::lean_inc(v_a_5023_);
    crate::leanh::lean_inc_ref(v_cmp_5021_);
    v___x_5025_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5021_, v_a_5023_, v_t_5022_);
    if v___x_5025_ == 0 {
        let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5026_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_5021_,
            v_a_5023_,
            v_b_5024_,
            v_t_5022_,
        );
        v___x_5027_ = crate::leanh::lean_box((v___x_5025_) as usize);
        v___x_5028_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5028_, 0, v___x_5027_);
        crate::leanh::lean_ctor_set(v___x_5028_, 1, v___x_5026_);
        return v___x_5028_;
    } else {
        let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_5024_);
        crate::leanh::lean_dec(v_a_5023_);
        crate::leanh::lean_dec_ref(v_cmp_5021_);
        v___x_5029_ = crate::leanh::lean_box((v___x_5025_) as usize);
        v___x_5030_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5030_, 0, v___x_5029_);
        crate::leanh::lean_ctor_set(v___x_5030_, 1, v_t_5022_);
        return v___x_5030_;
    }
}
pub unsafe fn l_Std_DTreeMap_containsThenInsertIfNew(
    mut v_00_u03b1_5031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5032_: *mut crate::leanh::LeanObject,
    mut v_cmp_5033_: *mut crate::leanh::LeanObject,
    mut v_t_5034_: *mut crate::leanh::LeanObject,
    mut v_a_5035_: *mut crate::leanh::LeanObject,
    mut v_b_5036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5037_: u8 = 0;
    crate::leanh::lean_inc(v_t_5034_);
    crate::leanh::lean_inc(v_a_5035_);
    crate::leanh::lean_inc_ref(v_cmp_5033_);
    v___x_5037_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5033_, v_a_5035_, v_t_5034_);
    if v___x_5037_ == 0 {
        let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5038_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_5033_,
            v_a_5035_,
            v_b_5036_,
            v_t_5034_,
        );
        v___x_5039_ = crate::leanh::lean_box((v___x_5037_) as usize);
        v___x_5040_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5040_, 0, v___x_5039_);
        crate::leanh::lean_ctor_set(v___x_5040_, 1, v___x_5038_);
        return v___x_5040_;
    } else {
        let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_5036_);
        crate::leanh::lean_dec(v_a_5035_);
        crate::leanh::lean_dec_ref(v_cmp_5033_);
        v___x_5041_ = crate::leanh::lean_box((v___x_5037_) as usize);
        v___x_5042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5042_, 0, v___x_5041_);
        crate::leanh::lean_ctor_set(v___x_5042_, 1, v_t_5034_);
        return v___x_5042_;
    }
}
pub unsafe fn l_Std_DTreeMap_getThenInsertIfNew_x3f___redArg(
    mut v_cmp_5043_: *mut crate::leanh::LeanObject,
    mut v_t_5044_: *mut crate::leanh::LeanObject,
    mut v_a_5045_: *mut crate::leanh::LeanObject,
    mut v_b_5046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_5045_);
    crate::leanh::lean_inc(v_t_5044_);
    crate::leanh::lean_inc_ref(v_cmp_5043_);
    v___x_5047_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_5043_, v_t_5044_, v_a_5045_);
    if crate::leanh::lean_obj_tag(v___x_5047_) == 0 {
        let mut v___x_5048_: u8 = 0;
        crate::leanh::lean_inc(v_t_5044_);
        crate::leanh::lean_inc(v_a_5045_);
        crate::leanh::lean_inc_ref(v_cmp_5043_);
        v___x_5048_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5043_, v_a_5045_, v_t_5044_);
        if v___x_5048_ == 0 {
            let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5049_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_5043_,
                v_a_5045_,
                v_b_5046_,
                v_t_5044_,
            );
            v___x_5050_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5050_, 0, v___x_5047_);
            crate::leanh::lean_ctor_set(v___x_5050_, 1, v___x_5049_);
            return v___x_5050_;
        } else {
            let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_5046_);
            crate::leanh::lean_dec(v_a_5045_);
            crate::leanh::lean_dec_ref(v_cmp_5043_);
            v___x_5051_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5051_, 0, v___x_5047_);
            crate::leanh::lean_ctor_set(v___x_5051_, 1, v_t_5044_);
            return v___x_5051_;
        }
    } else {
        let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_5046_);
        crate::leanh::lean_dec(v_a_5045_);
        crate::leanh::lean_dec_ref(v_cmp_5043_);
        v___x_5052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5052_, 0, v___x_5047_);
        crate::leanh::lean_ctor_set(v___x_5052_, 1, v_t_5044_);
        return v___x_5052_;
    }
}
pub unsafe fn l_Std_DTreeMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_5053_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5054_: *mut crate::leanh::LeanObject,
    mut v_cmp_5055_: *mut crate::leanh::LeanObject,
    mut v_inst_5056_: *mut crate::leanh::LeanObject,
    mut v_t_5057_: *mut crate::leanh::LeanObject,
    mut v_a_5058_: *mut crate::leanh::LeanObject,
    mut v_b_5059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_5058_);
    crate::leanh::lean_inc(v_t_5057_);
    crate::leanh::lean_inc_ref(v_cmp_5055_);
    v___x_5060_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_5055_, v_t_5057_, v_a_5058_);
    if crate::leanh::lean_obj_tag(v___x_5060_) == 0 {
        let mut v___x_5061_: u8 = 0;
        crate::leanh::lean_inc(v_t_5057_);
        crate::leanh::lean_inc(v_a_5058_);
        crate::leanh::lean_inc_ref(v_cmp_5055_);
        v___x_5061_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5055_, v_a_5058_, v_t_5057_);
        if v___x_5061_ == 0 {
            let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5062_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_5055_,
                v_a_5058_,
                v_b_5059_,
                v_t_5057_,
            );
            v___x_5063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5063_, 0, v___x_5060_);
            crate::leanh::lean_ctor_set(v___x_5063_, 1, v___x_5062_);
            return v___x_5063_;
        } else {
            let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_5059_);
            crate::leanh::lean_dec(v_a_5058_);
            crate::leanh::lean_dec_ref(v_cmp_5055_);
            v___x_5064_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5064_, 0, v___x_5060_);
            crate::leanh::lean_ctor_set(v___x_5064_, 1, v_t_5057_);
            return v___x_5064_;
        }
    } else {
        let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_5059_);
        crate::leanh::lean_dec(v_a_5058_);
        crate::leanh::lean_dec_ref(v_cmp_5055_);
        v___x_5065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5065_, 0, v___x_5060_);
        crate::leanh::lean_ctor_set(v___x_5065_, 1, v_t_5057_);
        return v___x_5065_;
    }
}
pub unsafe fn l_Std_DTreeMap_contains___redArg(
    mut v_cmp_5066_: *mut crate::leanh::LeanObject,
    mut v_t_5067_: *mut crate::leanh::LeanObject,
    mut v_a_5068_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5069_: u8 = 0;
    v___x_5069_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5066_, v_a_5068_, v_t_5067_);
    return v___x_5069_;
}
pub unsafe fn l_Std_DTreeMap_contains___redArg___boxed(
    mut v_cmp_5070_: *mut crate::leanh::LeanObject,
    mut v_t_5071_: *mut crate::leanh::LeanObject,
    mut v_a_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5073_: u8 = 0;
    let mut v_r_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5073_ = l_Std_DTreeMap_contains___redArg(v_cmp_5070_, v_t_5071_, v_a_5072_);
    v_r_5074_ = crate::leanh::lean_box((v_res_5073_) as usize);
    return v_r_5074_;
}
pub unsafe fn l_Std_DTreeMap_contains(
    mut v_00_u03b1_5075_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5076_: *mut crate::leanh::LeanObject,
    mut v_cmp_5077_: *mut crate::leanh::LeanObject,
    mut v_t_5078_: *mut crate::leanh::LeanObject,
    mut v_a_5079_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5080_: u8 = 0;
    v___x_5080_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5077_, v_a_5079_, v_t_5078_);
    return v___x_5080_;
}
pub unsafe fn l_Std_DTreeMap_contains___boxed(
    mut v_00_u03b1_5081_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5082_: *mut crate::leanh::LeanObject,
    mut v_cmp_5083_: *mut crate::leanh::LeanObject,
    mut v_t_5084_: *mut crate::leanh::LeanObject,
    mut v_a_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5086_: u8 = 0;
    let mut v_r_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5086_ = l_Std_DTreeMap_contains(
        v_00_u03b1_5081_,
        v_00_u03b2_5082_,
        v_cmp_5083_,
        v_t_5084_,
        v_a_5085_,
    );
    v_r_5087_ = crate::leanh::lean_box((v_res_5086_) as usize);
    return v_r_5087_;
}
pub unsafe fn l_Std_DTreeMap_instMembership(
    mut v_00_u03b1_5088_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5089_: *mut crate::leanh::LeanObject,
    mut v_cmp_5090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5091_ = crate::leanh::lean_box(0);
    return v___x_5091_;
}
pub unsafe fn l_Std_DTreeMap_instMembership___boxed(
    mut v_00_u03b1_5092_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5093_: *mut crate::leanh::LeanObject,
    mut v_cmp_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5095_ = l_Std_DTreeMap_instMembership(v_00_u03b1_5092_, v_00_u03b2_5093_, v_cmp_5094_);
    crate::leanh::lean_dec_ref(v_cmp_5094_);
    return v_res_5095_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableMem___redArg(
    mut v_cmp_5096_: *mut crate::leanh::LeanObject,
    mut v_m_5097_: *mut crate::leanh::LeanObject,
    mut v_a_5098_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5099_: u8 = 0;
    v___x_5099_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5096_, v_a_5098_, v_m_5097_);
    return v___x_5099_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableMem___redArg___boxed(
    mut v_cmp_5100_: *mut crate::leanh::LeanObject,
    mut v_m_5101_: *mut crate::leanh::LeanObject,
    mut v_a_5102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5103_: u8 = 0;
    let mut v_r_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5103_ = l_Std_DTreeMap_instDecidableMem___redArg(v_cmp_5100_, v_m_5101_, v_a_5102_);
    v_r_5104_ = crate::leanh::lean_box((v_res_5103_) as usize);
    return v_r_5104_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableMem(
    mut v_00_u03b1_5105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5106_: *mut crate::leanh::LeanObject,
    mut v_cmp_5107_: *mut crate::leanh::LeanObject,
    mut v_m_5108_: *mut crate::leanh::LeanObject,
    mut v_a_5109_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5110_: u8 = 0;
    v___x_5110_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5107_, v_a_5109_, v_m_5108_);
    return v___x_5110_;
}
pub unsafe fn l_Std_DTreeMap_instDecidableMem___boxed(
    mut v_00_u03b1_5111_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5112_: *mut crate::leanh::LeanObject,
    mut v_cmp_5113_: *mut crate::leanh::LeanObject,
    mut v_m_5114_: *mut crate::leanh::LeanObject,
    mut v_a_5115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5116_: u8 = 0;
    let mut v_r_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5116_ = l_Std_DTreeMap_instDecidableMem(
        v_00_u03b1_5111_,
        v_00_u03b2_5112_,
        v_cmp_5113_,
        v_m_5114_,
        v_a_5115_,
    );
    v_r_5117_ = crate::leanh::lean_box((v_res_5116_) as usize);
    return v_r_5117_;
}
pub unsafe fn l_Std_DTreeMap_size___redArg(
    mut v_t_5118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5118_) == 0 {
        let mut v_size_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_5119_ = crate::leanh::lean_ctor_get(v_t_5118_, 0);
        crate::leanh::lean_inc(v_size_5119_);
        return v_size_5119_;
    } else {
        let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5120_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_5120_;
    }
}
pub unsafe fn l_Std_DTreeMap_size___redArg___boxed(
    mut v_t_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5122_ = l_Std_DTreeMap_size___redArg(v_t_5121_);
    crate::leanh::lean_dec(v_t_5121_);
    return v_res_5122_;
}
pub unsafe fn l_Std_DTreeMap_size(
    mut v_00_u03b1_5123_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5124_: *mut crate::leanh::LeanObject,
    mut v_cmp_5125_: *mut crate::leanh::LeanObject,
    mut v_t_5126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5126_) == 0 {
        let mut v_size_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_5127_ = crate::leanh::lean_ctor_get(v_t_5126_, 0);
        crate::leanh::lean_inc(v_size_5127_);
        return v_size_5127_;
    } else {
        let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5128_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_5128_;
    }
}
pub unsafe fn l_Std_DTreeMap_size___boxed(
    mut v_00_u03b1_5129_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5130_: *mut crate::leanh::LeanObject,
    mut v_cmp_5131_: *mut crate::leanh::LeanObject,
    mut v_t_5132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5133_ = l_Std_DTreeMap_size(v_00_u03b1_5129_, v_00_u03b2_5130_, v_cmp_5131_, v_t_5132_);
    crate::leanh::lean_dec(v_t_5132_);
    crate::leanh::lean_dec_ref(v_cmp_5131_);
    return v_res_5133_;
}
pub unsafe fn l_Std_DTreeMap_isEmpty___redArg(mut v_t_5134_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_5134_) == 0 {
        let mut v___x_5135_: u8 = 0;
        v___x_5135_ = 0;
        return v___x_5135_;
    } else {
        let mut v___x_5136_: u8 = 0;
        v___x_5136_ = 1;
        return v___x_5136_;
    }
}
pub unsafe fn l_Std_DTreeMap_isEmpty___redArg___boxed(
    mut v_t_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5138_: u8 = 0;
    let mut v_r_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5138_ = l_Std_DTreeMap_isEmpty___redArg(v_t_5137_);
    crate::leanh::lean_dec(v_t_5137_);
    v_r_5139_ = crate::leanh::lean_box((v_res_5138_) as usize);
    return v_r_5139_;
}
pub unsafe fn l_Std_DTreeMap_isEmpty(
    mut v_00_u03b1_5140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5141_: *mut crate::leanh::LeanObject,
    mut v_cmp_5142_: *mut crate::leanh::LeanObject,
    mut v_t_5143_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_5143_) == 0 {
        let mut v___x_5144_: u8 = 0;
        v___x_5144_ = 0;
        return v___x_5144_;
    } else {
        let mut v___x_5145_: u8 = 0;
        v___x_5145_ = 1;
        return v___x_5145_;
    }
}
pub unsafe fn l_Std_DTreeMap_isEmpty___boxed(
    mut v_00_u03b1_5146_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5147_: *mut crate::leanh::LeanObject,
    mut v_cmp_5148_: *mut crate::leanh::LeanObject,
    mut v_t_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5150_: u8 = 0;
    let mut v_r_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5150_ =
        l_Std_DTreeMap_isEmpty(v_00_u03b1_5146_, v_00_u03b2_5147_, v_cmp_5148_, v_t_5149_);
    crate::leanh::lean_dec(v_t_5149_);
    crate::leanh::lean_dec_ref(v_cmp_5148_);
    v_r_5151_ = crate::leanh::lean_box((v_res_5150_) as usize);
    return v_r_5151_;
}
pub unsafe fn l_Std_DTreeMap_erase___redArg(
    mut v_cmp_5152_: *mut crate::leanh::LeanObject,
    mut v_t_5153_: *mut crate::leanh::LeanObject,
    mut v_a_5154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5155_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_5152_, v_a_5154_, v_t_5153_);
    return v___x_5155_;
}
pub unsafe fn l_Std_DTreeMap_erase(
    mut v_00_u03b1_5156_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5157_: *mut crate::leanh::LeanObject,
    mut v_cmp_5158_: *mut crate::leanh::LeanObject,
    mut v_t_5159_: *mut crate::leanh::LeanObject,
    mut v_a_5160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5161_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_5158_, v_a_5160_, v_t_5159_);
    return v___x_5161_;
}
pub unsafe fn l_Std_DTreeMap_get_x3f___redArg(
    mut v_cmp_5162_: *mut crate::leanh::LeanObject,
    mut v_t_5163_: *mut crate::leanh::LeanObject,
    mut v_a_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5165_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_5162_, v_t_5163_, v_a_5164_);
    return v___x_5165_;
}
pub unsafe fn l_Std_DTreeMap_get_x3f(
    mut v_00_u03b1_5166_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5167_: *mut crate::leanh::LeanObject,
    mut v_cmp_5168_: *mut crate::leanh::LeanObject,
    mut v_inst_5169_: *mut crate::leanh::LeanObject,
    mut v_t_5170_: *mut crate::leanh::LeanObject,
    mut v_a_5171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5172_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_5168_, v_t_5170_, v_a_5171_);
    return v___x_5172_;
}
pub unsafe fn l_Std_DTreeMap_get___redArg(
    mut v_cmp_5173_: *mut crate::leanh::LeanObject,
    mut v_t_5174_: *mut crate::leanh::LeanObject,
    mut v_a_5175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5176_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_5173_, v_t_5174_, v_a_5175_);
    return v___x_5176_;
}
pub unsafe fn l_Std_DTreeMap_get(
    mut v_00_u03b1_5177_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5178_: *mut crate::leanh::LeanObject,
    mut v_cmp_5179_: *mut crate::leanh::LeanObject,
    mut v_inst_5180_: *mut crate::leanh::LeanObject,
    mut v_t_5181_: *mut crate::leanh::LeanObject,
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v_h_5183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5184_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_5179_, v_t_5181_, v_a_5182_);
    return v___x_5184_;
}
pub unsafe fn l_Std_DTreeMap_get_x21___redArg(
    mut v_cmp_5185_: *mut crate::leanh::LeanObject,
    mut v_t_5186_: *mut crate::leanh::LeanObject,
    mut v_a_5187_: *mut crate::leanh::LeanObject,
    mut v_inst_5188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5189_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(
        v_cmp_5185_,
        v_t_5186_,
        v_a_5187_,
        v_inst_5188_,
    );
    return v___x_5189_;
}
pub unsafe fn l_Std_DTreeMap_get_x21___redArg___boxed(
    mut v_cmp_5190_: *mut crate::leanh::LeanObject,
    mut v_t_5191_: *mut crate::leanh::LeanObject,
    mut v_a_5192_: *mut crate::leanh::LeanObject,
    mut v_inst_5193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5194_ = l_Std_DTreeMap_get_x21___redArg(v_cmp_5190_, v_t_5191_, v_a_5192_, v_inst_5193_);
    crate::leanh::lean_dec(v_inst_5193_);
    return v_res_5194_;
}
pub unsafe fn l_Std_DTreeMap_get_x21(
    mut v_00_u03b1_5195_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5196_: *mut crate::leanh::LeanObject,
    mut v_cmp_5197_: *mut crate::leanh::LeanObject,
    mut v_inst_5198_: *mut crate::leanh::LeanObject,
    mut v_t_5199_: *mut crate::leanh::LeanObject,
    mut v_a_5200_: *mut crate::leanh::LeanObject,
    mut v_inst_5201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5202_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(
        v_cmp_5197_,
        v_t_5199_,
        v_a_5200_,
        v_inst_5201_,
    );
    return v___x_5202_;
}
pub unsafe fn l_Std_DTreeMap_get_x21___boxed(
    mut v_00_u03b1_5203_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5204_: *mut crate::leanh::LeanObject,
    mut v_cmp_5205_: *mut crate::leanh::LeanObject,
    mut v_inst_5206_: *mut crate::leanh::LeanObject,
    mut v_t_5207_: *mut crate::leanh::LeanObject,
    mut v_a_5208_: *mut crate::leanh::LeanObject,
    mut v_inst_5209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5210_ = l_Std_DTreeMap_get_x21(
        v_00_u03b1_5203_,
        v_00_u03b2_5204_,
        v_cmp_5205_,
        v_inst_5206_,
        v_t_5207_,
        v_a_5208_,
        v_inst_5209_,
    );
    crate::leanh::lean_dec(v_inst_5209_);
    return v_res_5210_;
}
pub unsafe fn l_Std_DTreeMap_getD___redArg(
    mut v_cmp_5211_: *mut crate::leanh::LeanObject,
    mut v_t_5212_: *mut crate::leanh::LeanObject,
    mut v_a_5213_: *mut crate::leanh::LeanObject,
    mut v_fallback_5214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5215_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(
        v_cmp_5211_,
        v_t_5212_,
        v_a_5213_,
        v_fallback_5214_,
    );
    return v___x_5215_;
}
pub unsafe fn l_Std_DTreeMap_getD___redArg___boxed(
    mut v_cmp_5216_: *mut crate::leanh::LeanObject,
    mut v_t_5217_: *mut crate::leanh::LeanObject,
    mut v_a_5218_: *mut crate::leanh::LeanObject,
    mut v_fallback_5219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5220_ = l_Std_DTreeMap_getD___redArg(v_cmp_5216_, v_t_5217_, v_a_5218_, v_fallback_5219_);
    crate::leanh::lean_dec(v_fallback_5219_);
    return v_res_5220_;
}
pub unsafe fn l_Std_DTreeMap_getD(
    mut v_00_u03b1_5221_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5222_: *mut crate::leanh::LeanObject,
    mut v_cmp_5223_: *mut crate::leanh::LeanObject,
    mut v_inst_5224_: *mut crate::leanh::LeanObject,
    mut v_t_5225_: *mut crate::leanh::LeanObject,
    mut v_a_5226_: *mut crate::leanh::LeanObject,
    mut v_fallback_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5228_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(
        v_cmp_5223_,
        v_t_5225_,
        v_a_5226_,
        v_fallback_5227_,
    );
    return v___x_5228_;
}
pub unsafe fn l_Std_DTreeMap_getD___boxed(
    mut v_00_u03b1_5229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5230_: *mut crate::leanh::LeanObject,
    mut v_cmp_5231_: *mut crate::leanh::LeanObject,
    mut v_inst_5232_: *mut crate::leanh::LeanObject,
    mut v_t_5233_: *mut crate::leanh::LeanObject,
    mut v_a_5234_: *mut crate::leanh::LeanObject,
    mut v_fallback_5235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5236_ = l_Std_DTreeMap_getD(
        v_00_u03b1_5229_,
        v_00_u03b2_5230_,
        v_cmp_5231_,
        v_inst_5232_,
        v_t_5233_,
        v_a_5234_,
        v_fallback_5235_,
    );
    crate::leanh::lean_dec(v_fallback_5235_);
    return v_res_5236_;
}
pub unsafe fn l_Std_DTreeMap_getKey_x3f___redArg(
    mut v_cmp_5237_: *mut crate::leanh::LeanObject,
    mut v_t_5238_: *mut crate::leanh::LeanObject,
    mut v_a_5239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5240_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_5237_, v_t_5238_, v_a_5239_);
    return v___x_5240_;
}
pub unsafe fn l_Std_DTreeMap_getKey_x3f(
    mut v_00_u03b1_5241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5242_: *mut crate::leanh::LeanObject,
    mut v_cmp_5243_: *mut crate::leanh::LeanObject,
    mut v_t_5244_: *mut crate::leanh::LeanObject,
    mut v_a_5245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5246_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_5243_, v_t_5244_, v_a_5245_);
    return v___x_5246_;
}
pub unsafe fn l_Std_DTreeMap_getKey___redArg(
    mut v_cmp_5247_: *mut crate::leanh::LeanObject,
    mut v_t_5248_: *mut crate::leanh::LeanObject,
    mut v_a_5249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5250_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_5247_, v_t_5248_, v_a_5249_);
    return v___x_5250_;
}
pub unsafe fn l_Std_DTreeMap_getKey(
    mut v_00_u03b1_5251_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5252_: *mut crate::leanh::LeanObject,
    mut v_cmp_5253_: *mut crate::leanh::LeanObject,
    mut v_t_5254_: *mut crate::leanh::LeanObject,
    mut v_a_5255_: *mut crate::leanh::LeanObject,
    mut v_h_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_5253_, v_t_5254_, v_a_5255_);
    return v___x_5257_;
}
pub unsafe fn l_Std_DTreeMap_getKey_x21___redArg(
    mut v_cmp_5258_: *mut crate::leanh::LeanObject,
    mut v_inst_5259_: *mut crate::leanh::LeanObject,
    mut v_t_5260_: *mut crate::leanh::LeanObject,
    mut v_a_5261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5262_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_5258_,
        v_t_5260_,
        v_a_5261_,
        v_inst_5259_,
    );
    return v___x_5262_;
}
pub unsafe fn l_Std_DTreeMap_getKey_x21___redArg___boxed(
    mut v_cmp_5263_: *mut crate::leanh::LeanObject,
    mut v_inst_5264_: *mut crate::leanh::LeanObject,
    mut v_t_5265_: *mut crate::leanh::LeanObject,
    mut v_a_5266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5267_ =
        l_Std_DTreeMap_getKey_x21___redArg(v_cmp_5263_, v_inst_5264_, v_t_5265_, v_a_5266_);
    crate::leanh::lean_dec(v_inst_5264_);
    return v_res_5267_;
}
pub unsafe fn l_Std_DTreeMap_getKey_x21(
    mut v_00_u03b1_5268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5269_: *mut crate::leanh::LeanObject,
    mut v_cmp_5270_: *mut crate::leanh::LeanObject,
    mut v_inst_5271_: *mut crate::leanh::LeanObject,
    mut v_t_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5274_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_5270_,
        v_t_5272_,
        v_a_5273_,
        v_inst_5271_,
    );
    return v___x_5274_;
}
pub unsafe fn l_Std_DTreeMap_getKey_x21___boxed(
    mut v_00_u03b1_5275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5276_: *mut crate::leanh::LeanObject,
    mut v_cmp_5277_: *mut crate::leanh::LeanObject,
    mut v_inst_5278_: *mut crate::leanh::LeanObject,
    mut v_t_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5281_ = l_Std_DTreeMap_getKey_x21(
        v_00_u03b1_5275_,
        v_00_u03b2_5276_,
        v_cmp_5277_,
        v_inst_5278_,
        v_t_5279_,
        v_a_5280_,
    );
    crate::leanh::lean_dec(v_inst_5278_);
    return v_res_5281_;
}
pub unsafe fn l_Std_DTreeMap_getKeyD___redArg(
    mut v_cmp_5282_: *mut crate::leanh::LeanObject,
    mut v_t_5283_: *mut crate::leanh::LeanObject,
    mut v_a_5284_: *mut crate::leanh::LeanObject,
    mut v_fallback_5285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5286_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_5282_,
        v_t_5283_,
        v_a_5284_,
        v_fallback_5285_,
    );
    return v___x_5286_;
}
pub unsafe fn l_Std_DTreeMap_getKeyD___redArg___boxed(
    mut v_cmp_5287_: *mut crate::leanh::LeanObject,
    mut v_t_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_fallback_5290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5291_ =
        l_Std_DTreeMap_getKeyD___redArg(v_cmp_5287_, v_t_5288_, v_a_5289_, v_fallback_5290_);
    crate::leanh::lean_dec(v_fallback_5290_);
    return v_res_5291_;
}
pub unsafe fn l_Std_DTreeMap_getKeyD(
    mut v_00_u03b1_5292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5293_: *mut crate::leanh::LeanObject,
    mut v_cmp_5294_: *mut crate::leanh::LeanObject,
    mut v_t_5295_: *mut crate::leanh::LeanObject,
    mut v_a_5296_: *mut crate::leanh::LeanObject,
    mut v_fallback_5297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5298_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_5294_,
        v_t_5295_,
        v_a_5296_,
        v_fallback_5297_,
    );
    return v___x_5298_;
}
pub unsafe fn l_Std_DTreeMap_getKeyD___boxed(
    mut v_00_u03b1_5299_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5300_: *mut crate::leanh::LeanObject,
    mut v_cmp_5301_: *mut crate::leanh::LeanObject,
    mut v_t_5302_: *mut crate::leanh::LeanObject,
    mut v_a_5303_: *mut crate::leanh::LeanObject,
    mut v_fallback_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5305_ = l_Std_DTreeMap_getKeyD(
        v_00_u03b1_5299_,
        v_00_u03b2_5300_,
        v_cmp_5301_,
        v_t_5302_,
        v_a_5303_,
        v_fallback_5304_,
    );
    crate::leanh::lean_dec(v_fallback_5304_);
    return v_res_5305_;
}
pub unsafe fn l_Std_DTreeMap_getEntry_x3f___redArg(
    mut v_cmp_5306_: *mut crate::leanh::LeanObject,
    mut v_t_5307_: *mut crate::leanh::LeanObject,
    mut v_a_5308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5309_ =
        l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_5306_, v_t_5307_, v_a_5308_);
    return v___x_5309_;
}
pub unsafe fn l_Std_DTreeMap_getEntry_x3f(
    mut v_00_u03b1_5310_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5311_: *mut crate::leanh::LeanObject,
    mut v_cmp_5312_: *mut crate::leanh::LeanObject,
    mut v_t_5313_: *mut crate::leanh::LeanObject,
    mut v_a_5314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5315_ =
        l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_5312_, v_t_5313_, v_a_5314_);
    return v___x_5315_;
}
pub unsafe fn l_Std_DTreeMap_getEntry___redArg(
    mut v_cmp_5316_: *mut crate::leanh::LeanObject,
    mut v_t_5317_: *mut crate::leanh::LeanObject,
    mut v_a_5318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5319_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_5316_, v_t_5317_, v_a_5318_);
    return v___x_5319_;
}
pub unsafe fn l_Std_DTreeMap_getEntry(
    mut v_00_u03b1_5320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5321_: *mut crate::leanh::LeanObject,
    mut v_cmp_5322_: *mut crate::leanh::LeanObject,
    mut v_t_5323_: *mut crate::leanh::LeanObject,
    mut v_a_5324_: *mut crate::leanh::LeanObject,
    mut v_h_5325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5326_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_5322_, v_t_5323_, v_a_5324_);
    return v___x_5326_;
}
pub unsafe fn l_Std_DTreeMap_getEntryD___redArg(
    mut v_cmp_5327_: *mut crate::leanh::LeanObject,
    mut v_t_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_fallback_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5331_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(
        v_cmp_5327_,
        v_t_5328_,
        v_a_5329_,
        v_fallback_5330_,
    );
    return v___x_5331_;
}
pub unsafe fn l_Std_DTreeMap_getEntryD___redArg___boxed(
    mut v_cmp_5332_: *mut crate::leanh::LeanObject,
    mut v_t_5333_: *mut crate::leanh::LeanObject,
    mut v_a_5334_: *mut crate::leanh::LeanObject,
    mut v_fallback_5335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5336_ =
        l_Std_DTreeMap_getEntryD___redArg(v_cmp_5332_, v_t_5333_, v_a_5334_, v_fallback_5335_);
    crate::leanh::lean_dec_ref(v_fallback_5335_);
    return v_res_5336_;
}
pub unsafe fn l_Std_DTreeMap_getEntryD(
    mut v_00_u03b1_5337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5338_: *mut crate::leanh::LeanObject,
    mut v_cmp_5339_: *mut crate::leanh::LeanObject,
    mut v_t_5340_: *mut crate::leanh::LeanObject,
    mut v_a_5341_: *mut crate::leanh::LeanObject,
    mut v_fallback_5342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5343_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(
        v_cmp_5339_,
        v_t_5340_,
        v_a_5341_,
        v_fallback_5342_,
    );
    return v___x_5343_;
}
pub unsafe fn l_Std_DTreeMap_getEntryD___boxed(
    mut v_00_u03b1_5344_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5345_: *mut crate::leanh::LeanObject,
    mut v_cmp_5346_: *mut crate::leanh::LeanObject,
    mut v_t_5347_: *mut crate::leanh::LeanObject,
    mut v_a_5348_: *mut crate::leanh::LeanObject,
    mut v_fallback_5349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5350_ = l_Std_DTreeMap_getEntryD(
        v_00_u03b1_5344_,
        v_00_u03b2_5345_,
        v_cmp_5346_,
        v_t_5347_,
        v_a_5348_,
        v_fallback_5349_,
    );
    crate::leanh::lean_dec_ref(v_fallback_5349_);
    return v_res_5350_;
}
pub unsafe fn l_Std_DTreeMap_getEntry_x21___redArg(
    mut v_cmp_5351_: *mut crate::leanh::LeanObject,
    mut v_inst_5352_: *mut crate::leanh::LeanObject,
    mut v_t_5353_: *mut crate::leanh::LeanObject,
    mut v_a_5354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5355_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(
        v_cmp_5351_,
        v_inst_5352_,
        v_t_5353_,
        v_a_5354_,
    );
    return v___x_5355_;
}
pub unsafe fn l_Std_DTreeMap_getEntry_x21___redArg___boxed(
    mut v_cmp_5356_: *mut crate::leanh::LeanObject,
    mut v_inst_5357_: *mut crate::leanh::LeanObject,
    mut v_t_5358_: *mut crate::leanh::LeanObject,
    mut v_a_5359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5360_ =
        l_Std_DTreeMap_getEntry_x21___redArg(v_cmp_5356_, v_inst_5357_, v_t_5358_, v_a_5359_);
    crate::leanh::lean_dec_ref(v_inst_5357_);
    return v_res_5360_;
}
pub unsafe fn l_Std_DTreeMap_getEntry_x21(
    mut v_00_u03b1_5361_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5362_: *mut crate::leanh::LeanObject,
    mut v_cmp_5363_: *mut crate::leanh::LeanObject,
    mut v_inst_5364_: *mut crate::leanh::LeanObject,
    mut v_t_5365_: *mut crate::leanh::LeanObject,
    mut v_a_5366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5367_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(
        v_cmp_5363_,
        v_inst_5364_,
        v_t_5365_,
        v_a_5366_,
    );
    return v___x_5367_;
}
pub unsafe fn l_Std_DTreeMap_getEntry_x21___boxed(
    mut v_00_u03b1_5368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5369_: *mut crate::leanh::LeanObject,
    mut v_cmp_5370_: *mut crate::leanh::LeanObject,
    mut v_inst_5371_: *mut crate::leanh::LeanObject,
    mut v_t_5372_: *mut crate::leanh::LeanObject,
    mut v_a_5373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5374_ = l_Std_DTreeMap_getEntry_x21(
        v_00_u03b1_5368_,
        v_00_u03b2_5369_,
        v_cmp_5370_,
        v_inst_5371_,
        v_t_5372_,
        v_a_5373_,
    );
    crate::leanh::lean_dec_ref(v_inst_5371_);
    return v_res_5374_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x3f___redArg(
    mut v_t_5375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5376_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_5375_);
    return v___x_5376_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x3f___redArg___boxed(
    mut v_t_5377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5378_ = l_Std_DTreeMap_minEntry_x3f___redArg(v_t_5377_);
    crate::leanh::lean_dec(v_t_5377_);
    return v_res_5378_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x3f(
    mut v_00_u03b1_5379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5380_: *mut crate::leanh::LeanObject,
    mut v_cmp_5381_: *mut crate::leanh::LeanObject,
    mut v_t_5382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5383_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_5382_);
    return v___x_5383_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x3f___boxed(
    mut v_00_u03b1_5384_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5385_: *mut crate::leanh::LeanObject,
    mut v_cmp_5386_: *mut crate::leanh::LeanObject,
    mut v_t_5387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5388_ =
        l_Std_DTreeMap_minEntry_x3f(v_00_u03b1_5384_, v_00_u03b2_5385_, v_cmp_5386_, v_t_5387_);
    crate::leanh::lean_dec(v_t_5387_);
    crate::leanh::lean_dec_ref(v_cmp_5386_);
    return v_res_5388_;
}
pub unsafe fn l_Std_DTreeMap_minEntry___redArg(
    mut v_t_5389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5390_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_5389_);
    return v___x_5390_;
}
pub unsafe fn l_Std_DTreeMap_minEntry___redArg___boxed(
    mut v_t_5391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5392_ = l_Std_DTreeMap_minEntry___redArg(v_t_5391_);
    crate::leanh::lean_dec(v_t_5391_);
    return v_res_5392_;
}
pub unsafe fn l_Std_DTreeMap_minEntry(
    mut v_00_u03b1_5393_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5394_: *mut crate::leanh::LeanObject,
    mut v_cmp_5395_: *mut crate::leanh::LeanObject,
    mut v_t_5396_: *mut crate::leanh::LeanObject,
    mut v_h_5397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5398_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_t_5396_);
    return v___x_5398_;
}
pub unsafe fn l_Std_DTreeMap_minEntry___boxed(
    mut v_00_u03b1_5399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5400_: *mut crate::leanh::LeanObject,
    mut v_cmp_5401_: *mut crate::leanh::LeanObject,
    mut v_t_5402_: *mut crate::leanh::LeanObject,
    mut v_h_5403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5404_ = l_Std_DTreeMap_minEntry(
        v_00_u03b1_5399_,
        v_00_u03b2_5400_,
        v_cmp_5401_,
        v_t_5402_,
        v_h_5403_,
    );
    crate::leanh::lean_dec(v_t_5402_);
    crate::leanh::lean_dec_ref(v_cmp_5401_);
    return v_res_5404_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x21___redArg(
    mut v_inst_5405_: *mut crate::leanh::LeanObject,
    mut v_t_5406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5407_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_5405_, v_t_5406_);
    return v___x_5407_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x21___redArg___boxed(
    mut v_inst_5408_: *mut crate::leanh::LeanObject,
    mut v_t_5409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5410_ = l_Std_DTreeMap_minEntry_x21___redArg(v_inst_5408_, v_t_5409_);
    crate::leanh::lean_dec(v_t_5409_);
    crate::leanh::lean_dec_ref(v_inst_5408_);
    return v_res_5410_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x21(
    mut v_00_u03b1_5411_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5412_: *mut crate::leanh::LeanObject,
    mut v_cmp_5413_: *mut crate::leanh::LeanObject,
    mut v_inst_5414_: *mut crate::leanh::LeanObject,
    mut v_t_5415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5416_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_5414_, v_t_5415_);
    return v___x_5416_;
}
pub unsafe fn l_Std_DTreeMap_minEntry_x21___boxed(
    mut v_00_u03b1_5417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5418_: *mut crate::leanh::LeanObject,
    mut v_cmp_5419_: *mut crate::leanh::LeanObject,
    mut v_inst_5420_: *mut crate::leanh::LeanObject,
    mut v_t_5421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5422_ = l_Std_DTreeMap_minEntry_x21(
        v_00_u03b1_5417_,
        v_00_u03b2_5418_,
        v_cmp_5419_,
        v_inst_5420_,
        v_t_5421_,
    );
    crate::leanh::lean_dec(v_t_5421_);
    crate::leanh::lean_dec_ref(v_inst_5420_);
    crate::leanh::lean_dec_ref(v_cmp_5419_);
    return v_res_5422_;
}
pub unsafe fn l_Std_DTreeMap_minEntryD___redArg(
    mut v_t_5423_: *mut crate::leanh::LeanObject,
    mut v_fallback_5424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5425_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_5423_, v_fallback_5424_);
    return v___x_5425_;
}
pub unsafe fn l_Std_DTreeMap_minEntryD___redArg___boxed(
    mut v_t_5426_: *mut crate::leanh::LeanObject,
    mut v_fallback_5427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5428_ = l_Std_DTreeMap_minEntryD___redArg(v_t_5426_, v_fallback_5427_);
    crate::leanh::lean_dec_ref(v_fallback_5427_);
    crate::leanh::lean_dec(v_t_5426_);
    return v_res_5428_;
}
pub unsafe fn l_Std_DTreeMap_minEntryD(
    mut v_00_u03b1_5429_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5430_: *mut crate::leanh::LeanObject,
    mut v_cmp_5431_: *mut crate::leanh::LeanObject,
    mut v_t_5432_: *mut crate::leanh::LeanObject,
    mut v_fallback_5433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5434_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_5432_, v_fallback_5433_);
    return v___x_5434_;
}
pub unsafe fn l_Std_DTreeMap_minEntryD___boxed(
    mut v_00_u03b1_5435_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5436_: *mut crate::leanh::LeanObject,
    mut v_cmp_5437_: *mut crate::leanh::LeanObject,
    mut v_t_5438_: *mut crate::leanh::LeanObject,
    mut v_fallback_5439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5440_ = l_Std_DTreeMap_minEntryD(
        v_00_u03b1_5435_,
        v_00_u03b2_5436_,
        v_cmp_5437_,
        v_t_5438_,
        v_fallback_5439_,
    );
    crate::leanh::lean_dec_ref(v_fallback_5439_);
    crate::leanh::lean_dec(v_t_5438_);
    crate::leanh::lean_dec_ref(v_cmp_5437_);
    return v_res_5440_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x3f___redArg(
    mut v_t_5441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5442_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_5441_);
    return v___x_5442_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x3f___redArg___boxed(
    mut v_t_5443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5444_ = l_Std_DTreeMap_maxEntry_x3f___redArg(v_t_5443_);
    crate::leanh::lean_dec(v_t_5443_);
    return v_res_5444_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x3f(
    mut v_00_u03b1_5445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5446_: *mut crate::leanh::LeanObject,
    mut v_cmp_5447_: *mut crate::leanh::LeanObject,
    mut v_t_5448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5449_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_5448_);
    return v___x_5449_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x3f___boxed(
    mut v_00_u03b1_5450_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5451_: *mut crate::leanh::LeanObject,
    mut v_cmp_5452_: *mut crate::leanh::LeanObject,
    mut v_t_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5454_ =
        l_Std_DTreeMap_maxEntry_x3f(v_00_u03b1_5450_, v_00_u03b2_5451_, v_cmp_5452_, v_t_5453_);
    crate::leanh::lean_dec(v_t_5453_);
    crate::leanh::lean_dec_ref(v_cmp_5452_);
    return v_res_5454_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry___redArg(
    mut v_t_5455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5456_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_5455_);
    return v___x_5456_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry___redArg___boxed(
    mut v_t_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5458_ = l_Std_DTreeMap_maxEntry___redArg(v_t_5457_);
    crate::leanh::lean_dec(v_t_5457_);
    return v_res_5458_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry(
    mut v_00_u03b1_5459_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5460_: *mut crate::leanh::LeanObject,
    mut v_cmp_5461_: *mut crate::leanh::LeanObject,
    mut v_t_5462_: *mut crate::leanh::LeanObject,
    mut v_h_5463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5464_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_t_5462_);
    return v___x_5464_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry___boxed(
    mut v_00_u03b1_5465_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5466_: *mut crate::leanh::LeanObject,
    mut v_cmp_5467_: *mut crate::leanh::LeanObject,
    mut v_t_5468_: *mut crate::leanh::LeanObject,
    mut v_h_5469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5470_ = l_Std_DTreeMap_maxEntry(
        v_00_u03b1_5465_,
        v_00_u03b2_5466_,
        v_cmp_5467_,
        v_t_5468_,
        v_h_5469_,
    );
    crate::leanh::lean_dec(v_t_5468_);
    crate::leanh::lean_dec_ref(v_cmp_5467_);
    return v_res_5470_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x21___redArg(
    mut v_inst_5471_: *mut crate::leanh::LeanObject,
    mut v_t_5472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5473_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_5471_, v_t_5472_);
    return v___x_5473_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x21___redArg___boxed(
    mut v_inst_5474_: *mut crate::leanh::LeanObject,
    mut v_t_5475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5476_ = l_Std_DTreeMap_maxEntry_x21___redArg(v_inst_5474_, v_t_5475_);
    crate::leanh::lean_dec(v_t_5475_);
    crate::leanh::lean_dec_ref(v_inst_5474_);
    return v_res_5476_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x21(
    mut v_00_u03b1_5477_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5478_: *mut crate::leanh::LeanObject,
    mut v_cmp_5479_: *mut crate::leanh::LeanObject,
    mut v_inst_5480_: *mut crate::leanh::LeanObject,
    mut v_t_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5482_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_5480_, v_t_5481_);
    return v___x_5482_;
}
pub unsafe fn l_Std_DTreeMap_maxEntry_x21___boxed(
    mut v_00_u03b1_5483_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5484_: *mut crate::leanh::LeanObject,
    mut v_cmp_5485_: *mut crate::leanh::LeanObject,
    mut v_inst_5486_: *mut crate::leanh::LeanObject,
    mut v_t_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5488_ = l_Std_DTreeMap_maxEntry_x21(
        v_00_u03b1_5483_,
        v_00_u03b2_5484_,
        v_cmp_5485_,
        v_inst_5486_,
        v_t_5487_,
    );
    crate::leanh::lean_dec(v_t_5487_);
    crate::leanh::lean_dec_ref(v_inst_5486_);
    crate::leanh::lean_dec_ref(v_cmp_5485_);
    return v_res_5488_;
}
pub unsafe fn l_Std_DTreeMap_maxEntryD___redArg(
    mut v_t_5489_: *mut crate::leanh::LeanObject,
    mut v_fallback_5490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5491_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_5489_, v_fallback_5490_);
    return v___x_5491_;
}
pub unsafe fn l_Std_DTreeMap_maxEntryD___redArg___boxed(
    mut v_t_5492_: *mut crate::leanh::LeanObject,
    mut v_fallback_5493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5494_ = l_Std_DTreeMap_maxEntryD___redArg(v_t_5492_, v_fallback_5493_);
    crate::leanh::lean_dec_ref(v_fallback_5493_);
    crate::leanh::lean_dec(v_t_5492_);
    return v_res_5494_;
}
pub unsafe fn l_Std_DTreeMap_maxEntryD(
    mut v_00_u03b1_5495_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5496_: *mut crate::leanh::LeanObject,
    mut v_cmp_5497_: *mut crate::leanh::LeanObject,
    mut v_t_5498_: *mut crate::leanh::LeanObject,
    mut v_fallback_5499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5500_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_5498_, v_fallback_5499_);
    return v___x_5500_;
}
pub unsafe fn l_Std_DTreeMap_maxEntryD___boxed(
    mut v_00_u03b1_5501_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5502_: *mut crate::leanh::LeanObject,
    mut v_cmp_5503_: *mut crate::leanh::LeanObject,
    mut v_t_5504_: *mut crate::leanh::LeanObject,
    mut v_fallback_5505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5506_ = l_Std_DTreeMap_maxEntryD(
        v_00_u03b1_5501_,
        v_00_u03b2_5502_,
        v_cmp_5503_,
        v_t_5504_,
        v_fallback_5505_,
    );
    crate::leanh::lean_dec_ref(v_fallback_5505_);
    crate::leanh::lean_dec(v_t_5504_);
    crate::leanh::lean_dec_ref(v_cmp_5503_);
    return v_res_5506_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x3f___redArg(
    mut v_t_5507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5508_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_5507_);
    return v___x_5508_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x3f___redArg___boxed(
    mut v_t_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5510_ = l_Std_DTreeMap_minKey_x3f___redArg(v_t_5509_);
    crate::leanh::lean_dec(v_t_5509_);
    return v_res_5510_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x3f(
    mut v_00_u03b1_5511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5512_: *mut crate::leanh::LeanObject,
    mut v_cmp_5513_: *mut crate::leanh::LeanObject,
    mut v_t_5514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5515_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_5514_);
    return v___x_5515_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x3f___boxed(
    mut v_00_u03b1_5516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5517_: *mut crate::leanh::LeanObject,
    mut v_cmp_5518_: *mut crate::leanh::LeanObject,
    mut v_t_5519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5520_ =
        l_Std_DTreeMap_minKey_x3f(v_00_u03b1_5516_, v_00_u03b2_5517_, v_cmp_5518_, v_t_5519_);
    crate::leanh::lean_dec(v_t_5519_);
    crate::leanh::lean_dec_ref(v_cmp_5518_);
    return v_res_5520_;
}
pub unsafe fn l_Std_DTreeMap_minKey___redArg(
    mut v_t_5521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5522_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_5521_);
    return v___x_5522_;
}
pub unsafe fn l_Std_DTreeMap_minKey___redArg___boxed(
    mut v_t_5523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5524_ = l_Std_DTreeMap_minKey___redArg(v_t_5523_);
    crate::leanh::lean_dec(v_t_5523_);
    return v_res_5524_;
}
pub unsafe fn l_Std_DTreeMap_minKey(
    mut v_00_u03b1_5525_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5526_: *mut crate::leanh::LeanObject,
    mut v_cmp_5527_: *mut crate::leanh::LeanObject,
    mut v_t_5528_: *mut crate::leanh::LeanObject,
    mut v_h_5529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5530_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_5528_);
    return v___x_5530_;
}
pub unsafe fn l_Std_DTreeMap_minKey___boxed(
    mut v_00_u03b1_5531_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5532_: *mut crate::leanh::LeanObject,
    mut v_cmp_5533_: *mut crate::leanh::LeanObject,
    mut v_t_5534_: *mut crate::leanh::LeanObject,
    mut v_h_5535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5536_ = l_Std_DTreeMap_minKey(
        v_00_u03b1_5531_,
        v_00_u03b2_5532_,
        v_cmp_5533_,
        v_t_5534_,
        v_h_5535_,
    );
    crate::leanh::lean_dec(v_t_5534_);
    crate::leanh::lean_dec_ref(v_cmp_5533_);
    return v_res_5536_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x21___redArg(
    mut v_inst_5537_: *mut crate::leanh::LeanObject,
    mut v_t_5538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_5537_, v_t_5538_);
    return v___x_5539_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x21___redArg___boxed(
    mut v_inst_5540_: *mut crate::leanh::LeanObject,
    mut v_t_5541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5542_ = l_Std_DTreeMap_minKey_x21___redArg(v_inst_5540_, v_t_5541_);
    crate::leanh::lean_dec(v_t_5541_);
    crate::leanh::lean_dec(v_inst_5540_);
    return v_res_5542_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x21(
    mut v_00_u03b1_5543_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5544_: *mut crate::leanh::LeanObject,
    mut v_cmp_5545_: *mut crate::leanh::LeanObject,
    mut v_inst_5546_: *mut crate::leanh::LeanObject,
    mut v_t_5547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5548_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_5546_, v_t_5547_);
    return v___x_5548_;
}
pub unsafe fn l_Std_DTreeMap_minKey_x21___boxed(
    mut v_00_u03b1_5549_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5550_: *mut crate::leanh::LeanObject,
    mut v_cmp_5551_: *mut crate::leanh::LeanObject,
    mut v_inst_5552_: *mut crate::leanh::LeanObject,
    mut v_t_5553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5554_ = l_Std_DTreeMap_minKey_x21(
        v_00_u03b1_5549_,
        v_00_u03b2_5550_,
        v_cmp_5551_,
        v_inst_5552_,
        v_t_5553_,
    );
    crate::leanh::lean_dec(v_t_5553_);
    crate::leanh::lean_dec(v_inst_5552_);
    crate::leanh::lean_dec_ref(v_cmp_5551_);
    return v_res_5554_;
}
pub unsafe fn l_Std_DTreeMap_minKeyD___redArg(
    mut v_t_5555_: *mut crate::leanh::LeanObject,
    mut v_fallback_5556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5557_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_5555_, v_fallback_5556_);
    return v___x_5557_;
}
pub unsafe fn l_Std_DTreeMap_minKeyD___redArg___boxed(
    mut v_t_5558_: *mut crate::leanh::LeanObject,
    mut v_fallback_5559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5560_ = l_Std_DTreeMap_minKeyD___redArg(v_t_5558_, v_fallback_5559_);
    crate::leanh::lean_dec(v_fallback_5559_);
    crate::leanh::lean_dec(v_t_5558_);
    return v_res_5560_;
}
pub unsafe fn l_Std_DTreeMap_minKeyD(
    mut v_00_u03b1_5561_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5562_: *mut crate::leanh::LeanObject,
    mut v_cmp_5563_: *mut crate::leanh::LeanObject,
    mut v_t_5564_: *mut crate::leanh::LeanObject,
    mut v_fallback_5565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5566_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_5564_, v_fallback_5565_);
    return v___x_5566_;
}
pub unsafe fn l_Std_DTreeMap_minKeyD___boxed(
    mut v_00_u03b1_5567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5568_: *mut crate::leanh::LeanObject,
    mut v_cmp_5569_: *mut crate::leanh::LeanObject,
    mut v_t_5570_: *mut crate::leanh::LeanObject,
    mut v_fallback_5571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5572_ = l_Std_DTreeMap_minKeyD(
        v_00_u03b1_5567_,
        v_00_u03b2_5568_,
        v_cmp_5569_,
        v_t_5570_,
        v_fallback_5571_,
    );
    crate::leanh::lean_dec(v_fallback_5571_);
    crate::leanh::lean_dec(v_t_5570_);
    crate::leanh::lean_dec_ref(v_cmp_5569_);
    return v_res_5572_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x3f___redArg(
    mut v_t_5573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5574_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_5573_);
    return v___x_5574_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x3f___redArg___boxed(
    mut v_t_5575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5576_ = l_Std_DTreeMap_maxKey_x3f___redArg(v_t_5575_);
    crate::leanh::lean_dec(v_t_5575_);
    return v_res_5576_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x3f(
    mut v_00_u03b1_5577_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5578_: *mut crate::leanh::LeanObject,
    mut v_cmp_5579_: *mut crate::leanh::LeanObject,
    mut v_t_5580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5581_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_5580_);
    return v___x_5581_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x3f___boxed(
    mut v_00_u03b1_5582_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5583_: *mut crate::leanh::LeanObject,
    mut v_cmp_5584_: *mut crate::leanh::LeanObject,
    mut v_t_5585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5586_ =
        l_Std_DTreeMap_maxKey_x3f(v_00_u03b1_5582_, v_00_u03b2_5583_, v_cmp_5584_, v_t_5585_);
    crate::leanh::lean_dec(v_t_5585_);
    crate::leanh::lean_dec_ref(v_cmp_5584_);
    return v_res_5586_;
}
pub unsafe fn l_Std_DTreeMap_maxKey___redArg(
    mut v_t_5587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5588_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_5587_);
    return v___x_5588_;
}
pub unsafe fn l_Std_DTreeMap_maxKey___redArg___boxed(
    mut v_t_5589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5590_ = l_Std_DTreeMap_maxKey___redArg(v_t_5589_);
    crate::leanh::lean_dec(v_t_5589_);
    return v_res_5590_;
}
pub unsafe fn l_Std_DTreeMap_maxKey(
    mut v_00_u03b1_5591_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5592_: *mut crate::leanh::LeanObject,
    mut v_cmp_5593_: *mut crate::leanh::LeanObject,
    mut v_t_5594_: *mut crate::leanh::LeanObject,
    mut v_h_5595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5596_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_5594_);
    return v___x_5596_;
}
pub unsafe fn l_Std_DTreeMap_maxKey___boxed(
    mut v_00_u03b1_5597_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5598_: *mut crate::leanh::LeanObject,
    mut v_cmp_5599_: *mut crate::leanh::LeanObject,
    mut v_t_5600_: *mut crate::leanh::LeanObject,
    mut v_h_5601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5602_ = l_Std_DTreeMap_maxKey(
        v_00_u03b1_5597_,
        v_00_u03b2_5598_,
        v_cmp_5599_,
        v_t_5600_,
        v_h_5601_,
    );
    crate::leanh::lean_dec(v_t_5600_);
    crate::leanh::lean_dec_ref(v_cmp_5599_);
    return v_res_5602_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x21___redArg(
    mut v_inst_5603_: *mut crate::leanh::LeanObject,
    mut v_t_5604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5605_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_5603_, v_t_5604_);
    return v___x_5605_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x21___redArg___boxed(
    mut v_inst_5606_: *mut crate::leanh::LeanObject,
    mut v_t_5607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5608_ = l_Std_DTreeMap_maxKey_x21___redArg(v_inst_5606_, v_t_5607_);
    crate::leanh::lean_dec(v_t_5607_);
    crate::leanh::lean_dec(v_inst_5606_);
    return v_res_5608_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x21(
    mut v_00_u03b1_5609_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5610_: *mut crate::leanh::LeanObject,
    mut v_cmp_5611_: *mut crate::leanh::LeanObject,
    mut v_inst_5612_: *mut crate::leanh::LeanObject,
    mut v_t_5613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5614_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_5612_, v_t_5613_);
    return v___x_5614_;
}
pub unsafe fn l_Std_DTreeMap_maxKey_x21___boxed(
    mut v_00_u03b1_5615_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5616_: *mut crate::leanh::LeanObject,
    mut v_cmp_5617_: *mut crate::leanh::LeanObject,
    mut v_inst_5618_: *mut crate::leanh::LeanObject,
    mut v_t_5619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5620_ = l_Std_DTreeMap_maxKey_x21(
        v_00_u03b1_5615_,
        v_00_u03b2_5616_,
        v_cmp_5617_,
        v_inst_5618_,
        v_t_5619_,
    );
    crate::leanh::lean_dec(v_t_5619_);
    crate::leanh::lean_dec(v_inst_5618_);
    crate::leanh::lean_dec_ref(v_cmp_5617_);
    return v_res_5620_;
}
pub unsafe fn l_Std_DTreeMap_maxKeyD___redArg(
    mut v_t_5621_: *mut crate::leanh::LeanObject,
    mut v_fallback_5622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5623_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_5621_, v_fallback_5622_);
    return v___x_5623_;
}
pub unsafe fn l_Std_DTreeMap_maxKeyD___redArg___boxed(
    mut v_t_5624_: *mut crate::leanh::LeanObject,
    mut v_fallback_5625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5626_ = l_Std_DTreeMap_maxKeyD___redArg(v_t_5624_, v_fallback_5625_);
    crate::leanh::lean_dec(v_fallback_5625_);
    crate::leanh::lean_dec(v_t_5624_);
    return v_res_5626_;
}
pub unsafe fn l_Std_DTreeMap_maxKeyD(
    mut v_00_u03b1_5627_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5628_: *mut crate::leanh::LeanObject,
    mut v_cmp_5629_: *mut crate::leanh::LeanObject,
    mut v_t_5630_: *mut crate::leanh::LeanObject,
    mut v_fallback_5631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5632_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_5630_, v_fallback_5631_);
    return v___x_5632_;
}
pub unsafe fn l_Std_DTreeMap_maxKeyD___boxed(
    mut v_00_u03b1_5633_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5634_: *mut crate::leanh::LeanObject,
    mut v_cmp_5635_: *mut crate::leanh::LeanObject,
    mut v_t_5636_: *mut crate::leanh::LeanObject,
    mut v_fallback_5637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5638_ = l_Std_DTreeMap_maxKeyD(
        v_00_u03b1_5633_,
        v_00_u03b2_5634_,
        v_cmp_5635_,
        v_t_5636_,
        v_fallback_5637_,
    );
    crate::leanh::lean_dec(v_fallback_5637_);
    crate::leanh::lean_dec(v_t_5636_);
    crate::leanh::lean_dec_ref(v_cmp_5635_);
    return v_res_5638_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x3f___redArg(
    mut v_t_5639_: *mut crate::leanh::LeanObject,
    mut v_n_5640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5641_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_5639_, v_n_5640_);
    return v___x_5641_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x3f___redArg___boxed(
    mut v_t_5642_: *mut crate::leanh::LeanObject,
    mut v_n_5643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5644_ = l_Std_DTreeMap_entryAtIdx_x3f___redArg(v_t_5642_, v_n_5643_);
    crate::leanh::lean_dec(v_t_5642_);
    return v_res_5644_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x3f(
    mut v_00_u03b1_5645_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5646_: *mut crate::leanh::LeanObject,
    mut v_cmp_5647_: *mut crate::leanh::LeanObject,
    mut v_t_5648_: *mut crate::leanh::LeanObject,
    mut v_n_5649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5650_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_5648_, v_n_5649_);
    return v___x_5650_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_5651_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5652_: *mut crate::leanh::LeanObject,
    mut v_cmp_5653_: *mut crate::leanh::LeanObject,
    mut v_t_5654_: *mut crate::leanh::LeanObject,
    mut v_n_5655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5656_ = l_Std_DTreeMap_entryAtIdx_x3f(
        v_00_u03b1_5651_,
        v_00_u03b2_5652_,
        v_cmp_5653_,
        v_t_5654_,
        v_n_5655_,
    );
    crate::leanh::lean_dec(v_t_5654_);
    crate::leanh::lean_dec_ref(v_cmp_5653_);
    return v_res_5656_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx___redArg(
    mut v_t_5657_: *mut crate::leanh::LeanObject,
    mut v_n_5658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5659_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_5657_, v_n_5658_);
    return v___x_5659_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx___redArg___boxed(
    mut v_t_5660_: *mut crate::leanh::LeanObject,
    mut v_n_5661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5662_ = l_Std_DTreeMap_entryAtIdx___redArg(v_t_5660_, v_n_5661_);
    crate::leanh::lean_dec(v_t_5660_);
    return v_res_5662_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx(
    mut v_00_u03b1_5663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5664_: *mut crate::leanh::LeanObject,
    mut v_cmp_5665_: *mut crate::leanh::LeanObject,
    mut v_t_5666_: *mut crate::leanh::LeanObject,
    mut v_n_5667_: *mut crate::leanh::LeanObject,
    mut v_h_5668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5669_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_t_5666_, v_n_5667_);
    return v___x_5669_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx___boxed(
    mut v_00_u03b1_5670_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5671_: *mut crate::leanh::LeanObject,
    mut v_cmp_5672_: *mut crate::leanh::LeanObject,
    mut v_t_5673_: *mut crate::leanh::LeanObject,
    mut v_n_5674_: *mut crate::leanh::LeanObject,
    mut v_h_5675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5676_ = l_Std_DTreeMap_entryAtIdx(
        v_00_u03b1_5670_,
        v_00_u03b2_5671_,
        v_cmp_5672_,
        v_t_5673_,
        v_n_5674_,
        v_h_5675_,
    );
    crate::leanh::lean_dec(v_t_5673_);
    crate::leanh::lean_dec_ref(v_cmp_5672_);
    return v_res_5676_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x21___redArg(
    mut v_inst_5677_: *mut crate::leanh::LeanObject,
    mut v_t_5678_: *mut crate::leanh::LeanObject,
    mut v_n_5679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5680_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_5677_, v_t_5678_, v_n_5679_);
    return v___x_5680_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x21___redArg___boxed(
    mut v_inst_5681_: *mut crate::leanh::LeanObject,
    mut v_t_5682_: *mut crate::leanh::LeanObject,
    mut v_n_5683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5684_ = l_Std_DTreeMap_entryAtIdx_x21___redArg(v_inst_5681_, v_t_5682_, v_n_5683_);
    crate::leanh::lean_dec(v_t_5682_);
    crate::leanh::lean_dec_ref(v_inst_5681_);
    return v_res_5684_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x21(
    mut v_00_u03b1_5685_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5686_: *mut crate::leanh::LeanObject,
    mut v_cmp_5687_: *mut crate::leanh::LeanObject,
    mut v_inst_5688_: *mut crate::leanh::LeanObject,
    mut v_t_5689_: *mut crate::leanh::LeanObject,
    mut v_n_5690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5691_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_5688_, v_t_5689_, v_n_5690_);
    return v___x_5691_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdx_x21___boxed(
    mut v_00_u03b1_5692_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5693_: *mut crate::leanh::LeanObject,
    mut v_cmp_5694_: *mut crate::leanh::LeanObject,
    mut v_inst_5695_: *mut crate::leanh::LeanObject,
    mut v_t_5696_: *mut crate::leanh::LeanObject,
    mut v_n_5697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5698_ = l_Std_DTreeMap_entryAtIdx_x21(
        v_00_u03b1_5692_,
        v_00_u03b2_5693_,
        v_cmp_5694_,
        v_inst_5695_,
        v_t_5696_,
        v_n_5697_,
    );
    crate::leanh::lean_dec(v_t_5696_);
    crate::leanh::lean_dec_ref(v_inst_5695_);
    crate::leanh::lean_dec_ref(v_cmp_5694_);
    return v_res_5698_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdxD___redArg(
    mut v_t_5699_: *mut crate::leanh::LeanObject,
    mut v_n_5700_: *mut crate::leanh::LeanObject,
    mut v_fallback_5701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5702_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_5699_, v_n_5700_, v_fallback_5701_);
    return v___x_5702_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdxD___redArg___boxed(
    mut v_t_5703_: *mut crate::leanh::LeanObject,
    mut v_n_5704_: *mut crate::leanh::LeanObject,
    mut v_fallback_5705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5706_ = l_Std_DTreeMap_entryAtIdxD___redArg(v_t_5703_, v_n_5704_, v_fallback_5705_);
    crate::leanh::lean_dec_ref(v_fallback_5705_);
    crate::leanh::lean_dec(v_t_5703_);
    return v_res_5706_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdxD(
    mut v_00_u03b1_5707_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5708_: *mut crate::leanh::LeanObject,
    mut v_cmp_5709_: *mut crate::leanh::LeanObject,
    mut v_t_5710_: *mut crate::leanh::LeanObject,
    mut v_n_5711_: *mut crate::leanh::LeanObject,
    mut v_fallback_5712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5713_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_5710_, v_n_5711_, v_fallback_5712_);
    return v___x_5713_;
}
pub unsafe fn l_Std_DTreeMap_entryAtIdxD___boxed(
    mut v_00_u03b1_5714_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5715_: *mut crate::leanh::LeanObject,
    mut v_cmp_5716_: *mut crate::leanh::LeanObject,
    mut v_t_5717_: *mut crate::leanh::LeanObject,
    mut v_n_5718_: *mut crate::leanh::LeanObject,
    mut v_fallback_5719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5720_ = l_Std_DTreeMap_entryAtIdxD(
        v_00_u03b1_5714_,
        v_00_u03b2_5715_,
        v_cmp_5716_,
        v_t_5717_,
        v_n_5718_,
        v_fallback_5719_,
    );
    crate::leanh::lean_dec_ref(v_fallback_5719_);
    crate::leanh::lean_dec(v_t_5717_);
    crate::leanh::lean_dec_ref(v_cmp_5716_);
    return v_res_5720_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x3f___redArg(
    mut v_t_5721_: *mut crate::leanh::LeanObject,
    mut v_n_5722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5723_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_5721_, v_n_5722_);
    return v___x_5723_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x3f___redArg___boxed(
    mut v_t_5724_: *mut crate::leanh::LeanObject,
    mut v_n_5725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5726_ = l_Std_DTreeMap_keyAtIdx_x3f___redArg(v_t_5724_, v_n_5725_);
    crate::leanh::lean_dec(v_t_5724_);
    return v_res_5726_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x3f(
    mut v_00_u03b1_5727_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5728_: *mut crate::leanh::LeanObject,
    mut v_cmp_5729_: *mut crate::leanh::LeanObject,
    mut v_t_5730_: *mut crate::leanh::LeanObject,
    mut v_n_5731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5732_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_5730_, v_n_5731_);
    return v___x_5732_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x3f___boxed(
    mut v_00_u03b1_5733_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5734_: *mut crate::leanh::LeanObject,
    mut v_cmp_5735_: *mut crate::leanh::LeanObject,
    mut v_t_5736_: *mut crate::leanh::LeanObject,
    mut v_n_5737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5738_ = l_Std_DTreeMap_keyAtIdx_x3f(
        v_00_u03b1_5733_,
        v_00_u03b2_5734_,
        v_cmp_5735_,
        v_t_5736_,
        v_n_5737_,
    );
    crate::leanh::lean_dec(v_t_5736_);
    crate::leanh::lean_dec_ref(v_cmp_5735_);
    return v_res_5738_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx___redArg(
    mut v_t_5739_: *mut crate::leanh::LeanObject,
    mut v_n_5740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5741_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_5739_, v_n_5740_);
    return v___x_5741_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx___redArg___boxed(
    mut v_t_5742_: *mut crate::leanh::LeanObject,
    mut v_n_5743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5744_ = l_Std_DTreeMap_keyAtIdx___redArg(v_t_5742_, v_n_5743_);
    crate::leanh::lean_dec(v_t_5742_);
    return v_res_5744_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx(
    mut v_00_u03b1_5745_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5746_: *mut crate::leanh::LeanObject,
    mut v_cmp_5747_: *mut crate::leanh::LeanObject,
    mut v_t_5748_: *mut crate::leanh::LeanObject,
    mut v_n_5749_: *mut crate::leanh::LeanObject,
    mut v_h_5750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5751_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_5748_, v_n_5749_);
    return v___x_5751_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx___boxed(
    mut v_00_u03b1_5752_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5753_: *mut crate::leanh::LeanObject,
    mut v_cmp_5754_: *mut crate::leanh::LeanObject,
    mut v_t_5755_: *mut crate::leanh::LeanObject,
    mut v_n_5756_: *mut crate::leanh::LeanObject,
    mut v_h_5757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5758_ = l_Std_DTreeMap_keyAtIdx(
        v_00_u03b1_5752_,
        v_00_u03b2_5753_,
        v_cmp_5754_,
        v_t_5755_,
        v_n_5756_,
        v_h_5757_,
    );
    crate::leanh::lean_dec(v_t_5755_);
    crate::leanh::lean_dec_ref(v_cmp_5754_);
    return v_res_5758_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x21___redArg(
    mut v_inst_5759_: *mut crate::leanh::LeanObject,
    mut v_t_5760_: *mut crate::leanh::LeanObject,
    mut v_n_5761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5762_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_5759_, v_t_5760_, v_n_5761_);
    return v___x_5762_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x21___redArg___boxed(
    mut v_inst_5763_: *mut crate::leanh::LeanObject,
    mut v_t_5764_: *mut crate::leanh::LeanObject,
    mut v_n_5765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5766_ = l_Std_DTreeMap_keyAtIdx_x21___redArg(v_inst_5763_, v_t_5764_, v_n_5765_);
    crate::leanh::lean_dec(v_t_5764_);
    crate::leanh::lean_dec(v_inst_5763_);
    return v_res_5766_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x21(
    mut v_00_u03b1_5767_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5768_: *mut crate::leanh::LeanObject,
    mut v_cmp_5769_: *mut crate::leanh::LeanObject,
    mut v_inst_5770_: *mut crate::leanh::LeanObject,
    mut v_t_5771_: *mut crate::leanh::LeanObject,
    mut v_n_5772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5773_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_5770_, v_t_5771_, v_n_5772_);
    return v___x_5773_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdx_x21___boxed(
    mut v_00_u03b1_5774_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5775_: *mut crate::leanh::LeanObject,
    mut v_cmp_5776_: *mut crate::leanh::LeanObject,
    mut v_inst_5777_: *mut crate::leanh::LeanObject,
    mut v_t_5778_: *mut crate::leanh::LeanObject,
    mut v_n_5779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5780_ = l_Std_DTreeMap_keyAtIdx_x21(
        v_00_u03b1_5774_,
        v_00_u03b2_5775_,
        v_cmp_5776_,
        v_inst_5777_,
        v_t_5778_,
        v_n_5779_,
    );
    crate::leanh::lean_dec(v_t_5778_);
    crate::leanh::lean_dec(v_inst_5777_);
    crate::leanh::lean_dec_ref(v_cmp_5776_);
    return v_res_5780_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdxD___redArg(
    mut v_t_5781_: *mut crate::leanh::LeanObject,
    mut v_n_5782_: *mut crate::leanh::LeanObject,
    mut v_fallback_5783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5784_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_5781_, v_n_5782_, v_fallback_5783_);
    return v___x_5784_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdxD___redArg___boxed(
    mut v_t_5785_: *mut crate::leanh::LeanObject,
    mut v_n_5786_: *mut crate::leanh::LeanObject,
    mut v_fallback_5787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5788_ = l_Std_DTreeMap_keyAtIdxD___redArg(v_t_5785_, v_n_5786_, v_fallback_5787_);
    crate::leanh::lean_dec(v_fallback_5787_);
    crate::leanh::lean_dec(v_t_5785_);
    return v_res_5788_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdxD(
    mut v_00_u03b1_5789_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5790_: *mut crate::leanh::LeanObject,
    mut v_cmp_5791_: *mut crate::leanh::LeanObject,
    mut v_t_5792_: *mut crate::leanh::LeanObject,
    mut v_n_5793_: *mut crate::leanh::LeanObject,
    mut v_fallback_5794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5795_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_5792_, v_n_5793_, v_fallback_5794_);
    return v___x_5795_;
}
pub unsafe fn l_Std_DTreeMap_keyAtIdxD___boxed(
    mut v_00_u03b1_5796_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5797_: *mut crate::leanh::LeanObject,
    mut v_cmp_5798_: *mut crate::leanh::LeanObject,
    mut v_t_5799_: *mut crate::leanh::LeanObject,
    mut v_n_5800_: *mut crate::leanh::LeanObject,
    mut v_fallback_5801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5802_ = l_Std_DTreeMap_keyAtIdxD(
        v_00_u03b1_5796_,
        v_00_u03b2_5797_,
        v_cmp_5798_,
        v_t_5799_,
        v_n_5800_,
        v_fallback_5801_,
    );
    crate::leanh::lean_dec(v_fallback_5801_);
    crate::leanh::lean_dec(v_t_5799_);
    crate::leanh::lean_dec_ref(v_cmp_5798_);
    return v_res_5802_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGE_x3f___redArg(
    mut v_cmp_5803_: *mut crate::leanh::LeanObject,
    mut v_t_5804_: *mut crate::leanh::LeanObject,
    mut v_k_5805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5806_ = crate::leanh::lean_box(0);
    v___x_5807_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_5803_,
        v_k_5805_,
        v___x_5806_,
        v_t_5804_,
    );
    return v___x_5807_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGE_x3f(
    mut v_00_u03b1_5808_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5809_: *mut crate::leanh::LeanObject,
    mut v_cmp_5810_: *mut crate::leanh::LeanObject,
    mut v_t_5811_: *mut crate::leanh::LeanObject,
    mut v_k_5812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5813_ = crate::leanh::lean_box(0);
    v___x_5814_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_5810_,
        v_k_5812_,
        v___x_5813_,
        v_t_5811_,
    );
    return v___x_5814_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGT_x3f___redArg(
    mut v_cmp_5815_: *mut crate::leanh::LeanObject,
    mut v_t_5816_: *mut crate::leanh::LeanObject,
    mut v_k_5817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5818_ = crate::leanh::lean_box(0);
    v___x_5819_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5815_,
        v_k_5817_,
        v___x_5818_,
        v_t_5816_,
    );
    return v___x_5819_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGT_x3f(
    mut v_00_u03b1_5820_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5821_: *mut crate::leanh::LeanObject,
    mut v_cmp_5822_: *mut crate::leanh::LeanObject,
    mut v_t_5823_: *mut crate::leanh::LeanObject,
    mut v_k_5824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5825_ = crate::leanh::lean_box(0);
    v___x_5826_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5822_,
        v_k_5824_,
        v___x_5825_,
        v_t_5823_,
    );
    return v___x_5826_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLE_x3f___redArg(
    mut v_cmp_5827_: *mut crate::leanh::LeanObject,
    mut v_t_5828_: *mut crate::leanh::LeanObject,
    mut v_k_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = crate::leanh::lean_box(0);
    v___x_5831_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5827_,
        v_k_5829_,
        v___x_5830_,
        v_t_5828_,
    );
    return v___x_5831_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLE_x3f(
    mut v_00_u03b1_5832_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5833_: *mut crate::leanh::LeanObject,
    mut v_cmp_5834_: *mut crate::leanh::LeanObject,
    mut v_t_5835_: *mut crate::leanh::LeanObject,
    mut v_k_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5837_ = crate::leanh::lean_box(0);
    v___x_5838_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5834_,
        v_k_5836_,
        v___x_5837_,
        v_t_5835_,
    );
    return v___x_5838_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLT_x3f___redArg(
    mut v_cmp_5839_: *mut crate::leanh::LeanObject,
    mut v_t_5840_: *mut crate::leanh::LeanObject,
    mut v_k_5841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5842_ = crate::leanh::lean_box(0);
    v___x_5843_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5839_,
        v_k_5841_,
        v___x_5842_,
        v_t_5840_,
    );
    return v___x_5843_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLT_x3f(
    mut v_00_u03b1_5844_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5845_: *mut crate::leanh::LeanObject,
    mut v_cmp_5846_: *mut crate::leanh::LeanObject,
    mut v_t_5847_: *mut crate::leanh::LeanObject,
    mut v_k_5848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5849_ = crate::leanh::lean_box(0);
    v___x_5850_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5846_,
        v_k_5848_,
        v___x_5849_,
        v_t_5847_,
    );
    return v___x_5850_;
}
pub unsafe fn _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5854_ = l_Std_DTreeMap_getEntryGE_x21___redArg___closed__2;
    v___x_5855_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_5856_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_5857_ = l_Std_DTreeMap_getEntryGE_x21___redArg___closed__1;
    v___x_5858_ = l_Std_DTreeMap_getEntryGE_x21___redArg___closed__0;
    v___x_5859_ = l_mkPanicMessageWithDecl(
        v___x_5858_,
        v___x_5857_,
        v___x_5856_,
        v___x_5855_,
        v___x_5854_,
    );
    return v___x_5859_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGE_x21___redArg(
    mut v_cmp_5860_: *mut crate::leanh::LeanObject,
    mut v_inst_5861_: *mut crate::leanh::LeanObject,
    mut v_t_5862_: *mut crate::leanh::LeanObject,
    mut v_k_5863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5864_ = crate::leanh::lean_box(0);
    v___x_5865_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_5860_,
        v_k_5863_,
        v___x_5864_,
        v_t_5862_,
    );
    if crate::leanh::lean_obj_tag(v___x_5865_) == 0 {
        let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5866_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5867_ = l_panic___redArg(v_inst_5861_, v___x_5866_);
        return v___x_5867_;
    } else {
        let mut v_val_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5868_ = crate::leanh::lean_ctor_get(v___x_5865_, 0);
        crate::leanh::lean_inc(v_val_5868_);
        crate::leanh::lean_dec_ref_known(v___x_5865_, 1);
        return v_val_5868_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGE_x21___redArg___boxed(
    mut v_cmp_5869_: *mut crate::leanh::LeanObject,
    mut v_inst_5870_: *mut crate::leanh::LeanObject,
    mut v_t_5871_: *mut crate::leanh::LeanObject,
    mut v_k_5872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5873_ =
        l_Std_DTreeMap_getEntryGE_x21___redArg(v_cmp_5869_, v_inst_5870_, v_t_5871_, v_k_5872_);
    crate::leanh::lean_dec_ref(v_inst_5870_);
    return v_res_5873_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGE_x21(
    mut v_00_u03b1_5874_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5875_: *mut crate::leanh::LeanObject,
    mut v_cmp_5876_: *mut crate::leanh::LeanObject,
    mut v_inst_5877_: *mut crate::leanh::LeanObject,
    mut v_t_5878_: *mut crate::leanh::LeanObject,
    mut v_k_5879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5880_ = crate::leanh::lean_box(0);
    v___x_5881_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_5876_,
        v_k_5879_,
        v___x_5880_,
        v_t_5878_,
    );
    if crate::leanh::lean_obj_tag(v___x_5881_) == 0 {
        let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5882_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5883_ = l_panic___redArg(v_inst_5877_, v___x_5882_);
        return v___x_5883_;
    } else {
        let mut v_val_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5884_ = crate::leanh::lean_ctor_get(v___x_5881_, 0);
        crate::leanh::lean_inc(v_val_5884_);
        crate::leanh::lean_dec_ref_known(v___x_5881_, 1);
        return v_val_5884_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGE_x21___boxed(
    mut v_00_u03b1_5885_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5886_: *mut crate::leanh::LeanObject,
    mut v_cmp_5887_: *mut crate::leanh::LeanObject,
    mut v_inst_5888_: *mut crate::leanh::LeanObject,
    mut v_t_5889_: *mut crate::leanh::LeanObject,
    mut v_k_5890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5891_ = l_Std_DTreeMap_getEntryGE_x21(
        v_00_u03b1_5885_,
        v_00_u03b2_5886_,
        v_cmp_5887_,
        v_inst_5888_,
        v_t_5889_,
        v_k_5890_,
    );
    crate::leanh::lean_dec_ref(v_inst_5888_);
    return v_res_5891_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGT_x21___redArg(
    mut v_cmp_5892_: *mut crate::leanh::LeanObject,
    mut v_inst_5893_: *mut crate::leanh::LeanObject,
    mut v_t_5894_: *mut crate::leanh::LeanObject,
    mut v_k_5895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5896_ = crate::leanh::lean_box(0);
    v___x_5897_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5892_,
        v_k_5895_,
        v___x_5896_,
        v_t_5894_,
    );
    if crate::leanh::lean_obj_tag(v___x_5897_) == 0 {
        let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5898_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5899_ = l_panic___redArg(v_inst_5893_, v___x_5898_);
        return v___x_5899_;
    } else {
        let mut v_val_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5900_ = crate::leanh::lean_ctor_get(v___x_5897_, 0);
        crate::leanh::lean_inc(v_val_5900_);
        crate::leanh::lean_dec_ref_known(v___x_5897_, 1);
        return v_val_5900_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGT_x21___redArg___boxed(
    mut v_cmp_5901_: *mut crate::leanh::LeanObject,
    mut v_inst_5902_: *mut crate::leanh::LeanObject,
    mut v_t_5903_: *mut crate::leanh::LeanObject,
    mut v_k_5904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5905_ =
        l_Std_DTreeMap_getEntryGT_x21___redArg(v_cmp_5901_, v_inst_5902_, v_t_5903_, v_k_5904_);
    crate::leanh::lean_dec_ref(v_inst_5902_);
    return v_res_5905_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGT_x21(
    mut v_00_u03b1_5906_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5907_: *mut crate::leanh::LeanObject,
    mut v_cmp_5908_: *mut crate::leanh::LeanObject,
    mut v_inst_5909_: *mut crate::leanh::LeanObject,
    mut v_t_5910_: *mut crate::leanh::LeanObject,
    mut v_k_5911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5912_ = crate::leanh::lean_box(0);
    v___x_5913_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_5908_,
        v_k_5911_,
        v___x_5912_,
        v_t_5910_,
    );
    if crate::leanh::lean_obj_tag(v___x_5913_) == 0 {
        let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5914_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5915_ = l_panic___redArg(v_inst_5909_, v___x_5914_);
        return v___x_5915_;
    } else {
        let mut v_val_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5916_ = crate::leanh::lean_ctor_get(v___x_5913_, 0);
        crate::leanh::lean_inc(v_val_5916_);
        crate::leanh::lean_dec_ref_known(v___x_5913_, 1);
        return v_val_5916_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGT_x21___boxed(
    mut v_00_u03b1_5917_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5918_: *mut crate::leanh::LeanObject,
    mut v_cmp_5919_: *mut crate::leanh::LeanObject,
    mut v_inst_5920_: *mut crate::leanh::LeanObject,
    mut v_t_5921_: *mut crate::leanh::LeanObject,
    mut v_k_5922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5923_ = l_Std_DTreeMap_getEntryGT_x21(
        v_00_u03b1_5917_,
        v_00_u03b2_5918_,
        v_cmp_5919_,
        v_inst_5920_,
        v_t_5921_,
        v_k_5922_,
    );
    crate::leanh::lean_dec_ref(v_inst_5920_);
    return v_res_5923_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLE_x21___redArg(
    mut v_cmp_5924_: *mut crate::leanh::LeanObject,
    mut v_inst_5925_: *mut crate::leanh::LeanObject,
    mut v_t_5926_: *mut crate::leanh::LeanObject,
    mut v_k_5927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5928_ = crate::leanh::lean_box(0);
    v___x_5929_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5924_,
        v_k_5927_,
        v___x_5928_,
        v_t_5926_,
    );
    if crate::leanh::lean_obj_tag(v___x_5929_) == 0 {
        let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5930_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5931_ = l_panic___redArg(v_inst_5925_, v___x_5930_);
        return v___x_5931_;
    } else {
        let mut v_val_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5932_ = crate::leanh::lean_ctor_get(v___x_5929_, 0);
        crate::leanh::lean_inc(v_val_5932_);
        crate::leanh::lean_dec_ref_known(v___x_5929_, 1);
        return v_val_5932_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLE_x21___redArg___boxed(
    mut v_cmp_5933_: *mut crate::leanh::LeanObject,
    mut v_inst_5934_: *mut crate::leanh::LeanObject,
    mut v_t_5935_: *mut crate::leanh::LeanObject,
    mut v_k_5936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5937_ =
        l_Std_DTreeMap_getEntryLE_x21___redArg(v_cmp_5933_, v_inst_5934_, v_t_5935_, v_k_5936_);
    crate::leanh::lean_dec_ref(v_inst_5934_);
    return v_res_5937_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLE_x21(
    mut v_00_u03b1_5938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5939_: *mut crate::leanh::LeanObject,
    mut v_cmp_5940_: *mut crate::leanh::LeanObject,
    mut v_inst_5941_: *mut crate::leanh::LeanObject,
    mut v_t_5942_: *mut crate::leanh::LeanObject,
    mut v_k_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5944_ = crate::leanh::lean_box(0);
    v___x_5945_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_5940_,
        v_k_5943_,
        v___x_5944_,
        v_t_5942_,
    );
    if crate::leanh::lean_obj_tag(v___x_5945_) == 0 {
        let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5946_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5947_ = l_panic___redArg(v_inst_5941_, v___x_5946_);
        return v___x_5947_;
    } else {
        let mut v_val_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5948_ = crate::leanh::lean_ctor_get(v___x_5945_, 0);
        crate::leanh::lean_inc(v_val_5948_);
        crate::leanh::lean_dec_ref_known(v___x_5945_, 1);
        return v_val_5948_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLE_x21___boxed(
    mut v_00_u03b1_5949_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5950_: *mut crate::leanh::LeanObject,
    mut v_cmp_5951_: *mut crate::leanh::LeanObject,
    mut v_inst_5952_: *mut crate::leanh::LeanObject,
    mut v_t_5953_: *mut crate::leanh::LeanObject,
    mut v_k_5954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5955_ = l_Std_DTreeMap_getEntryLE_x21(
        v_00_u03b1_5949_,
        v_00_u03b2_5950_,
        v_cmp_5951_,
        v_inst_5952_,
        v_t_5953_,
        v_k_5954_,
    );
    crate::leanh::lean_dec_ref(v_inst_5952_);
    return v_res_5955_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLT_x21___redArg(
    mut v_cmp_5956_: *mut crate::leanh::LeanObject,
    mut v_inst_5957_: *mut crate::leanh::LeanObject,
    mut v_t_5958_: *mut crate::leanh::LeanObject,
    mut v_k_5959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5960_ = crate::leanh::lean_box(0);
    v___x_5961_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5956_,
        v_k_5959_,
        v___x_5960_,
        v_t_5958_,
    );
    if crate::leanh::lean_obj_tag(v___x_5961_) == 0 {
        let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5962_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5963_ = l_panic___redArg(v_inst_5957_, v___x_5962_);
        return v___x_5963_;
    } else {
        let mut v_val_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5964_ = crate::leanh::lean_ctor_get(v___x_5961_, 0);
        crate::leanh::lean_inc(v_val_5964_);
        crate::leanh::lean_dec_ref_known(v___x_5961_, 1);
        return v_val_5964_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLT_x21___redArg___boxed(
    mut v_cmp_5965_: *mut crate::leanh::LeanObject,
    mut v_inst_5966_: *mut crate::leanh::LeanObject,
    mut v_t_5967_: *mut crate::leanh::LeanObject,
    mut v_k_5968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5969_ =
        l_Std_DTreeMap_getEntryLT_x21___redArg(v_cmp_5965_, v_inst_5966_, v_t_5967_, v_k_5968_);
    crate::leanh::lean_dec_ref(v_inst_5966_);
    return v_res_5969_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLT_x21(
    mut v_00_u03b1_5970_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5971_: *mut crate::leanh::LeanObject,
    mut v_cmp_5972_: *mut crate::leanh::LeanObject,
    mut v_inst_5973_: *mut crate::leanh::LeanObject,
    mut v_t_5974_: *mut crate::leanh::LeanObject,
    mut v_k_5975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5976_ = crate::leanh::lean_box(0);
    v___x_5977_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_5972_,
        v_k_5975_,
        v___x_5976_,
        v_t_5974_,
    );
    if crate::leanh::lean_obj_tag(v___x_5977_) == 0 {
        let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5978_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_5979_ = l_panic___redArg(v_inst_5973_, v___x_5978_);
        return v___x_5979_;
    } else {
        let mut v_val_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5980_ = crate::leanh::lean_ctor_get(v___x_5977_, 0);
        crate::leanh::lean_inc(v_val_5980_);
        crate::leanh::lean_dec_ref_known(v___x_5977_, 1);
        return v_val_5980_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLT_x21___boxed(
    mut v_00_u03b1_5981_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5982_: *mut crate::leanh::LeanObject,
    mut v_cmp_5983_: *mut crate::leanh::LeanObject,
    mut v_inst_5984_: *mut crate::leanh::LeanObject,
    mut v_t_5985_: *mut crate::leanh::LeanObject,
    mut v_k_5986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5987_ = l_Std_DTreeMap_getEntryLT_x21(
        v_00_u03b1_5981_,
        v_00_u03b2_5982_,
        v_cmp_5983_,
        v_inst_5984_,
        v_t_5985_,
        v_k_5986_,
    );
    crate::leanh::lean_dec_ref(v_inst_5984_);
    return v_res_5987_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGED___redArg(
    mut v_cmp_5988_: *mut crate::leanh::LeanObject,
    mut v_t_5989_: *mut crate::leanh::LeanObject,
    mut v_k_5990_: *mut crate::leanh::LeanObject,
    mut v_fallback_5991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5992_ = crate::leanh::lean_box(0);
    v___x_5993_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_5988_,
        v_k_5990_,
        v___x_5992_,
        v_t_5989_,
    );
    if crate::leanh::lean_obj_tag(v___x_5993_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_5991_);
        return v_fallback_5991_;
    } else {
        let mut v_val_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5994_ = crate::leanh::lean_ctor_get(v___x_5993_, 0);
        crate::leanh::lean_inc(v_val_5994_);
        crate::leanh::lean_dec_ref_known(v___x_5993_, 1);
        return v_val_5994_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGED___redArg___boxed(
    mut v_cmp_5995_: *mut crate::leanh::LeanObject,
    mut v_t_5996_: *mut crate::leanh::LeanObject,
    mut v_k_5997_: *mut crate::leanh::LeanObject,
    mut v_fallback_5998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5999_ =
        l_Std_DTreeMap_getEntryGED___redArg(v_cmp_5995_, v_t_5996_, v_k_5997_, v_fallback_5998_);
    crate::leanh::lean_dec_ref(v_fallback_5998_);
    return v_res_5999_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGED(
    mut v_00_u03b1_6000_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6001_: *mut crate::leanh::LeanObject,
    mut v_cmp_6002_: *mut crate::leanh::LeanObject,
    mut v_t_6003_: *mut crate::leanh::LeanObject,
    mut v_k_6004_: *mut crate::leanh::LeanObject,
    mut v_fallback_6005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6006_ = crate::leanh::lean_box(0);
    v___x_6007_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_cmp_6002_,
        v_k_6004_,
        v___x_6006_,
        v_t_6003_,
    );
    if crate::leanh::lean_obj_tag(v___x_6007_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6005_);
        return v_fallback_6005_;
    } else {
        let mut v_val_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6008_ = crate::leanh::lean_ctor_get(v___x_6007_, 0);
        crate::leanh::lean_inc(v_val_6008_);
        crate::leanh::lean_dec_ref_known(v___x_6007_, 1);
        return v_val_6008_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGED___boxed(
    mut v_00_u03b1_6009_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6010_: *mut crate::leanh::LeanObject,
    mut v_cmp_6011_: *mut crate::leanh::LeanObject,
    mut v_t_6012_: *mut crate::leanh::LeanObject,
    mut v_k_6013_: *mut crate::leanh::LeanObject,
    mut v_fallback_6014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6015_ = l_Std_DTreeMap_getEntryGED(
        v_00_u03b1_6009_,
        v_00_u03b2_6010_,
        v_cmp_6011_,
        v_t_6012_,
        v_k_6013_,
        v_fallback_6014_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6014_);
    return v_res_6015_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGTD___redArg(
    mut v_cmp_6016_: *mut crate::leanh::LeanObject,
    mut v_t_6017_: *mut crate::leanh::LeanObject,
    mut v_k_6018_: *mut crate::leanh::LeanObject,
    mut v_fallback_6019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6020_ = crate::leanh::lean_box(0);
    v___x_6021_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_6016_,
        v_k_6018_,
        v___x_6020_,
        v_t_6017_,
    );
    if crate::leanh::lean_obj_tag(v___x_6021_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6019_);
        return v_fallback_6019_;
    } else {
        let mut v_val_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6022_ = crate::leanh::lean_ctor_get(v___x_6021_, 0);
        crate::leanh::lean_inc(v_val_6022_);
        crate::leanh::lean_dec_ref_known(v___x_6021_, 1);
        return v_val_6022_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGTD___redArg___boxed(
    mut v_cmp_6023_: *mut crate::leanh::LeanObject,
    mut v_t_6024_: *mut crate::leanh::LeanObject,
    mut v_k_6025_: *mut crate::leanh::LeanObject,
    mut v_fallback_6026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6027_ =
        l_Std_DTreeMap_getEntryGTD___redArg(v_cmp_6023_, v_t_6024_, v_k_6025_, v_fallback_6026_);
    crate::leanh::lean_dec_ref(v_fallback_6026_);
    return v_res_6027_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGTD(
    mut v_00_u03b1_6028_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6029_: *mut crate::leanh::LeanObject,
    mut v_cmp_6030_: *mut crate::leanh::LeanObject,
    mut v_t_6031_: *mut crate::leanh::LeanObject,
    mut v_k_6032_: *mut crate::leanh::LeanObject,
    mut v_fallback_6033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6034_ = crate::leanh::lean_box(0);
    v___x_6035_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_cmp_6030_,
        v_k_6032_,
        v___x_6034_,
        v_t_6031_,
    );
    if crate::leanh::lean_obj_tag(v___x_6035_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6033_);
        return v_fallback_6033_;
    } else {
        let mut v_val_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6036_ = crate::leanh::lean_ctor_get(v___x_6035_, 0);
        crate::leanh::lean_inc(v_val_6036_);
        crate::leanh::lean_dec_ref_known(v___x_6035_, 1);
        return v_val_6036_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryGTD___boxed(
    mut v_00_u03b1_6037_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6038_: *mut crate::leanh::LeanObject,
    mut v_cmp_6039_: *mut crate::leanh::LeanObject,
    mut v_t_6040_: *mut crate::leanh::LeanObject,
    mut v_k_6041_: *mut crate::leanh::LeanObject,
    mut v_fallback_6042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6043_ = l_Std_DTreeMap_getEntryGTD(
        v_00_u03b1_6037_,
        v_00_u03b2_6038_,
        v_cmp_6039_,
        v_t_6040_,
        v_k_6041_,
        v_fallback_6042_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6042_);
    return v_res_6043_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLED___redArg(
    mut v_cmp_6044_: *mut crate::leanh::LeanObject,
    mut v_t_6045_: *mut crate::leanh::LeanObject,
    mut v_k_6046_: *mut crate::leanh::LeanObject,
    mut v_fallback_6047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6048_ = crate::leanh::lean_box(0);
    v___x_6049_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_6044_,
        v_k_6046_,
        v___x_6048_,
        v_t_6045_,
    );
    if crate::leanh::lean_obj_tag(v___x_6049_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6047_);
        return v_fallback_6047_;
    } else {
        let mut v_val_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6050_ = crate::leanh::lean_ctor_get(v___x_6049_, 0);
        crate::leanh::lean_inc(v_val_6050_);
        crate::leanh::lean_dec_ref_known(v___x_6049_, 1);
        return v_val_6050_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLED___redArg___boxed(
    mut v_cmp_6051_: *mut crate::leanh::LeanObject,
    mut v_t_6052_: *mut crate::leanh::LeanObject,
    mut v_k_6053_: *mut crate::leanh::LeanObject,
    mut v_fallback_6054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6055_ =
        l_Std_DTreeMap_getEntryLED___redArg(v_cmp_6051_, v_t_6052_, v_k_6053_, v_fallback_6054_);
    crate::leanh::lean_dec_ref(v_fallback_6054_);
    return v_res_6055_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLED(
    mut v_00_u03b1_6056_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6057_: *mut crate::leanh::LeanObject,
    mut v_cmp_6058_: *mut crate::leanh::LeanObject,
    mut v_t_6059_: *mut crate::leanh::LeanObject,
    mut v_k_6060_: *mut crate::leanh::LeanObject,
    mut v_fallback_6061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6062_ = crate::leanh::lean_box(0);
    v___x_6063_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_cmp_6058_,
        v_k_6060_,
        v___x_6062_,
        v_t_6059_,
    );
    if crate::leanh::lean_obj_tag(v___x_6063_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6061_);
        return v_fallback_6061_;
    } else {
        let mut v_val_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6064_ = crate::leanh::lean_ctor_get(v___x_6063_, 0);
        crate::leanh::lean_inc(v_val_6064_);
        crate::leanh::lean_dec_ref_known(v___x_6063_, 1);
        return v_val_6064_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLED___boxed(
    mut v_00_u03b1_6065_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6066_: *mut crate::leanh::LeanObject,
    mut v_cmp_6067_: *mut crate::leanh::LeanObject,
    mut v_t_6068_: *mut crate::leanh::LeanObject,
    mut v_k_6069_: *mut crate::leanh::LeanObject,
    mut v_fallback_6070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6071_ = l_Std_DTreeMap_getEntryLED(
        v_00_u03b1_6065_,
        v_00_u03b2_6066_,
        v_cmp_6067_,
        v_t_6068_,
        v_k_6069_,
        v_fallback_6070_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6070_);
    return v_res_6071_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLTD___redArg(
    mut v_cmp_6072_: *mut crate::leanh::LeanObject,
    mut v_t_6073_: *mut crate::leanh::LeanObject,
    mut v_k_6074_: *mut crate::leanh::LeanObject,
    mut v_fallback_6075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6076_ = crate::leanh::lean_box(0);
    v___x_6077_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_6072_,
        v_k_6074_,
        v___x_6076_,
        v_t_6073_,
    );
    if crate::leanh::lean_obj_tag(v___x_6077_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6075_);
        return v_fallback_6075_;
    } else {
        let mut v_val_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6078_ = crate::leanh::lean_ctor_get(v___x_6077_, 0);
        crate::leanh::lean_inc(v_val_6078_);
        crate::leanh::lean_dec_ref_known(v___x_6077_, 1);
        return v_val_6078_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLTD___redArg___boxed(
    mut v_cmp_6079_: *mut crate::leanh::LeanObject,
    mut v_t_6080_: *mut crate::leanh::LeanObject,
    mut v_k_6081_: *mut crate::leanh::LeanObject,
    mut v_fallback_6082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6083_ =
        l_Std_DTreeMap_getEntryLTD___redArg(v_cmp_6079_, v_t_6080_, v_k_6081_, v_fallback_6082_);
    crate::leanh::lean_dec_ref(v_fallback_6082_);
    return v_res_6083_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLTD(
    mut v_00_u03b1_6084_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6085_: *mut crate::leanh::LeanObject,
    mut v_cmp_6086_: *mut crate::leanh::LeanObject,
    mut v_t_6087_: *mut crate::leanh::LeanObject,
    mut v_k_6088_: *mut crate::leanh::LeanObject,
    mut v_fallback_6089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6090_ = crate::leanh::lean_box(0);
    v___x_6091_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_cmp_6086_,
        v_k_6088_,
        v___x_6090_,
        v_t_6087_,
    );
    if crate::leanh::lean_obj_tag(v___x_6091_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6089_);
        return v_fallback_6089_;
    } else {
        let mut v_val_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6092_ = crate::leanh::lean_ctor_get(v___x_6091_, 0);
        crate::leanh::lean_inc(v_val_6092_);
        crate::leanh::lean_dec_ref_known(v___x_6091_, 1);
        return v_val_6092_;
    }
}
pub unsafe fn l_Std_DTreeMap_getEntryLTD___boxed(
    mut v_00_u03b1_6093_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6094_: *mut crate::leanh::LeanObject,
    mut v_cmp_6095_: *mut crate::leanh::LeanObject,
    mut v_t_6096_: *mut crate::leanh::LeanObject,
    mut v_k_6097_: *mut crate::leanh::LeanObject,
    mut v_fallback_6098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6099_ = l_Std_DTreeMap_getEntryLTD(
        v_00_u03b1_6093_,
        v_00_u03b2_6094_,
        v_cmp_6095_,
        v_t_6096_,
        v_k_6097_,
        v_fallback_6098_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6098_);
    return v_res_6099_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGE_x3f___redArg(
    mut v_cmp_6100_: *mut crate::leanh::LeanObject,
    mut v_t_6101_: *mut crate::leanh::LeanObject,
    mut v_k_6102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6103_ = crate::leanh::lean_box(0);
    v___x_6104_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_6100_,
        v_k_6102_,
        v___x_6103_,
        v_t_6101_,
    );
    return v___x_6104_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGE_x3f(
    mut v_00_u03b1_6105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6106_: *mut crate::leanh::LeanObject,
    mut v_cmp_6107_: *mut crate::leanh::LeanObject,
    mut v_t_6108_: *mut crate::leanh::LeanObject,
    mut v_k_6109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6110_ = crate::leanh::lean_box(0);
    v___x_6111_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_6107_,
        v_k_6109_,
        v___x_6110_,
        v_t_6108_,
    );
    return v___x_6111_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGT_x3f___redArg(
    mut v_cmp_6112_: *mut crate::leanh::LeanObject,
    mut v_t_6113_: *mut crate::leanh::LeanObject,
    mut v_k_6114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6115_ = crate::leanh::lean_box(0);
    v___x_6116_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_6112_,
        v_k_6114_,
        v___x_6115_,
        v_t_6113_,
    );
    return v___x_6116_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGT_x3f(
    mut v_00_u03b1_6117_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6118_: *mut crate::leanh::LeanObject,
    mut v_cmp_6119_: *mut crate::leanh::LeanObject,
    mut v_t_6120_: *mut crate::leanh::LeanObject,
    mut v_k_6121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6122_ = crate::leanh::lean_box(0);
    v___x_6123_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_6119_,
        v_k_6121_,
        v___x_6122_,
        v_t_6120_,
    );
    return v___x_6123_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLE_x3f___redArg(
    mut v_cmp_6124_: *mut crate::leanh::LeanObject,
    mut v_t_6125_: *mut crate::leanh::LeanObject,
    mut v_k_6126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6127_ = crate::leanh::lean_box(0);
    v___x_6128_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_6124_,
        v_k_6126_,
        v___x_6127_,
        v_t_6125_,
    );
    return v___x_6128_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLE_x3f(
    mut v_00_u03b1_6129_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6130_: *mut crate::leanh::LeanObject,
    mut v_cmp_6131_: *mut crate::leanh::LeanObject,
    mut v_t_6132_: *mut crate::leanh::LeanObject,
    mut v_k_6133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6134_ = crate::leanh::lean_box(0);
    v___x_6135_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_6131_,
        v_k_6133_,
        v___x_6134_,
        v_t_6132_,
    );
    return v___x_6135_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLT_x3f___redArg(
    mut v_cmp_6136_: *mut crate::leanh::LeanObject,
    mut v_t_6137_: *mut crate::leanh::LeanObject,
    mut v_k_6138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6139_ = crate::leanh::lean_box(0);
    v___x_6140_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_6136_,
        v_k_6138_,
        v___x_6139_,
        v_t_6137_,
    );
    return v___x_6140_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLT_x3f(
    mut v_00_u03b1_6141_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6142_: *mut crate::leanh::LeanObject,
    mut v_cmp_6143_: *mut crate::leanh::LeanObject,
    mut v_t_6144_: *mut crate::leanh::LeanObject,
    mut v_k_6145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6146_ = crate::leanh::lean_box(0);
    v___x_6147_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_6143_,
        v_k_6145_,
        v___x_6146_,
        v_t_6144_,
    );
    return v___x_6147_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGE_x21___redArg(
    mut v_cmp_6148_: *mut crate::leanh::LeanObject,
    mut v_inst_6149_: *mut crate::leanh::LeanObject,
    mut v_t_6150_: *mut crate::leanh::LeanObject,
    mut v_k_6151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6152_ = crate::leanh::lean_box(0);
    v___x_6153_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_6148_,
        v_k_6151_,
        v___x_6152_,
        v_t_6150_,
    );
    if crate::leanh::lean_obj_tag(v___x_6153_) == 0 {
        let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6154_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6155_ = l_panic___redArg(v_inst_6149_, v___x_6154_);
        return v___x_6155_;
    } else {
        let mut v_val_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6156_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
        crate::leanh::lean_inc(v_val_6156_);
        crate::leanh::lean_dec_ref_known(v___x_6153_, 1);
        return v_val_6156_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGE_x21___redArg___boxed(
    mut v_cmp_6157_: *mut crate::leanh::LeanObject,
    mut v_inst_6158_: *mut crate::leanh::LeanObject,
    mut v_t_6159_: *mut crate::leanh::LeanObject,
    mut v_k_6160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6161_ =
        l_Std_DTreeMap_getKeyGE_x21___redArg(v_cmp_6157_, v_inst_6158_, v_t_6159_, v_k_6160_);
    crate::leanh::lean_dec(v_inst_6158_);
    return v_res_6161_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGE_x21(
    mut v_00_u03b1_6162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6163_: *mut crate::leanh::LeanObject,
    mut v_cmp_6164_: *mut crate::leanh::LeanObject,
    mut v_inst_6165_: *mut crate::leanh::LeanObject,
    mut v_t_6166_: *mut crate::leanh::LeanObject,
    mut v_k_6167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6168_ = crate::leanh::lean_box(0);
    v___x_6169_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_6164_,
        v_k_6167_,
        v___x_6168_,
        v_t_6166_,
    );
    if crate::leanh::lean_obj_tag(v___x_6169_) == 0 {
        let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6170_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6171_ = l_panic___redArg(v_inst_6165_, v___x_6170_);
        return v___x_6171_;
    } else {
        let mut v_val_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6172_ = crate::leanh::lean_ctor_get(v___x_6169_, 0);
        crate::leanh::lean_inc(v_val_6172_);
        crate::leanh::lean_dec_ref_known(v___x_6169_, 1);
        return v_val_6172_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGE_x21___boxed(
    mut v_00_u03b1_6173_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6174_: *mut crate::leanh::LeanObject,
    mut v_cmp_6175_: *mut crate::leanh::LeanObject,
    mut v_inst_6176_: *mut crate::leanh::LeanObject,
    mut v_t_6177_: *mut crate::leanh::LeanObject,
    mut v_k_6178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6179_ = l_Std_DTreeMap_getKeyGE_x21(
        v_00_u03b1_6173_,
        v_00_u03b2_6174_,
        v_cmp_6175_,
        v_inst_6176_,
        v_t_6177_,
        v_k_6178_,
    );
    crate::leanh::lean_dec(v_inst_6176_);
    return v_res_6179_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGT_x21___redArg(
    mut v_cmp_6180_: *mut crate::leanh::LeanObject,
    mut v_inst_6181_: *mut crate::leanh::LeanObject,
    mut v_t_6182_: *mut crate::leanh::LeanObject,
    mut v_k_6183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6184_ = crate::leanh::lean_box(0);
    v___x_6185_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_6180_,
        v_k_6183_,
        v___x_6184_,
        v_t_6182_,
    );
    if crate::leanh::lean_obj_tag(v___x_6185_) == 0 {
        let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6186_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6187_ = l_panic___redArg(v_inst_6181_, v___x_6186_);
        return v___x_6187_;
    } else {
        let mut v_val_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6188_ = crate::leanh::lean_ctor_get(v___x_6185_, 0);
        crate::leanh::lean_inc(v_val_6188_);
        crate::leanh::lean_dec_ref_known(v___x_6185_, 1);
        return v_val_6188_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGT_x21___redArg___boxed(
    mut v_cmp_6189_: *mut crate::leanh::LeanObject,
    mut v_inst_6190_: *mut crate::leanh::LeanObject,
    mut v_t_6191_: *mut crate::leanh::LeanObject,
    mut v_k_6192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6193_ =
        l_Std_DTreeMap_getKeyGT_x21___redArg(v_cmp_6189_, v_inst_6190_, v_t_6191_, v_k_6192_);
    crate::leanh::lean_dec(v_inst_6190_);
    return v_res_6193_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGT_x21(
    mut v_00_u03b1_6194_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6195_: *mut crate::leanh::LeanObject,
    mut v_cmp_6196_: *mut crate::leanh::LeanObject,
    mut v_inst_6197_: *mut crate::leanh::LeanObject,
    mut v_t_6198_: *mut crate::leanh::LeanObject,
    mut v_k_6199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6200_ = crate::leanh::lean_box(0);
    v___x_6201_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_6196_,
        v_k_6199_,
        v___x_6200_,
        v_t_6198_,
    );
    if crate::leanh::lean_obj_tag(v___x_6201_) == 0 {
        let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6202_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6203_ = l_panic___redArg(v_inst_6197_, v___x_6202_);
        return v___x_6203_;
    } else {
        let mut v_val_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6204_ = crate::leanh::lean_ctor_get(v___x_6201_, 0);
        crate::leanh::lean_inc(v_val_6204_);
        crate::leanh::lean_dec_ref_known(v___x_6201_, 1);
        return v_val_6204_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGT_x21___boxed(
    mut v_00_u03b1_6205_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6206_: *mut crate::leanh::LeanObject,
    mut v_cmp_6207_: *mut crate::leanh::LeanObject,
    mut v_inst_6208_: *mut crate::leanh::LeanObject,
    mut v_t_6209_: *mut crate::leanh::LeanObject,
    mut v_k_6210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6211_ = l_Std_DTreeMap_getKeyGT_x21(
        v_00_u03b1_6205_,
        v_00_u03b2_6206_,
        v_cmp_6207_,
        v_inst_6208_,
        v_t_6209_,
        v_k_6210_,
    );
    crate::leanh::lean_dec(v_inst_6208_);
    return v_res_6211_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLE_x21___redArg(
    mut v_cmp_6212_: *mut crate::leanh::LeanObject,
    mut v_inst_6213_: *mut crate::leanh::LeanObject,
    mut v_t_6214_: *mut crate::leanh::LeanObject,
    mut v_k_6215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6216_ = crate::leanh::lean_box(0);
    v___x_6217_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_6212_,
        v_k_6215_,
        v___x_6216_,
        v_t_6214_,
    );
    if crate::leanh::lean_obj_tag(v___x_6217_) == 0 {
        let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6218_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6219_ = l_panic___redArg(v_inst_6213_, v___x_6218_);
        return v___x_6219_;
    } else {
        let mut v_val_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6220_ = crate::leanh::lean_ctor_get(v___x_6217_, 0);
        crate::leanh::lean_inc(v_val_6220_);
        crate::leanh::lean_dec_ref_known(v___x_6217_, 1);
        return v_val_6220_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLE_x21___redArg___boxed(
    mut v_cmp_6221_: *mut crate::leanh::LeanObject,
    mut v_inst_6222_: *mut crate::leanh::LeanObject,
    mut v_t_6223_: *mut crate::leanh::LeanObject,
    mut v_k_6224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6225_ =
        l_Std_DTreeMap_getKeyLE_x21___redArg(v_cmp_6221_, v_inst_6222_, v_t_6223_, v_k_6224_);
    crate::leanh::lean_dec(v_inst_6222_);
    return v_res_6225_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLE_x21(
    mut v_00_u03b1_6226_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6227_: *mut crate::leanh::LeanObject,
    mut v_cmp_6228_: *mut crate::leanh::LeanObject,
    mut v_inst_6229_: *mut crate::leanh::LeanObject,
    mut v_t_6230_: *mut crate::leanh::LeanObject,
    mut v_k_6231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6232_ = crate::leanh::lean_box(0);
    v___x_6233_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_6228_,
        v_k_6231_,
        v___x_6232_,
        v_t_6230_,
    );
    if crate::leanh::lean_obj_tag(v___x_6233_) == 0 {
        let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6234_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6235_ = l_panic___redArg(v_inst_6229_, v___x_6234_);
        return v___x_6235_;
    } else {
        let mut v_val_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6236_ = crate::leanh::lean_ctor_get(v___x_6233_, 0);
        crate::leanh::lean_inc(v_val_6236_);
        crate::leanh::lean_dec_ref_known(v___x_6233_, 1);
        return v_val_6236_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLE_x21___boxed(
    mut v_00_u03b1_6237_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6238_: *mut crate::leanh::LeanObject,
    mut v_cmp_6239_: *mut crate::leanh::LeanObject,
    mut v_inst_6240_: *mut crate::leanh::LeanObject,
    mut v_t_6241_: *mut crate::leanh::LeanObject,
    mut v_k_6242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6243_ = l_Std_DTreeMap_getKeyLE_x21(
        v_00_u03b1_6237_,
        v_00_u03b2_6238_,
        v_cmp_6239_,
        v_inst_6240_,
        v_t_6241_,
        v_k_6242_,
    );
    crate::leanh::lean_dec(v_inst_6240_);
    return v_res_6243_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLT_x21___redArg(
    mut v_cmp_6244_: *mut crate::leanh::LeanObject,
    mut v_inst_6245_: *mut crate::leanh::LeanObject,
    mut v_t_6246_: *mut crate::leanh::LeanObject,
    mut v_k_6247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6248_ = crate::leanh::lean_box(0);
    v___x_6249_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_6244_,
        v_k_6247_,
        v___x_6248_,
        v_t_6246_,
    );
    if crate::leanh::lean_obj_tag(v___x_6249_) == 0 {
        let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6250_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6251_ = l_panic___redArg(v_inst_6245_, v___x_6250_);
        return v___x_6251_;
    } else {
        let mut v_val_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6252_ = crate::leanh::lean_ctor_get(v___x_6249_, 0);
        crate::leanh::lean_inc(v_val_6252_);
        crate::leanh::lean_dec_ref_known(v___x_6249_, 1);
        return v_val_6252_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLT_x21___redArg___boxed(
    mut v_cmp_6253_: *mut crate::leanh::LeanObject,
    mut v_inst_6254_: *mut crate::leanh::LeanObject,
    mut v_t_6255_: *mut crate::leanh::LeanObject,
    mut v_k_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6257_ =
        l_Std_DTreeMap_getKeyLT_x21___redArg(v_cmp_6253_, v_inst_6254_, v_t_6255_, v_k_6256_);
    crate::leanh::lean_dec(v_inst_6254_);
    return v_res_6257_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLT_x21(
    mut v_00_u03b1_6258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6259_: *mut crate::leanh::LeanObject,
    mut v_cmp_6260_: *mut crate::leanh::LeanObject,
    mut v_inst_6261_: *mut crate::leanh::LeanObject,
    mut v_t_6262_: *mut crate::leanh::LeanObject,
    mut v_k_6263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6264_ = crate::leanh::lean_box(0);
    v___x_6265_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_6260_,
        v_k_6263_,
        v___x_6264_,
        v_t_6262_,
    );
    if crate::leanh::lean_obj_tag(v___x_6265_) == 0 {
        let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6266_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6267_ = l_panic___redArg(v_inst_6261_, v___x_6266_);
        return v___x_6267_;
    } else {
        let mut v_val_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6268_ = crate::leanh::lean_ctor_get(v___x_6265_, 0);
        crate::leanh::lean_inc(v_val_6268_);
        crate::leanh::lean_dec_ref_known(v___x_6265_, 1);
        return v_val_6268_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLT_x21___boxed(
    mut v_00_u03b1_6269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6270_: *mut crate::leanh::LeanObject,
    mut v_cmp_6271_: *mut crate::leanh::LeanObject,
    mut v_inst_6272_: *mut crate::leanh::LeanObject,
    mut v_t_6273_: *mut crate::leanh::LeanObject,
    mut v_k_6274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6275_ = l_Std_DTreeMap_getKeyLT_x21(
        v_00_u03b1_6269_,
        v_00_u03b2_6270_,
        v_cmp_6271_,
        v_inst_6272_,
        v_t_6273_,
        v_k_6274_,
    );
    crate::leanh::lean_dec(v_inst_6272_);
    return v_res_6275_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGED___redArg(
    mut v_cmp_6276_: *mut crate::leanh::LeanObject,
    mut v_t_6277_: *mut crate::leanh::LeanObject,
    mut v_k_6278_: *mut crate::leanh::LeanObject,
    mut v_fallback_6279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6280_ = crate::leanh::lean_box(0);
    v___x_6281_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_6276_,
        v_k_6278_,
        v___x_6280_,
        v_t_6277_,
    );
    if crate::leanh::lean_obj_tag(v___x_6281_) == 0 {
        crate::leanh::lean_inc(v_fallback_6279_);
        return v_fallback_6279_;
    } else {
        let mut v_val_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6282_ = crate::leanh::lean_ctor_get(v___x_6281_, 0);
        crate::leanh::lean_inc(v_val_6282_);
        crate::leanh::lean_dec_ref_known(v___x_6281_, 1);
        return v_val_6282_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGED___redArg___boxed(
    mut v_cmp_6283_: *mut crate::leanh::LeanObject,
    mut v_t_6284_: *mut crate::leanh::LeanObject,
    mut v_k_6285_: *mut crate::leanh::LeanObject,
    mut v_fallback_6286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6287_ =
        l_Std_DTreeMap_getKeyGED___redArg(v_cmp_6283_, v_t_6284_, v_k_6285_, v_fallback_6286_);
    crate::leanh::lean_dec(v_fallback_6286_);
    return v_res_6287_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGED(
    mut v_00_u03b1_6288_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6289_: *mut crate::leanh::LeanObject,
    mut v_cmp_6290_: *mut crate::leanh::LeanObject,
    mut v_t_6291_: *mut crate::leanh::LeanObject,
    mut v_k_6292_: *mut crate::leanh::LeanObject,
    mut v_fallback_6293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6294_ = crate::leanh::lean_box(0);
    v___x_6295_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_6290_,
        v_k_6292_,
        v___x_6294_,
        v_t_6291_,
    );
    if crate::leanh::lean_obj_tag(v___x_6295_) == 0 {
        crate::leanh::lean_inc(v_fallback_6293_);
        return v_fallback_6293_;
    } else {
        let mut v_val_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6296_ = crate::leanh::lean_ctor_get(v___x_6295_, 0);
        crate::leanh::lean_inc(v_val_6296_);
        crate::leanh::lean_dec_ref_known(v___x_6295_, 1);
        return v_val_6296_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGED___boxed(
    mut v_00_u03b1_6297_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6298_: *mut crate::leanh::LeanObject,
    mut v_cmp_6299_: *mut crate::leanh::LeanObject,
    mut v_t_6300_: *mut crate::leanh::LeanObject,
    mut v_k_6301_: *mut crate::leanh::LeanObject,
    mut v_fallback_6302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6303_ = l_Std_DTreeMap_getKeyGED(
        v_00_u03b1_6297_,
        v_00_u03b2_6298_,
        v_cmp_6299_,
        v_t_6300_,
        v_k_6301_,
        v_fallback_6302_,
    );
    crate::leanh::lean_dec(v_fallback_6302_);
    return v_res_6303_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGTD___redArg(
    mut v_cmp_6304_: *mut crate::leanh::LeanObject,
    mut v_t_6305_: *mut crate::leanh::LeanObject,
    mut v_k_6306_: *mut crate::leanh::LeanObject,
    mut v_fallback_6307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6308_ = crate::leanh::lean_box(0);
    v___x_6309_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_6304_,
        v_k_6306_,
        v___x_6308_,
        v_t_6305_,
    );
    if crate::leanh::lean_obj_tag(v___x_6309_) == 0 {
        crate::leanh::lean_inc(v_fallback_6307_);
        return v_fallback_6307_;
    } else {
        let mut v_val_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6310_ = crate::leanh::lean_ctor_get(v___x_6309_, 0);
        crate::leanh::lean_inc(v_val_6310_);
        crate::leanh::lean_dec_ref_known(v___x_6309_, 1);
        return v_val_6310_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGTD___redArg___boxed(
    mut v_cmp_6311_: *mut crate::leanh::LeanObject,
    mut v_t_6312_: *mut crate::leanh::LeanObject,
    mut v_k_6313_: *mut crate::leanh::LeanObject,
    mut v_fallback_6314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6315_ =
        l_Std_DTreeMap_getKeyGTD___redArg(v_cmp_6311_, v_t_6312_, v_k_6313_, v_fallback_6314_);
    crate::leanh::lean_dec(v_fallback_6314_);
    return v_res_6315_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGTD(
    mut v_00_u03b1_6316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6317_: *mut crate::leanh::LeanObject,
    mut v_cmp_6318_: *mut crate::leanh::LeanObject,
    mut v_t_6319_: *mut crate::leanh::LeanObject,
    mut v_k_6320_: *mut crate::leanh::LeanObject,
    mut v_fallback_6321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6322_ = crate::leanh::lean_box(0);
    v___x_6323_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_6318_,
        v_k_6320_,
        v___x_6322_,
        v_t_6319_,
    );
    if crate::leanh::lean_obj_tag(v___x_6323_) == 0 {
        crate::leanh::lean_inc(v_fallback_6321_);
        return v_fallback_6321_;
    } else {
        let mut v_val_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6324_ = crate::leanh::lean_ctor_get(v___x_6323_, 0);
        crate::leanh::lean_inc(v_val_6324_);
        crate::leanh::lean_dec_ref_known(v___x_6323_, 1);
        return v_val_6324_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyGTD___boxed(
    mut v_00_u03b1_6325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6326_: *mut crate::leanh::LeanObject,
    mut v_cmp_6327_: *mut crate::leanh::LeanObject,
    mut v_t_6328_: *mut crate::leanh::LeanObject,
    mut v_k_6329_: *mut crate::leanh::LeanObject,
    mut v_fallback_6330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6331_ = l_Std_DTreeMap_getKeyGTD(
        v_00_u03b1_6325_,
        v_00_u03b2_6326_,
        v_cmp_6327_,
        v_t_6328_,
        v_k_6329_,
        v_fallback_6330_,
    );
    crate::leanh::lean_dec(v_fallback_6330_);
    return v_res_6331_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLED___redArg(
    mut v_cmp_6332_: *mut crate::leanh::LeanObject,
    mut v_t_6333_: *mut crate::leanh::LeanObject,
    mut v_k_6334_: *mut crate::leanh::LeanObject,
    mut v_fallback_6335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6336_ = crate::leanh::lean_box(0);
    v___x_6337_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_6332_,
        v_k_6334_,
        v___x_6336_,
        v_t_6333_,
    );
    if crate::leanh::lean_obj_tag(v___x_6337_) == 0 {
        crate::leanh::lean_inc(v_fallback_6335_);
        return v_fallback_6335_;
    } else {
        let mut v_val_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6338_ = crate::leanh::lean_ctor_get(v___x_6337_, 0);
        crate::leanh::lean_inc(v_val_6338_);
        crate::leanh::lean_dec_ref_known(v___x_6337_, 1);
        return v_val_6338_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLED___redArg___boxed(
    mut v_cmp_6339_: *mut crate::leanh::LeanObject,
    mut v_t_6340_: *mut crate::leanh::LeanObject,
    mut v_k_6341_: *mut crate::leanh::LeanObject,
    mut v_fallback_6342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6343_ =
        l_Std_DTreeMap_getKeyLED___redArg(v_cmp_6339_, v_t_6340_, v_k_6341_, v_fallback_6342_);
    crate::leanh::lean_dec(v_fallback_6342_);
    return v_res_6343_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLED(
    mut v_00_u03b1_6344_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6345_: *mut crate::leanh::LeanObject,
    mut v_cmp_6346_: *mut crate::leanh::LeanObject,
    mut v_t_6347_: *mut crate::leanh::LeanObject,
    mut v_k_6348_: *mut crate::leanh::LeanObject,
    mut v_fallback_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6350_ = crate::leanh::lean_box(0);
    v___x_6351_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_6346_,
        v_k_6348_,
        v___x_6350_,
        v_t_6347_,
    );
    if crate::leanh::lean_obj_tag(v___x_6351_) == 0 {
        crate::leanh::lean_inc(v_fallback_6349_);
        return v_fallback_6349_;
    } else {
        let mut v_val_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6352_ = crate::leanh::lean_ctor_get(v___x_6351_, 0);
        crate::leanh::lean_inc(v_val_6352_);
        crate::leanh::lean_dec_ref_known(v___x_6351_, 1);
        return v_val_6352_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLED___boxed(
    mut v_00_u03b1_6353_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6354_: *mut crate::leanh::LeanObject,
    mut v_cmp_6355_: *mut crate::leanh::LeanObject,
    mut v_t_6356_: *mut crate::leanh::LeanObject,
    mut v_k_6357_: *mut crate::leanh::LeanObject,
    mut v_fallback_6358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6359_ = l_Std_DTreeMap_getKeyLED(
        v_00_u03b1_6353_,
        v_00_u03b2_6354_,
        v_cmp_6355_,
        v_t_6356_,
        v_k_6357_,
        v_fallback_6358_,
    );
    crate::leanh::lean_dec(v_fallback_6358_);
    return v_res_6359_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLTD___redArg(
    mut v_cmp_6360_: *mut crate::leanh::LeanObject,
    mut v_t_6361_: *mut crate::leanh::LeanObject,
    mut v_k_6362_: *mut crate::leanh::LeanObject,
    mut v_fallback_6363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6364_ = crate::leanh::lean_box(0);
    v___x_6365_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_6360_,
        v_k_6362_,
        v___x_6364_,
        v_t_6361_,
    );
    if crate::leanh::lean_obj_tag(v___x_6365_) == 0 {
        crate::leanh::lean_inc(v_fallback_6363_);
        return v_fallback_6363_;
    } else {
        let mut v_val_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6366_ = crate::leanh::lean_ctor_get(v___x_6365_, 0);
        crate::leanh::lean_inc(v_val_6366_);
        crate::leanh::lean_dec_ref_known(v___x_6365_, 1);
        return v_val_6366_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLTD___redArg___boxed(
    mut v_cmp_6367_: *mut crate::leanh::LeanObject,
    mut v_t_6368_: *mut crate::leanh::LeanObject,
    mut v_k_6369_: *mut crate::leanh::LeanObject,
    mut v_fallback_6370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6371_ =
        l_Std_DTreeMap_getKeyLTD___redArg(v_cmp_6367_, v_t_6368_, v_k_6369_, v_fallback_6370_);
    crate::leanh::lean_dec(v_fallback_6370_);
    return v_res_6371_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLTD(
    mut v_00_u03b1_6372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6373_: *mut crate::leanh::LeanObject,
    mut v_cmp_6374_: *mut crate::leanh::LeanObject,
    mut v_t_6375_: *mut crate::leanh::LeanObject,
    mut v_k_6376_: *mut crate::leanh::LeanObject,
    mut v_fallback_6377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6378_ = crate::leanh::lean_box(0);
    v___x_6379_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_6374_,
        v_k_6376_,
        v___x_6378_,
        v_t_6375_,
    );
    if crate::leanh::lean_obj_tag(v___x_6379_) == 0 {
        crate::leanh::lean_inc(v_fallback_6377_);
        return v_fallback_6377_;
    } else {
        let mut v_val_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6380_ = crate::leanh::lean_ctor_get(v___x_6379_, 0);
        crate::leanh::lean_inc(v_val_6380_);
        crate::leanh::lean_dec_ref_known(v___x_6379_, 1);
        return v_val_6380_;
    }
}
pub unsafe fn l_Std_DTreeMap_getKeyLTD___boxed(
    mut v_00_u03b1_6381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6382_: *mut crate::leanh::LeanObject,
    mut v_cmp_6383_: *mut crate::leanh::LeanObject,
    mut v_t_6384_: *mut crate::leanh::LeanObject,
    mut v_k_6385_: *mut crate::leanh::LeanObject,
    mut v_fallback_6386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6387_ = l_Std_DTreeMap_getKeyLTD(
        v_00_u03b1_6381_,
        v_00_u03b2_6382_,
        v_cmp_6383_,
        v_t_6384_,
        v_k_6385_,
        v_fallback_6386_,
    );
    crate::leanh::lean_dec(v_fallback_6386_);
    return v_res_6387_;
}
pub unsafe fn l_Std_DTreeMap_Const_getThenInsertIfNew_x3f___redArg(
    mut v_cmp_6388_: *mut crate::leanh::LeanObject,
    mut v_t_6389_: *mut crate::leanh::LeanObject,
    mut v_a_6390_: *mut crate::leanh::LeanObject,
    mut v_b_6391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_6390_);
    crate::leanh::lean_inc(v_t_6389_);
    crate::leanh::lean_inc_ref(v_cmp_6388_);
    v___x_6392_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_6388_, v_t_6389_, v_a_6390_);
    if crate::leanh::lean_obj_tag(v___x_6392_) == 0 {
        let mut v___x_6393_: u8 = 0;
        crate::leanh::lean_inc(v_t_6389_);
        crate::leanh::lean_inc(v_a_6390_);
        crate::leanh::lean_inc_ref(v_cmp_6388_);
        v___x_6393_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_6388_, v_a_6390_, v_t_6389_);
        if v___x_6393_ == 0 {
            let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6394_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_6388_,
                v_a_6390_,
                v_b_6391_,
                v_t_6389_,
            );
            v___x_6395_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6395_, 0, v___x_6392_);
            crate::leanh::lean_ctor_set(v___x_6395_, 1, v___x_6394_);
            return v___x_6395_;
        } else {
            let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_6391_);
            crate::leanh::lean_dec(v_a_6390_);
            crate::leanh::lean_dec_ref(v_cmp_6388_);
            v___x_6396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6396_, 0, v___x_6392_);
            crate::leanh::lean_ctor_set(v___x_6396_, 1, v_t_6389_);
            return v___x_6396_;
        }
    } else {
        let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_6391_);
        crate::leanh::lean_dec(v_a_6390_);
        crate::leanh::lean_dec_ref(v_cmp_6388_);
        v___x_6397_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6397_, 0, v___x_6392_);
        crate::leanh::lean_ctor_set(v___x_6397_, 1, v_t_6389_);
        return v___x_6397_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_6398_: *mut crate::leanh::LeanObject,
    mut v_cmp_6399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6400_: *mut crate::leanh::LeanObject,
    mut v_t_6401_: *mut crate::leanh::LeanObject,
    mut v_a_6402_: *mut crate::leanh::LeanObject,
    mut v_b_6403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_6402_);
    crate::leanh::lean_inc(v_t_6401_);
    crate::leanh::lean_inc_ref(v_cmp_6399_);
    v___x_6404_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_6399_, v_t_6401_, v_a_6402_);
    if crate::leanh::lean_obj_tag(v___x_6404_) == 0 {
        let mut v___x_6405_: u8 = 0;
        crate::leanh::lean_inc(v_t_6401_);
        crate::leanh::lean_inc(v_a_6402_);
        crate::leanh::lean_inc_ref(v_cmp_6399_);
        v___x_6405_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_6399_, v_a_6402_, v_t_6401_);
        if v___x_6405_ == 0 {
            let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6406_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                v_cmp_6399_,
                v_a_6402_,
                v_b_6403_,
                v_t_6401_,
            );
            v___x_6407_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6407_, 0, v___x_6404_);
            crate::leanh::lean_ctor_set(v___x_6407_, 1, v___x_6406_);
            return v___x_6407_;
        } else {
            let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_6403_);
            crate::leanh::lean_dec(v_a_6402_);
            crate::leanh::lean_dec_ref(v_cmp_6399_);
            v___x_6408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6408_, 0, v___x_6404_);
            crate::leanh::lean_ctor_set(v___x_6408_, 1, v_t_6401_);
            return v___x_6408_;
        }
    } else {
        let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_6403_);
        crate::leanh::lean_dec(v_a_6402_);
        crate::leanh::lean_dec_ref(v_cmp_6399_);
        v___x_6409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6409_, 0, v___x_6404_);
        crate::leanh::lean_ctor_set(v___x_6409_, 1, v_t_6401_);
        return v___x_6409_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_get_x3f___redArg(
    mut v_cmp_6410_: *mut crate::leanh::LeanObject,
    mut v_t_6411_: *mut crate::leanh::LeanObject,
    mut v_a_6412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6413_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_6410_, v_t_6411_, v_a_6412_);
    return v___x_6413_;
}
pub unsafe fn l_Std_DTreeMap_Const_get_x3f(
    mut v_00_u03b1_6414_: *mut crate::leanh::LeanObject,
    mut v_cmp_6415_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6416_: *mut crate::leanh::LeanObject,
    mut v_t_6417_: *mut crate::leanh::LeanObject,
    mut v_a_6418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6419_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_6415_, v_t_6417_, v_a_6418_);
    return v___x_6419_;
}
pub unsafe fn l_Std_DTreeMap_Const_get___redArg(
    mut v_cmp_6420_: *mut crate::leanh::LeanObject,
    mut v_t_6421_: *mut crate::leanh::LeanObject,
    mut v_a_6422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6423_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_6420_, v_t_6421_, v_a_6422_);
    return v___x_6423_;
}
pub unsafe fn l_Std_DTreeMap_Const_get(
    mut v_00_u03b1_6424_: *mut crate::leanh::LeanObject,
    mut v_cmp_6425_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6426_: *mut crate::leanh::LeanObject,
    mut v_t_6427_: *mut crate::leanh::LeanObject,
    mut v_a_6428_: *mut crate::leanh::LeanObject,
    mut v_h_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6430_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_6425_, v_t_6427_, v_a_6428_);
    return v___x_6430_;
}
pub unsafe fn l_Std_DTreeMap_Const_get_x21___redArg(
    mut v_cmp_6431_: *mut crate::leanh::LeanObject,
    mut v_inst_6432_: *mut crate::leanh::LeanObject,
    mut v_t_6433_: *mut crate::leanh::LeanObject,
    mut v_a_6434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_6431_,
        v_inst_6432_,
        v_t_6433_,
        v_a_6434_,
    );
    return v___x_6435_;
}
pub unsafe fn l_Std_DTreeMap_Const_get_x21___redArg___boxed(
    mut v_cmp_6436_: *mut crate::leanh::LeanObject,
    mut v_inst_6437_: *mut crate::leanh::LeanObject,
    mut v_t_6438_: *mut crate::leanh::LeanObject,
    mut v_a_6439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6440_ =
        l_Std_DTreeMap_Const_get_x21___redArg(v_cmp_6436_, v_inst_6437_, v_t_6438_, v_a_6439_);
    crate::leanh::lean_dec(v_inst_6437_);
    return v_res_6440_;
}
pub unsafe fn l_Std_DTreeMap_Const_get_x21(
    mut v_00_u03b1_6441_: *mut crate::leanh::LeanObject,
    mut v_cmp_6442_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6443_: *mut crate::leanh::LeanObject,
    mut v_inst_6444_: *mut crate::leanh::LeanObject,
    mut v_t_6445_: *mut crate::leanh::LeanObject,
    mut v_a_6446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6447_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_6442_,
        v_inst_6444_,
        v_t_6445_,
        v_a_6446_,
    );
    return v___x_6447_;
}
pub unsafe fn l_Std_DTreeMap_Const_get_x21___boxed(
    mut v_00_u03b1_6448_: *mut crate::leanh::LeanObject,
    mut v_cmp_6449_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6450_: *mut crate::leanh::LeanObject,
    mut v_inst_6451_: *mut crate::leanh::LeanObject,
    mut v_t_6452_: *mut crate::leanh::LeanObject,
    mut v_a_6453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6454_ = l_Std_DTreeMap_Const_get_x21(
        v_00_u03b1_6448_,
        v_cmp_6449_,
        v_00_u03b2_6450_,
        v_inst_6451_,
        v_t_6452_,
        v_a_6453_,
    );
    crate::leanh::lean_dec(v_inst_6451_);
    return v_res_6454_;
}
pub unsafe fn l_Std_DTreeMap_Const_getD___redArg(
    mut v_cmp_6455_: *mut crate::leanh::LeanObject,
    mut v_t_6456_: *mut crate::leanh::LeanObject,
    mut v_a_6457_: *mut crate::leanh::LeanObject,
    mut v_fallback_6458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6459_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_6455_,
        v_t_6456_,
        v_a_6457_,
        v_fallback_6458_,
    );
    return v___x_6459_;
}
pub unsafe fn l_Std_DTreeMap_Const_getD___redArg___boxed(
    mut v_cmp_6460_: *mut crate::leanh::LeanObject,
    mut v_t_6461_: *mut crate::leanh::LeanObject,
    mut v_a_6462_: *mut crate::leanh::LeanObject,
    mut v_fallback_6463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6464_ =
        l_Std_DTreeMap_Const_getD___redArg(v_cmp_6460_, v_t_6461_, v_a_6462_, v_fallback_6463_);
    crate::leanh::lean_dec(v_fallback_6463_);
    return v_res_6464_;
}
pub unsafe fn l_Std_DTreeMap_Const_getD(
    mut v_00_u03b1_6465_: *mut crate::leanh::LeanObject,
    mut v_cmp_6466_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6467_: *mut crate::leanh::LeanObject,
    mut v_t_6468_: *mut crate::leanh::LeanObject,
    mut v_a_6469_: *mut crate::leanh::LeanObject,
    mut v_fallback_6470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6471_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_6466_,
        v_t_6468_,
        v_a_6469_,
        v_fallback_6470_,
    );
    return v___x_6471_;
}
pub unsafe fn l_Std_DTreeMap_Const_getD___boxed(
    mut v_00_u03b1_6472_: *mut crate::leanh::LeanObject,
    mut v_cmp_6473_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6474_: *mut crate::leanh::LeanObject,
    mut v_t_6475_: *mut crate::leanh::LeanObject,
    mut v_a_6476_: *mut crate::leanh::LeanObject,
    mut v_fallback_6477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6478_ = l_Std_DTreeMap_Const_getD(
        v_00_u03b1_6472_,
        v_cmp_6473_,
        v_00_u03b2_6474_,
        v_t_6475_,
        v_a_6476_,
        v_fallback_6477_,
    );
    crate::leanh::lean_dec(v_fallback_6477_);
    return v_res_6478_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x3f___redArg(
    mut v_t_6479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6480_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_6479_);
    return v___x_6480_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x3f___redArg___boxed(
    mut v_t_6481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6482_ = l_Std_DTreeMap_Const_minEntry_x3f___redArg(v_t_6481_);
    crate::leanh::lean_dec(v_t_6481_);
    return v_res_6482_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x3f(
    mut v_00_u03b1_6483_: *mut crate::leanh::LeanObject,
    mut v_cmp_6484_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6485_: *mut crate::leanh::LeanObject,
    mut v_t_6486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6487_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_6486_);
    return v___x_6487_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x3f___boxed(
    mut v_00_u03b1_6488_: *mut crate::leanh::LeanObject,
    mut v_cmp_6489_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6490_: *mut crate::leanh::LeanObject,
    mut v_t_6491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6492_ = l_Std_DTreeMap_Const_minEntry_x3f(
        v_00_u03b1_6488_,
        v_cmp_6489_,
        v_00_u03b2_6490_,
        v_t_6491_,
    );
    crate::leanh::lean_dec(v_t_6491_);
    crate::leanh::lean_dec_ref(v_cmp_6489_);
    return v_res_6492_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry___redArg(
    mut v_t_6493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6494_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_6493_);
    return v___x_6494_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry___redArg___boxed(
    mut v_t_6495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6496_ = l_Std_DTreeMap_Const_minEntry___redArg(v_t_6495_);
    crate::leanh::lean_dec(v_t_6495_);
    return v_res_6496_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry(
    mut v_00_u03b1_6497_: *mut crate::leanh::LeanObject,
    mut v_cmp_6498_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6499_: *mut crate::leanh::LeanObject,
    mut v_t_6500_: *mut crate::leanh::LeanObject,
    mut v_h_6501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6502_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_t_6500_);
    return v___x_6502_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry___boxed(
    mut v_00_u03b1_6503_: *mut crate::leanh::LeanObject,
    mut v_cmp_6504_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6505_: *mut crate::leanh::LeanObject,
    mut v_t_6506_: *mut crate::leanh::LeanObject,
    mut v_h_6507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6508_ = l_Std_DTreeMap_Const_minEntry(
        v_00_u03b1_6503_,
        v_cmp_6504_,
        v_00_u03b2_6505_,
        v_t_6506_,
        v_h_6507_,
    );
    crate::leanh::lean_dec(v_t_6506_);
    crate::leanh::lean_dec_ref(v_cmp_6504_);
    return v_res_6508_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x21___redArg(
    mut v_inst_6509_: *mut crate::leanh::LeanObject,
    mut v_t_6510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6511_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_6509_, v_t_6510_);
    return v___x_6511_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x21___redArg___boxed(
    mut v_inst_6512_: *mut crate::leanh::LeanObject,
    mut v_t_6513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6514_ = l_Std_DTreeMap_Const_minEntry_x21___redArg(v_inst_6512_, v_t_6513_);
    crate::leanh::lean_dec(v_t_6513_);
    crate::leanh::lean_dec_ref(v_inst_6512_);
    return v_res_6514_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x21(
    mut v_00_u03b1_6515_: *mut crate::leanh::LeanObject,
    mut v_cmp_6516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6517_: *mut crate::leanh::LeanObject,
    mut v_inst_6518_: *mut crate::leanh::LeanObject,
    mut v_t_6519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_6518_, v_t_6519_);
    return v___x_6520_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntry_x21___boxed(
    mut v_00_u03b1_6521_: *mut crate::leanh::LeanObject,
    mut v_cmp_6522_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6523_: *mut crate::leanh::LeanObject,
    mut v_inst_6524_: *mut crate::leanh::LeanObject,
    mut v_t_6525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6526_ = l_Std_DTreeMap_Const_minEntry_x21(
        v_00_u03b1_6521_,
        v_cmp_6522_,
        v_00_u03b2_6523_,
        v_inst_6524_,
        v_t_6525_,
    );
    crate::leanh::lean_dec(v_t_6525_);
    crate::leanh::lean_dec_ref(v_inst_6524_);
    crate::leanh::lean_dec_ref(v_cmp_6522_);
    return v_res_6526_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntryD___redArg(
    mut v_t_6527_: *mut crate::leanh::LeanObject,
    mut v_fallback_6528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6529_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_6527_, v_fallback_6528_);
    return v___x_6529_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntryD___redArg___boxed(
    mut v_t_6530_: *mut crate::leanh::LeanObject,
    mut v_fallback_6531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6532_ = l_Std_DTreeMap_Const_minEntryD___redArg(v_t_6530_, v_fallback_6531_);
    crate::leanh::lean_dec_ref(v_fallback_6531_);
    crate::leanh::lean_dec(v_t_6530_);
    return v_res_6532_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntryD(
    mut v_00_u03b1_6533_: *mut crate::leanh::LeanObject,
    mut v_cmp_6534_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6535_: *mut crate::leanh::LeanObject,
    mut v_t_6536_: *mut crate::leanh::LeanObject,
    mut v_fallback_6537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6538_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_6536_, v_fallback_6537_);
    return v___x_6538_;
}
pub unsafe fn l_Std_DTreeMap_Const_minEntryD___boxed(
    mut v_00_u03b1_6539_: *mut crate::leanh::LeanObject,
    mut v_cmp_6540_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6541_: *mut crate::leanh::LeanObject,
    mut v_t_6542_: *mut crate::leanh::LeanObject,
    mut v_fallback_6543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6544_ = l_Std_DTreeMap_Const_minEntryD(
        v_00_u03b1_6539_,
        v_cmp_6540_,
        v_00_u03b2_6541_,
        v_t_6542_,
        v_fallback_6543_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6543_);
    crate::leanh::lean_dec(v_t_6542_);
    crate::leanh::lean_dec_ref(v_cmp_6540_);
    return v_res_6544_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x3f___redArg(
    mut v_t_6545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6546_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_6545_);
    return v___x_6546_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x3f___redArg___boxed(
    mut v_t_6547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6548_ = l_Std_DTreeMap_Const_maxEntry_x3f___redArg(v_t_6547_);
    crate::leanh::lean_dec(v_t_6547_);
    return v_res_6548_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x3f(
    mut v_00_u03b1_6549_: *mut crate::leanh::LeanObject,
    mut v_cmp_6550_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6551_: *mut crate::leanh::LeanObject,
    mut v_t_6552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6553_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_6552_);
    return v___x_6553_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x3f___boxed(
    mut v_00_u03b1_6554_: *mut crate::leanh::LeanObject,
    mut v_cmp_6555_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6556_: *mut crate::leanh::LeanObject,
    mut v_t_6557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6558_ = l_Std_DTreeMap_Const_maxEntry_x3f(
        v_00_u03b1_6554_,
        v_cmp_6555_,
        v_00_u03b2_6556_,
        v_t_6557_,
    );
    crate::leanh::lean_dec(v_t_6557_);
    crate::leanh::lean_dec_ref(v_cmp_6555_);
    return v_res_6558_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry___redArg(
    mut v_t_6559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6560_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_6559_);
    return v___x_6560_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry___redArg___boxed(
    mut v_t_6561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6562_ = l_Std_DTreeMap_Const_maxEntry___redArg(v_t_6561_);
    crate::leanh::lean_dec(v_t_6561_);
    return v_res_6562_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry(
    mut v_00_u03b1_6563_: *mut crate::leanh::LeanObject,
    mut v_cmp_6564_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6565_: *mut crate::leanh::LeanObject,
    mut v_t_6566_: *mut crate::leanh::LeanObject,
    mut v_h_6567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6568_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_t_6566_);
    return v___x_6568_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry___boxed(
    mut v_00_u03b1_6569_: *mut crate::leanh::LeanObject,
    mut v_cmp_6570_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6571_: *mut crate::leanh::LeanObject,
    mut v_t_6572_: *mut crate::leanh::LeanObject,
    mut v_h_6573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6574_ = l_Std_DTreeMap_Const_maxEntry(
        v_00_u03b1_6569_,
        v_cmp_6570_,
        v_00_u03b2_6571_,
        v_t_6572_,
        v_h_6573_,
    );
    crate::leanh::lean_dec(v_t_6572_);
    crate::leanh::lean_dec_ref(v_cmp_6570_);
    return v_res_6574_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x21___redArg(
    mut v_inst_6575_: *mut crate::leanh::LeanObject,
    mut v_t_6576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6577_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_6575_, v_t_6576_);
    return v___x_6577_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x21___redArg___boxed(
    mut v_inst_6578_: *mut crate::leanh::LeanObject,
    mut v_t_6579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6580_ = l_Std_DTreeMap_Const_maxEntry_x21___redArg(v_inst_6578_, v_t_6579_);
    crate::leanh::lean_dec(v_t_6579_);
    crate::leanh::lean_dec_ref(v_inst_6578_);
    return v_res_6580_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x21(
    mut v_00_u03b1_6581_: *mut crate::leanh::LeanObject,
    mut v_cmp_6582_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6583_: *mut crate::leanh::LeanObject,
    mut v_inst_6584_: *mut crate::leanh::LeanObject,
    mut v_t_6585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6586_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_6584_, v_t_6585_);
    return v___x_6586_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntry_x21___boxed(
    mut v_00_u03b1_6587_: *mut crate::leanh::LeanObject,
    mut v_cmp_6588_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6589_: *mut crate::leanh::LeanObject,
    mut v_inst_6590_: *mut crate::leanh::LeanObject,
    mut v_t_6591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6592_ = l_Std_DTreeMap_Const_maxEntry_x21(
        v_00_u03b1_6587_,
        v_cmp_6588_,
        v_00_u03b2_6589_,
        v_inst_6590_,
        v_t_6591_,
    );
    crate::leanh::lean_dec(v_t_6591_);
    crate::leanh::lean_dec_ref(v_inst_6590_);
    crate::leanh::lean_dec_ref(v_cmp_6588_);
    return v_res_6592_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntryD___redArg(
    mut v_t_6593_: *mut crate::leanh::LeanObject,
    mut v_fallback_6594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6595_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_6593_, v_fallback_6594_);
    return v___x_6595_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntryD___redArg___boxed(
    mut v_t_6596_: *mut crate::leanh::LeanObject,
    mut v_fallback_6597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6598_ = l_Std_DTreeMap_Const_maxEntryD___redArg(v_t_6596_, v_fallback_6597_);
    crate::leanh::lean_dec_ref(v_fallback_6597_);
    crate::leanh::lean_dec(v_t_6596_);
    return v_res_6598_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntryD(
    mut v_00_u03b1_6599_: *mut crate::leanh::LeanObject,
    mut v_cmp_6600_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6601_: *mut crate::leanh::LeanObject,
    mut v_t_6602_: *mut crate::leanh::LeanObject,
    mut v_fallback_6603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6604_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_6602_, v_fallback_6603_);
    return v___x_6604_;
}
pub unsafe fn l_Std_DTreeMap_Const_maxEntryD___boxed(
    mut v_00_u03b1_6605_: *mut crate::leanh::LeanObject,
    mut v_cmp_6606_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6607_: *mut crate::leanh::LeanObject,
    mut v_t_6608_: *mut crate::leanh::LeanObject,
    mut v_fallback_6609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6610_ = l_Std_DTreeMap_Const_maxEntryD(
        v_00_u03b1_6605_,
        v_cmp_6606_,
        v_00_u03b2_6607_,
        v_t_6608_,
        v_fallback_6609_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6609_);
    crate::leanh::lean_dec(v_t_6608_);
    crate::leanh::lean_dec_ref(v_cmp_6606_);
    return v_res_6610_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(
    mut v_t_6611_: *mut crate::leanh::LeanObject,
    mut v_n_6612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6613_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_6611_, v_n_6612_);
    return v___x_6613_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg___boxed(
    mut v_t_6614_: *mut crate::leanh::LeanObject,
    mut v_n_6615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6616_ = l_Std_DTreeMap_Const_entryAtIdx_x3f___redArg(v_t_6614_, v_n_6615_);
    crate::leanh::lean_dec(v_t_6614_);
    return v_res_6616_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x3f(
    mut v_00_u03b1_6617_: *mut crate::leanh::LeanObject,
    mut v_cmp_6618_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6619_: *mut crate::leanh::LeanObject,
    mut v_t_6620_: *mut crate::leanh::LeanObject,
    mut v_n_6621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6622_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_6620_, v_n_6621_);
    return v___x_6622_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_6623_: *mut crate::leanh::LeanObject,
    mut v_cmp_6624_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6625_: *mut crate::leanh::LeanObject,
    mut v_t_6626_: *mut crate::leanh::LeanObject,
    mut v_n_6627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6628_ = l_Std_DTreeMap_Const_entryAtIdx_x3f(
        v_00_u03b1_6623_,
        v_cmp_6624_,
        v_00_u03b2_6625_,
        v_t_6626_,
        v_n_6627_,
    );
    crate::leanh::lean_dec(v_t_6626_);
    crate::leanh::lean_dec_ref(v_cmp_6624_);
    return v_res_6628_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx___redArg(
    mut v_t_6629_: *mut crate::leanh::LeanObject,
    mut v_n_6630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6631_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_6629_, v_n_6630_);
    return v___x_6631_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx___redArg___boxed(
    mut v_t_6632_: *mut crate::leanh::LeanObject,
    mut v_n_6633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6634_ = l_Std_DTreeMap_Const_entryAtIdx___redArg(v_t_6632_, v_n_6633_);
    crate::leanh::lean_dec(v_t_6632_);
    return v_res_6634_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx(
    mut v_00_u03b1_6635_: *mut crate::leanh::LeanObject,
    mut v_cmp_6636_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6637_: *mut crate::leanh::LeanObject,
    mut v_t_6638_: *mut crate::leanh::LeanObject,
    mut v_n_6639_: *mut crate::leanh::LeanObject,
    mut v_h_6640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6641_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_t_6638_, v_n_6639_);
    return v___x_6641_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx___boxed(
    mut v_00_u03b1_6642_: *mut crate::leanh::LeanObject,
    mut v_cmp_6643_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6644_: *mut crate::leanh::LeanObject,
    mut v_t_6645_: *mut crate::leanh::LeanObject,
    mut v_n_6646_: *mut crate::leanh::LeanObject,
    mut v_h_6647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6648_ = l_Std_DTreeMap_Const_entryAtIdx(
        v_00_u03b1_6642_,
        v_cmp_6643_,
        v_00_u03b2_6644_,
        v_t_6645_,
        v_n_6646_,
        v_h_6647_,
    );
    crate::leanh::lean_dec(v_t_6645_);
    crate::leanh::lean_dec_ref(v_cmp_6643_);
    return v_res_6648_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(
    mut v_inst_6649_: *mut crate::leanh::LeanObject,
    mut v_t_6650_: *mut crate::leanh::LeanObject,
    mut v_n_6651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6652_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_6649_,
        v_t_6650_,
        v_n_6651_,
    );
    return v___x_6652_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x21___redArg___boxed(
    mut v_inst_6653_: *mut crate::leanh::LeanObject,
    mut v_t_6654_: *mut crate::leanh::LeanObject,
    mut v_n_6655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6656_ = l_Std_DTreeMap_Const_entryAtIdx_x21___redArg(v_inst_6653_, v_t_6654_, v_n_6655_);
    crate::leanh::lean_dec(v_t_6654_);
    crate::leanh::lean_dec_ref(v_inst_6653_);
    return v_res_6656_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x21(
    mut v_00_u03b1_6657_: *mut crate::leanh::LeanObject,
    mut v_cmp_6658_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6659_: *mut crate::leanh::LeanObject,
    mut v_inst_6660_: *mut crate::leanh::LeanObject,
    mut v_t_6661_: *mut crate::leanh::LeanObject,
    mut v_n_6662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6663_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_6660_,
        v_t_6661_,
        v_n_6662_,
    );
    return v___x_6663_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdx_x21___boxed(
    mut v_00_u03b1_6664_: *mut crate::leanh::LeanObject,
    mut v_cmp_6665_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6666_: *mut crate::leanh::LeanObject,
    mut v_inst_6667_: *mut crate::leanh::LeanObject,
    mut v_t_6668_: *mut crate::leanh::LeanObject,
    mut v_n_6669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6670_ = l_Std_DTreeMap_Const_entryAtIdx_x21(
        v_00_u03b1_6664_,
        v_cmp_6665_,
        v_00_u03b2_6666_,
        v_inst_6667_,
        v_t_6668_,
        v_n_6669_,
    );
    crate::leanh::lean_dec(v_t_6668_);
    crate::leanh::lean_dec_ref(v_inst_6667_);
    crate::leanh::lean_dec_ref(v_cmp_6665_);
    return v_res_6670_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdxD___redArg(
    mut v_t_6671_: *mut crate::leanh::LeanObject,
    mut v_n_6672_: *mut crate::leanh::LeanObject,
    mut v_fallback_6673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6674_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_6671_,
        v_n_6672_,
        v_fallback_6673_,
    );
    return v___x_6674_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdxD___redArg___boxed(
    mut v_t_6675_: *mut crate::leanh::LeanObject,
    mut v_n_6676_: *mut crate::leanh::LeanObject,
    mut v_fallback_6677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6678_ = l_Std_DTreeMap_Const_entryAtIdxD___redArg(v_t_6675_, v_n_6676_, v_fallback_6677_);
    crate::leanh::lean_dec_ref(v_fallback_6677_);
    crate::leanh::lean_dec(v_t_6675_);
    return v_res_6678_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdxD(
    mut v_00_u03b1_6679_: *mut crate::leanh::LeanObject,
    mut v_cmp_6680_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6681_: *mut crate::leanh::LeanObject,
    mut v_t_6682_: *mut crate::leanh::LeanObject,
    mut v_n_6683_: *mut crate::leanh::LeanObject,
    mut v_fallback_6684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6685_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_6682_,
        v_n_6683_,
        v_fallback_6684_,
    );
    return v___x_6685_;
}
pub unsafe fn l_Std_DTreeMap_Const_entryAtIdxD___boxed(
    mut v_00_u03b1_6686_: *mut crate::leanh::LeanObject,
    mut v_cmp_6687_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6688_: *mut crate::leanh::LeanObject,
    mut v_t_6689_: *mut crate::leanh::LeanObject,
    mut v_n_6690_: *mut crate::leanh::LeanObject,
    mut v_fallback_6691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6692_ = l_Std_DTreeMap_Const_entryAtIdxD(
        v_00_u03b1_6686_,
        v_cmp_6687_,
        v_00_u03b2_6688_,
        v_t_6689_,
        v_n_6690_,
        v_fallback_6691_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6691_);
    crate::leanh::lean_dec(v_t_6689_);
    crate::leanh::lean_dec_ref(v_cmp_6687_);
    return v_res_6692_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE_x3f___redArg(
    mut v_cmp_6693_: *mut crate::leanh::LeanObject,
    mut v_t_6694_: *mut crate::leanh::LeanObject,
    mut v_k_6695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6696_ = crate::leanh::lean_box(0);
    v___x_6697_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6693_,
        v_k_6695_,
        v___x_6696_,
        v_t_6694_,
    );
    return v___x_6697_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE_x3f(
    mut v_00_u03b1_6698_: *mut crate::leanh::LeanObject,
    mut v_cmp_6699_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6700_: *mut crate::leanh::LeanObject,
    mut v_t_6701_: *mut crate::leanh::LeanObject,
    mut v_k_6702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6703_ = crate::leanh::lean_box(0);
    v___x_6704_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6699_,
        v_k_6702_,
        v___x_6703_,
        v_t_6701_,
    );
    return v___x_6704_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT_x3f___redArg(
    mut v_cmp_6705_: *mut crate::leanh::LeanObject,
    mut v_t_6706_: *mut crate::leanh::LeanObject,
    mut v_k_6707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6708_ = crate::leanh::lean_box(0);
    v___x_6709_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6705_,
        v_k_6707_,
        v___x_6708_,
        v_t_6706_,
    );
    return v___x_6709_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT_x3f(
    mut v_00_u03b1_6710_: *mut crate::leanh::LeanObject,
    mut v_cmp_6711_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6712_: *mut crate::leanh::LeanObject,
    mut v_t_6713_: *mut crate::leanh::LeanObject,
    mut v_k_6714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6715_ = crate::leanh::lean_box(0);
    v___x_6716_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6711_,
        v_k_6714_,
        v___x_6715_,
        v_t_6713_,
    );
    return v___x_6716_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE_x3f___redArg(
    mut v_cmp_6717_: *mut crate::leanh::LeanObject,
    mut v_t_6718_: *mut crate::leanh::LeanObject,
    mut v_k_6719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6720_ = crate::leanh::lean_box(0);
    v___x_6721_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6717_,
        v_k_6719_,
        v___x_6720_,
        v_t_6718_,
    );
    return v___x_6721_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE_x3f(
    mut v_00_u03b1_6722_: *mut crate::leanh::LeanObject,
    mut v_cmp_6723_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6724_: *mut crate::leanh::LeanObject,
    mut v_t_6725_: *mut crate::leanh::LeanObject,
    mut v_k_6726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6727_ = crate::leanh::lean_box(0);
    v___x_6728_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6723_,
        v_k_6726_,
        v___x_6727_,
        v_t_6725_,
    );
    return v___x_6728_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT_x3f___redArg(
    mut v_cmp_6729_: *mut crate::leanh::LeanObject,
    mut v_t_6730_: *mut crate::leanh::LeanObject,
    mut v_k_6731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6732_ = crate::leanh::lean_box(0);
    v___x_6733_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6729_,
        v_k_6731_,
        v___x_6732_,
        v_t_6730_,
    );
    return v___x_6733_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT_x3f(
    mut v_00_u03b1_6734_: *mut crate::leanh::LeanObject,
    mut v_cmp_6735_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6736_: *mut crate::leanh::LeanObject,
    mut v_t_6737_: *mut crate::leanh::LeanObject,
    mut v_k_6738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6739_ = crate::leanh::lean_box(0);
    v___x_6740_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6735_,
        v_k_6738_,
        v___x_6739_,
        v_t_6737_,
    );
    return v___x_6740_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE_x21___redArg(
    mut v_cmp_6741_: *mut crate::leanh::LeanObject,
    mut v_inst_6742_: *mut crate::leanh::LeanObject,
    mut v_t_6743_: *mut crate::leanh::LeanObject,
    mut v_k_6744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6745_ = crate::leanh::lean_box(0);
    v___x_6746_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6741_,
        v_k_6744_,
        v___x_6745_,
        v_t_6743_,
    );
    if crate::leanh::lean_obj_tag(v___x_6746_) == 0 {
        let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6747_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6748_ = l_panic___redArg(v_inst_6742_, v___x_6747_);
        return v___x_6748_;
    } else {
        let mut v_val_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6749_ = crate::leanh::lean_ctor_get(v___x_6746_, 0);
        crate::leanh::lean_inc(v_val_6749_);
        crate::leanh::lean_dec_ref_known(v___x_6746_, 1);
        return v_val_6749_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE_x21___redArg___boxed(
    mut v_cmp_6750_: *mut crate::leanh::LeanObject,
    mut v_inst_6751_: *mut crate::leanh::LeanObject,
    mut v_t_6752_: *mut crate::leanh::LeanObject,
    mut v_k_6753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6754_ = l_Std_DTreeMap_Const_getEntryGE_x21___redArg(
        v_cmp_6750_,
        v_inst_6751_,
        v_t_6752_,
        v_k_6753_,
    );
    crate::leanh::lean_dec_ref(v_inst_6751_);
    return v_res_6754_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE_x21(
    mut v_00_u03b1_6755_: *mut crate::leanh::LeanObject,
    mut v_cmp_6756_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6757_: *mut crate::leanh::LeanObject,
    mut v_inst_6758_: *mut crate::leanh::LeanObject,
    mut v_t_6759_: *mut crate::leanh::LeanObject,
    mut v_k_6760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6761_ = crate::leanh::lean_box(0);
    v___x_6762_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6756_,
        v_k_6760_,
        v___x_6761_,
        v_t_6759_,
    );
    if crate::leanh::lean_obj_tag(v___x_6762_) == 0 {
        let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6763_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6764_ = l_panic___redArg(v_inst_6758_, v___x_6763_);
        return v___x_6764_;
    } else {
        let mut v_val_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6765_ = crate::leanh::lean_ctor_get(v___x_6762_, 0);
        crate::leanh::lean_inc(v_val_6765_);
        crate::leanh::lean_dec_ref_known(v___x_6762_, 1);
        return v_val_6765_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE_x21___boxed(
    mut v_00_u03b1_6766_: *mut crate::leanh::LeanObject,
    mut v_cmp_6767_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6768_: *mut crate::leanh::LeanObject,
    mut v_inst_6769_: *mut crate::leanh::LeanObject,
    mut v_t_6770_: *mut crate::leanh::LeanObject,
    mut v_k_6771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6772_ = l_Std_DTreeMap_Const_getEntryGE_x21(
        v_00_u03b1_6766_,
        v_cmp_6767_,
        v_00_u03b2_6768_,
        v_inst_6769_,
        v_t_6770_,
        v_k_6771_,
    );
    crate::leanh::lean_dec_ref(v_inst_6769_);
    return v_res_6772_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT_x21___redArg(
    mut v_cmp_6773_: *mut crate::leanh::LeanObject,
    mut v_inst_6774_: *mut crate::leanh::LeanObject,
    mut v_t_6775_: *mut crate::leanh::LeanObject,
    mut v_k_6776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6777_ = crate::leanh::lean_box(0);
    v___x_6778_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6773_,
        v_k_6776_,
        v___x_6777_,
        v_t_6775_,
    );
    if crate::leanh::lean_obj_tag(v___x_6778_) == 0 {
        let mut v___x_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6779_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6780_ = l_panic___redArg(v_inst_6774_, v___x_6779_);
        return v___x_6780_;
    } else {
        let mut v_val_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6781_ = crate::leanh::lean_ctor_get(v___x_6778_, 0);
        crate::leanh::lean_inc(v_val_6781_);
        crate::leanh::lean_dec_ref_known(v___x_6778_, 1);
        return v_val_6781_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT_x21___redArg___boxed(
    mut v_cmp_6782_: *mut crate::leanh::LeanObject,
    mut v_inst_6783_: *mut crate::leanh::LeanObject,
    mut v_t_6784_: *mut crate::leanh::LeanObject,
    mut v_k_6785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6786_ = l_Std_DTreeMap_Const_getEntryGT_x21___redArg(
        v_cmp_6782_,
        v_inst_6783_,
        v_t_6784_,
        v_k_6785_,
    );
    crate::leanh::lean_dec_ref(v_inst_6783_);
    return v_res_6786_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT_x21(
    mut v_00_u03b1_6787_: *mut crate::leanh::LeanObject,
    mut v_cmp_6788_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6789_: *mut crate::leanh::LeanObject,
    mut v_inst_6790_: *mut crate::leanh::LeanObject,
    mut v_t_6791_: *mut crate::leanh::LeanObject,
    mut v_k_6792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6793_ = crate::leanh::lean_box(0);
    v___x_6794_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6788_,
        v_k_6792_,
        v___x_6793_,
        v_t_6791_,
    );
    if crate::leanh::lean_obj_tag(v___x_6794_) == 0 {
        let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6795_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6796_ = l_panic___redArg(v_inst_6790_, v___x_6795_);
        return v___x_6796_;
    } else {
        let mut v_val_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6797_ = crate::leanh::lean_ctor_get(v___x_6794_, 0);
        crate::leanh::lean_inc(v_val_6797_);
        crate::leanh::lean_dec_ref_known(v___x_6794_, 1);
        return v_val_6797_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT_x21___boxed(
    mut v_00_u03b1_6798_: *mut crate::leanh::LeanObject,
    mut v_cmp_6799_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6800_: *mut crate::leanh::LeanObject,
    mut v_inst_6801_: *mut crate::leanh::LeanObject,
    mut v_t_6802_: *mut crate::leanh::LeanObject,
    mut v_k_6803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6804_ = l_Std_DTreeMap_Const_getEntryGT_x21(
        v_00_u03b1_6798_,
        v_cmp_6799_,
        v_00_u03b2_6800_,
        v_inst_6801_,
        v_t_6802_,
        v_k_6803_,
    );
    crate::leanh::lean_dec_ref(v_inst_6801_);
    return v_res_6804_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE_x21___redArg(
    mut v_cmp_6805_: *mut crate::leanh::LeanObject,
    mut v_inst_6806_: *mut crate::leanh::LeanObject,
    mut v_t_6807_: *mut crate::leanh::LeanObject,
    mut v_k_6808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6809_ = crate::leanh::lean_box(0);
    v___x_6810_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6805_,
        v_k_6808_,
        v___x_6809_,
        v_t_6807_,
    );
    if crate::leanh::lean_obj_tag(v___x_6810_) == 0 {
        let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6811_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6812_ = l_panic___redArg(v_inst_6806_, v___x_6811_);
        return v___x_6812_;
    } else {
        let mut v_val_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6813_ = crate::leanh::lean_ctor_get(v___x_6810_, 0);
        crate::leanh::lean_inc(v_val_6813_);
        crate::leanh::lean_dec_ref_known(v___x_6810_, 1);
        return v_val_6813_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE_x21___redArg___boxed(
    mut v_cmp_6814_: *mut crate::leanh::LeanObject,
    mut v_inst_6815_: *mut crate::leanh::LeanObject,
    mut v_t_6816_: *mut crate::leanh::LeanObject,
    mut v_k_6817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6818_ = l_Std_DTreeMap_Const_getEntryLE_x21___redArg(
        v_cmp_6814_,
        v_inst_6815_,
        v_t_6816_,
        v_k_6817_,
    );
    crate::leanh::lean_dec_ref(v_inst_6815_);
    return v_res_6818_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE_x21(
    mut v_00_u03b1_6819_: *mut crate::leanh::LeanObject,
    mut v_cmp_6820_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6821_: *mut crate::leanh::LeanObject,
    mut v_inst_6822_: *mut crate::leanh::LeanObject,
    mut v_t_6823_: *mut crate::leanh::LeanObject,
    mut v_k_6824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6825_ = crate::leanh::lean_box(0);
    v___x_6826_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6820_,
        v_k_6824_,
        v___x_6825_,
        v_t_6823_,
    );
    if crate::leanh::lean_obj_tag(v___x_6826_) == 0 {
        let mut v___x_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6827_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6828_ = l_panic___redArg(v_inst_6822_, v___x_6827_);
        return v___x_6828_;
    } else {
        let mut v_val_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6829_ = crate::leanh::lean_ctor_get(v___x_6826_, 0);
        crate::leanh::lean_inc(v_val_6829_);
        crate::leanh::lean_dec_ref_known(v___x_6826_, 1);
        return v_val_6829_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE_x21___boxed(
    mut v_00_u03b1_6830_: *mut crate::leanh::LeanObject,
    mut v_cmp_6831_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6832_: *mut crate::leanh::LeanObject,
    mut v_inst_6833_: *mut crate::leanh::LeanObject,
    mut v_t_6834_: *mut crate::leanh::LeanObject,
    mut v_k_6835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6836_ = l_Std_DTreeMap_Const_getEntryLE_x21(
        v_00_u03b1_6830_,
        v_cmp_6831_,
        v_00_u03b2_6832_,
        v_inst_6833_,
        v_t_6834_,
        v_k_6835_,
    );
    crate::leanh::lean_dec_ref(v_inst_6833_);
    return v_res_6836_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT_x21___redArg(
    mut v_cmp_6837_: *mut crate::leanh::LeanObject,
    mut v_inst_6838_: *mut crate::leanh::LeanObject,
    mut v_t_6839_: *mut crate::leanh::LeanObject,
    mut v_k_6840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6841_ = crate::leanh::lean_box(0);
    v___x_6842_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6837_,
        v_k_6840_,
        v___x_6841_,
        v_t_6839_,
    );
    if crate::leanh::lean_obj_tag(v___x_6842_) == 0 {
        let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6843_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6844_ = l_panic___redArg(v_inst_6838_, v___x_6843_);
        return v___x_6844_;
    } else {
        let mut v_val_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6845_ = crate::leanh::lean_ctor_get(v___x_6842_, 0);
        crate::leanh::lean_inc(v_val_6845_);
        crate::leanh::lean_dec_ref_known(v___x_6842_, 1);
        return v_val_6845_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT_x21___redArg___boxed(
    mut v_cmp_6846_: *mut crate::leanh::LeanObject,
    mut v_inst_6847_: *mut crate::leanh::LeanObject,
    mut v_t_6848_: *mut crate::leanh::LeanObject,
    mut v_k_6849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6850_ = l_Std_DTreeMap_Const_getEntryLT_x21___redArg(
        v_cmp_6846_,
        v_inst_6847_,
        v_t_6848_,
        v_k_6849_,
    );
    crate::leanh::lean_dec_ref(v_inst_6847_);
    return v_res_6850_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT_x21(
    mut v_00_u03b1_6851_: *mut crate::leanh::LeanObject,
    mut v_cmp_6852_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6853_: *mut crate::leanh::LeanObject,
    mut v_inst_6854_: *mut crate::leanh::LeanObject,
    mut v_t_6855_: *mut crate::leanh::LeanObject,
    mut v_k_6856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6857_ = crate::leanh::lean_box(0);
    v___x_6858_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6852_,
        v_k_6856_,
        v___x_6857_,
        v_t_6855_,
    );
    if crate::leanh::lean_obj_tag(v___x_6858_) == 0 {
        let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6859_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_DTreeMap_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6860_ = l_panic___redArg(v_inst_6854_, v___x_6859_);
        return v___x_6860_;
    } else {
        let mut v_val_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6861_ = crate::leanh::lean_ctor_get(v___x_6858_, 0);
        crate::leanh::lean_inc(v_val_6861_);
        crate::leanh::lean_dec_ref_known(v___x_6858_, 1);
        return v_val_6861_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT_x21___boxed(
    mut v_00_u03b1_6862_: *mut crate::leanh::LeanObject,
    mut v_cmp_6863_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6864_: *mut crate::leanh::LeanObject,
    mut v_inst_6865_: *mut crate::leanh::LeanObject,
    mut v_t_6866_: *mut crate::leanh::LeanObject,
    mut v_k_6867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6868_ = l_Std_DTreeMap_Const_getEntryLT_x21(
        v_00_u03b1_6862_,
        v_cmp_6863_,
        v_00_u03b2_6864_,
        v_inst_6865_,
        v_t_6866_,
        v_k_6867_,
    );
    crate::leanh::lean_dec_ref(v_inst_6865_);
    return v_res_6868_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGED___redArg(
    mut v_cmp_6869_: *mut crate::leanh::LeanObject,
    mut v_t_6870_: *mut crate::leanh::LeanObject,
    mut v_k_6871_: *mut crate::leanh::LeanObject,
    mut v_fallback_6872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6873_ = crate::leanh::lean_box(0);
    v___x_6874_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6869_,
        v_k_6871_,
        v___x_6873_,
        v_t_6870_,
    );
    if crate::leanh::lean_obj_tag(v___x_6874_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6872_);
        return v_fallback_6872_;
    } else {
        let mut v_val_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6875_ = crate::leanh::lean_ctor_get(v___x_6874_, 0);
        crate::leanh::lean_inc(v_val_6875_);
        crate::leanh::lean_dec_ref_known(v___x_6874_, 1);
        return v_val_6875_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGED___redArg___boxed(
    mut v_cmp_6876_: *mut crate::leanh::LeanObject,
    mut v_t_6877_: *mut crate::leanh::LeanObject,
    mut v_k_6878_: *mut crate::leanh::LeanObject,
    mut v_fallback_6879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6880_ = l_Std_DTreeMap_Const_getEntryGED___redArg(
        v_cmp_6876_,
        v_t_6877_,
        v_k_6878_,
        v_fallback_6879_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6879_);
    return v_res_6880_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGED(
    mut v_00_u03b1_6881_: *mut crate::leanh::LeanObject,
    mut v_cmp_6882_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6883_: *mut crate::leanh::LeanObject,
    mut v_t_6884_: *mut crate::leanh::LeanObject,
    mut v_k_6885_: *mut crate::leanh::LeanObject,
    mut v_fallback_6886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6887_ = crate::leanh::lean_box(0);
    v___x_6888_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_6882_,
        v_k_6885_,
        v___x_6887_,
        v_t_6884_,
    );
    if crate::leanh::lean_obj_tag(v___x_6888_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6886_);
        return v_fallback_6886_;
    } else {
        let mut v_val_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6889_ = crate::leanh::lean_ctor_get(v___x_6888_, 0);
        crate::leanh::lean_inc(v_val_6889_);
        crate::leanh::lean_dec_ref_known(v___x_6888_, 1);
        return v_val_6889_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGED___boxed(
    mut v_00_u03b1_6890_: *mut crate::leanh::LeanObject,
    mut v_cmp_6891_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6892_: *mut crate::leanh::LeanObject,
    mut v_t_6893_: *mut crate::leanh::LeanObject,
    mut v_k_6894_: *mut crate::leanh::LeanObject,
    mut v_fallback_6895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6896_ = l_Std_DTreeMap_Const_getEntryGED(
        v_00_u03b1_6890_,
        v_cmp_6891_,
        v_00_u03b2_6892_,
        v_t_6893_,
        v_k_6894_,
        v_fallback_6895_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6895_);
    return v_res_6896_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGTD___redArg(
    mut v_cmp_6897_: *mut crate::leanh::LeanObject,
    mut v_t_6898_: *mut crate::leanh::LeanObject,
    mut v_k_6899_: *mut crate::leanh::LeanObject,
    mut v_fallback_6900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6901_ = crate::leanh::lean_box(0);
    v___x_6902_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6897_,
        v_k_6899_,
        v___x_6901_,
        v_t_6898_,
    );
    if crate::leanh::lean_obj_tag(v___x_6902_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6900_);
        return v_fallback_6900_;
    } else {
        let mut v_val_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6903_ = crate::leanh::lean_ctor_get(v___x_6902_, 0);
        crate::leanh::lean_inc(v_val_6903_);
        crate::leanh::lean_dec_ref_known(v___x_6902_, 1);
        return v_val_6903_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGTD___redArg___boxed(
    mut v_cmp_6904_: *mut crate::leanh::LeanObject,
    mut v_t_6905_: *mut crate::leanh::LeanObject,
    mut v_k_6906_: *mut crate::leanh::LeanObject,
    mut v_fallback_6907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6908_ = l_Std_DTreeMap_Const_getEntryGTD___redArg(
        v_cmp_6904_,
        v_t_6905_,
        v_k_6906_,
        v_fallback_6907_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6907_);
    return v_res_6908_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGTD(
    mut v_00_u03b1_6909_: *mut crate::leanh::LeanObject,
    mut v_cmp_6910_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6911_: *mut crate::leanh::LeanObject,
    mut v_t_6912_: *mut crate::leanh::LeanObject,
    mut v_k_6913_: *mut crate::leanh::LeanObject,
    mut v_fallback_6914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6915_ = crate::leanh::lean_box(0);
    v___x_6916_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_6910_,
        v_k_6913_,
        v___x_6915_,
        v_t_6912_,
    );
    if crate::leanh::lean_obj_tag(v___x_6916_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6914_);
        return v_fallback_6914_;
    } else {
        let mut v_val_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6917_ = crate::leanh::lean_ctor_get(v___x_6916_, 0);
        crate::leanh::lean_inc(v_val_6917_);
        crate::leanh::lean_dec_ref_known(v___x_6916_, 1);
        return v_val_6917_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGTD___boxed(
    mut v_00_u03b1_6918_: *mut crate::leanh::LeanObject,
    mut v_cmp_6919_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6920_: *mut crate::leanh::LeanObject,
    mut v_t_6921_: *mut crate::leanh::LeanObject,
    mut v_k_6922_: *mut crate::leanh::LeanObject,
    mut v_fallback_6923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6924_ = l_Std_DTreeMap_Const_getEntryGTD(
        v_00_u03b1_6918_,
        v_cmp_6919_,
        v_00_u03b2_6920_,
        v_t_6921_,
        v_k_6922_,
        v_fallback_6923_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6923_);
    return v_res_6924_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLED___redArg(
    mut v_cmp_6925_: *mut crate::leanh::LeanObject,
    mut v_t_6926_: *mut crate::leanh::LeanObject,
    mut v_k_6927_: *mut crate::leanh::LeanObject,
    mut v_fallback_6928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6929_ = crate::leanh::lean_box(0);
    v___x_6930_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6925_,
        v_k_6927_,
        v___x_6929_,
        v_t_6926_,
    );
    if crate::leanh::lean_obj_tag(v___x_6930_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6928_);
        return v_fallback_6928_;
    } else {
        let mut v_val_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6931_ = crate::leanh::lean_ctor_get(v___x_6930_, 0);
        crate::leanh::lean_inc(v_val_6931_);
        crate::leanh::lean_dec_ref_known(v___x_6930_, 1);
        return v_val_6931_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLED___redArg___boxed(
    mut v_cmp_6932_: *mut crate::leanh::LeanObject,
    mut v_t_6933_: *mut crate::leanh::LeanObject,
    mut v_k_6934_: *mut crate::leanh::LeanObject,
    mut v_fallback_6935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6936_ = l_Std_DTreeMap_Const_getEntryLED___redArg(
        v_cmp_6932_,
        v_t_6933_,
        v_k_6934_,
        v_fallback_6935_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6935_);
    return v_res_6936_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLED(
    mut v_00_u03b1_6937_: *mut crate::leanh::LeanObject,
    mut v_cmp_6938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6939_: *mut crate::leanh::LeanObject,
    mut v_t_6940_: *mut crate::leanh::LeanObject,
    mut v_k_6941_: *mut crate::leanh::LeanObject,
    mut v_fallback_6942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6943_ = crate::leanh::lean_box(0);
    v___x_6944_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_6938_,
        v_k_6941_,
        v___x_6943_,
        v_t_6940_,
    );
    if crate::leanh::lean_obj_tag(v___x_6944_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6942_);
        return v_fallback_6942_;
    } else {
        let mut v_val_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6945_ = crate::leanh::lean_ctor_get(v___x_6944_, 0);
        crate::leanh::lean_inc(v_val_6945_);
        crate::leanh::lean_dec_ref_known(v___x_6944_, 1);
        return v_val_6945_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLED___boxed(
    mut v_00_u03b1_6946_: *mut crate::leanh::LeanObject,
    mut v_cmp_6947_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6948_: *mut crate::leanh::LeanObject,
    mut v_t_6949_: *mut crate::leanh::LeanObject,
    mut v_k_6950_: *mut crate::leanh::LeanObject,
    mut v_fallback_6951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6952_ = l_Std_DTreeMap_Const_getEntryLED(
        v_00_u03b1_6946_,
        v_cmp_6947_,
        v_00_u03b2_6948_,
        v_t_6949_,
        v_k_6950_,
        v_fallback_6951_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6951_);
    return v_res_6952_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLTD___redArg(
    mut v_cmp_6953_: *mut crate::leanh::LeanObject,
    mut v_t_6954_: *mut crate::leanh::LeanObject,
    mut v_k_6955_: *mut crate::leanh::LeanObject,
    mut v_fallback_6956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6957_ = crate::leanh::lean_box(0);
    v___x_6958_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6953_,
        v_k_6955_,
        v___x_6957_,
        v_t_6954_,
    );
    if crate::leanh::lean_obj_tag(v___x_6958_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6956_);
        return v_fallback_6956_;
    } else {
        let mut v_val_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6959_ = crate::leanh::lean_ctor_get(v___x_6958_, 0);
        crate::leanh::lean_inc(v_val_6959_);
        crate::leanh::lean_dec_ref_known(v___x_6958_, 1);
        return v_val_6959_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLTD___redArg___boxed(
    mut v_cmp_6960_: *mut crate::leanh::LeanObject,
    mut v_t_6961_: *mut crate::leanh::LeanObject,
    mut v_k_6962_: *mut crate::leanh::LeanObject,
    mut v_fallback_6963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6964_ = l_Std_DTreeMap_Const_getEntryLTD___redArg(
        v_cmp_6960_,
        v_t_6961_,
        v_k_6962_,
        v_fallback_6963_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6963_);
    return v_res_6964_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLTD(
    mut v_00_u03b1_6965_: *mut crate::leanh::LeanObject,
    mut v_cmp_6966_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6967_: *mut crate::leanh::LeanObject,
    mut v_t_6968_: *mut crate::leanh::LeanObject,
    mut v_k_6969_: *mut crate::leanh::LeanObject,
    mut v_fallback_6970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6971_ = crate::leanh::lean_box(0);
    v___x_6972_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_6966_,
        v_k_6969_,
        v___x_6971_,
        v_t_6968_,
    );
    if crate::leanh::lean_obj_tag(v___x_6972_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6970_);
        return v_fallback_6970_;
    } else {
        let mut v_val_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6973_ = crate::leanh::lean_ctor_get(v___x_6972_, 0);
        crate::leanh::lean_inc(v_val_6973_);
        crate::leanh::lean_dec_ref_known(v___x_6972_, 1);
        return v_val_6973_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLTD___boxed(
    mut v_00_u03b1_6974_: *mut crate::leanh::LeanObject,
    mut v_cmp_6975_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6976_: *mut crate::leanh::LeanObject,
    mut v_t_6977_: *mut crate::leanh::LeanObject,
    mut v_k_6978_: *mut crate::leanh::LeanObject,
    mut v_fallback_6979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6980_ = l_Std_DTreeMap_Const_getEntryLTD(
        v_00_u03b1_6974_,
        v_cmp_6975_,
        v_00_u03b2_6976_,
        v_t_6977_,
        v_k_6978_,
        v_fallback_6979_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6979_);
    return v_res_6980_;
}
pub unsafe fn l_Std_DTreeMap_filter___redArg(
    mut v_f_6981_: *mut crate::leanh::LeanObject,
    mut v_t_6982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6983_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_6981_, v_t_6982_);
    return v___x_6983_;
}
pub unsafe fn l_Std_DTreeMap_filter(
    mut v_00_u03b1_6984_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6985_: *mut crate::leanh::LeanObject,
    mut v_cmp_6986_: *mut crate::leanh::LeanObject,
    mut v_f_6987_: *mut crate::leanh::LeanObject,
    mut v_t_6988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6989_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v_f_6987_, v_t_6988_);
    return v___x_6989_;
}
pub unsafe fn l_Std_DTreeMap_filter___boxed(
    mut v_00_u03b1_6990_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6991_: *mut crate::leanh::LeanObject,
    mut v_cmp_6992_: *mut crate::leanh::LeanObject,
    mut v_f_6993_: *mut crate::leanh::LeanObject,
    mut v_t_6994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6995_ = l_Std_DTreeMap_filter(
        v_00_u03b1_6990_,
        v_00_u03b2_6991_,
        v_cmp_6992_,
        v_f_6993_,
        v_t_6994_,
    );
    crate::leanh::lean_dec_ref(v_cmp_6992_);
    return v_res_6995_;
}
pub unsafe fn l_Std_DTreeMap_foldlM___redArg(
    mut v_inst_6996_: *mut crate::leanh::LeanObject,
    mut v_f_6997_: *mut crate::leanh::LeanObject,
    mut v_init_6998_: *mut crate::leanh::LeanObject,
    mut v_t_6999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7000_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_6996_,
        v_f_6997_,
        v_init_6998_,
        v_t_6999_,
    );
    return v___x_7000_;
}
pub unsafe fn l_Std_DTreeMap_foldlM(
    mut v_00_u03b1_7001_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7002_: *mut crate::leanh::LeanObject,
    mut v_cmp_7003_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7004_: *mut crate::leanh::LeanObject,
    mut v_m_7005_: *mut crate::leanh::LeanObject,
    mut v_inst_7006_: *mut crate::leanh::LeanObject,
    mut v_f_7007_: *mut crate::leanh::LeanObject,
    mut v_init_7008_: *mut crate::leanh::LeanObject,
    mut v_t_7009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7010_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_7006_,
        v_f_7007_,
        v_init_7008_,
        v_t_7009_,
    );
    return v___x_7010_;
}
pub unsafe fn l_Std_DTreeMap_foldlM___boxed(
    mut v_00_u03b1_7011_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7012_: *mut crate::leanh::LeanObject,
    mut v_cmp_7013_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7014_: *mut crate::leanh::LeanObject,
    mut v_m_7015_: *mut crate::leanh::LeanObject,
    mut v_inst_7016_: *mut crate::leanh::LeanObject,
    mut v_f_7017_: *mut crate::leanh::LeanObject,
    mut v_init_7018_: *mut crate::leanh::LeanObject,
    mut v_t_7019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7020_ = l_Std_DTreeMap_foldlM(
        v_00_u03b1_7011_,
        v_00_u03b2_7012_,
        v_cmp_7013_,
        v_00_u03b4_7014_,
        v_m_7015_,
        v_inst_7016_,
        v_f_7017_,
        v_init_7018_,
        v_t_7019_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7013_);
    return v_res_7020_;
}
pub unsafe fn l_Std_DTreeMap_foldl___redArg(
    mut v_f_7021_: *mut crate::leanh::LeanObject,
    mut v_init_7022_: *mut crate::leanh::LeanObject,
    mut v_t_7023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7024_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_7021_, v_init_7022_, v_t_7023_);
    return v___x_7024_;
}
pub unsafe fn l_Std_DTreeMap_foldl(
    mut v_00_u03b1_7025_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7026_: *mut crate::leanh::LeanObject,
    mut v_cmp_7027_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7028_: *mut crate::leanh::LeanObject,
    mut v_f_7029_: *mut crate::leanh::LeanObject,
    mut v_init_7030_: *mut crate::leanh::LeanObject,
    mut v_t_7031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7032_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_7029_, v_init_7030_, v_t_7031_);
    return v___x_7032_;
}
pub unsafe fn l_Std_DTreeMap_foldl___boxed(
    mut v_00_u03b1_7033_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7034_: *mut crate::leanh::LeanObject,
    mut v_cmp_7035_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7036_: *mut crate::leanh::LeanObject,
    mut v_f_7037_: *mut crate::leanh::LeanObject,
    mut v_init_7038_: *mut crate::leanh::LeanObject,
    mut v_t_7039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7040_ = l_Std_DTreeMap_foldl(
        v_00_u03b1_7033_,
        v_00_u03b2_7034_,
        v_cmp_7035_,
        v_00_u03b4_7036_,
        v_f_7037_,
        v_init_7038_,
        v_t_7039_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7035_);
    return v_res_7040_;
}
pub unsafe fn l_Std_DTreeMap_foldrM___redArg(
    mut v_inst_7041_: *mut crate::leanh::LeanObject,
    mut v_f_7042_: *mut crate::leanh::LeanObject,
    mut v_init_7043_: *mut crate::leanh::LeanObject,
    mut v_t_7044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7045_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_7041_,
        v_f_7042_,
        v_init_7043_,
        v_t_7044_,
    );
    return v___x_7045_;
}
pub unsafe fn l_Std_DTreeMap_foldrM(
    mut v_00_u03b1_7046_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7047_: *mut crate::leanh::LeanObject,
    mut v_cmp_7048_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7049_: *mut crate::leanh::LeanObject,
    mut v_m_7050_: *mut crate::leanh::LeanObject,
    mut v_inst_7051_: *mut crate::leanh::LeanObject,
    mut v_f_7052_: *mut crate::leanh::LeanObject,
    mut v_init_7053_: *mut crate::leanh::LeanObject,
    mut v_t_7054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7055_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_7051_,
        v_f_7052_,
        v_init_7053_,
        v_t_7054_,
    );
    return v___x_7055_;
}
pub unsafe fn l_Std_DTreeMap_foldrM___boxed(
    mut v_00_u03b1_7056_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7057_: *mut crate::leanh::LeanObject,
    mut v_cmp_7058_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7059_: *mut crate::leanh::LeanObject,
    mut v_m_7060_: *mut crate::leanh::LeanObject,
    mut v_inst_7061_: *mut crate::leanh::LeanObject,
    mut v_f_7062_: *mut crate::leanh::LeanObject,
    mut v_init_7063_: *mut crate::leanh::LeanObject,
    mut v_t_7064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7065_ = l_Std_DTreeMap_foldrM(
        v_00_u03b1_7056_,
        v_00_u03b2_7057_,
        v_cmp_7058_,
        v_00_u03b4_7059_,
        v_m_7060_,
        v_inst_7061_,
        v_f_7062_,
        v_init_7063_,
        v_t_7064_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7058_);
    return v_res_7065_;
}
pub unsafe fn l_Std_DTreeMap_foldr___redArg___lam__0(
    mut v_f_7066_: *mut crate::leanh::LeanObject,
    mut v_x1_7067_: *mut crate::leanh::LeanObject,
    mut v_x2_7068_: *mut crate::leanh::LeanObject,
    mut v_x3_7069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7070_ = crate::leanh::lean_apply_3(v_f_7066_, v_x1_7067_, v_x2_7068_, v_x3_7069_);
    return v___x_7070_;
}
pub unsafe fn l_Std_DTreeMap_foldr___redArg(
    mut v_f_7090_: *mut crate::leanh::LeanObject,
    mut v_init_7091_: *mut crate::leanh::LeanObject,
    mut v_t_7092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7093_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7093_, 0, v_f_7090_);
    v___x_7094_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7095_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7094_,
        v___f_7093_,
        v_init_7091_,
        v_t_7092_,
    );
    return v___x_7095_;
}
pub unsafe fn l_Std_DTreeMap_foldr(
    mut v_00_u03b1_7096_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7097_: *mut crate::leanh::LeanObject,
    mut v_cmp_7098_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7099_: *mut crate::leanh::LeanObject,
    mut v_f_7100_: *mut crate::leanh::LeanObject,
    mut v_init_7101_: *mut crate::leanh::LeanObject,
    mut v_t_7102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7103_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7103_, 0, v_f_7100_);
    v___x_7104_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7105_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7104_,
        v___f_7103_,
        v_init_7101_,
        v_t_7102_,
    );
    return v___x_7105_;
}
pub unsafe fn l_Std_DTreeMap_foldr___boxed(
    mut v_00_u03b1_7106_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7107_: *mut crate::leanh::LeanObject,
    mut v_cmp_7108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7109_: *mut crate::leanh::LeanObject,
    mut v_f_7110_: *mut crate::leanh::LeanObject,
    mut v_init_7111_: *mut crate::leanh::LeanObject,
    mut v_t_7112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7113_ = l_Std_DTreeMap_foldr(
        v_00_u03b1_7106_,
        v_00_u03b2_7107_,
        v_cmp_7108_,
        v_00_u03b4_7109_,
        v_f_7110_,
        v_init_7111_,
        v_t_7112_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7108_);
    return v_res_7113_;
}
pub unsafe fn l_Std_DTreeMap_partition___redArg___lam__0(
    mut v_f_7114_: *mut crate::leanh::LeanObject,
    mut v_cmp_7115_: *mut crate::leanh::LeanObject,
    mut v_x_7116_: *mut crate::leanh::LeanObject,
    mut v_a_7117_: *mut crate::leanh::LeanObject,
    mut v_b_7118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7123_: u8 = 0;
    let mut v___x_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: u8 = 0;
    let mut v___x_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_7119_ = crate::leanh::lean_ctor_get(v_x_7116_, 0);
                v_snd_7120_ = crate::leanh::lean_ctor_get(v_x_7116_, 1);
                v_isSharedCheck_7134_ = (!crate::leanh::lean_is_exclusive(v_x_7116_)) as u8;
                if v_isSharedCheck_7134_ == 0 {
                    v___x_7122_ = v_x_7116_;
                    v_isShared_7123_ = v_isSharedCheck_7134_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7120_);
                    crate::leanh::lean_inc(v_fst_7119_);
                    crate::leanh::lean_dec(v_x_7116_);
                    v___x_7122_ = crate::leanh::lean_box(0);
                    v_isShared_7123_ = v_isSharedCheck_7134_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_b_7118_);
                crate::leanh::lean_inc(v_a_7117_);
                v___x_7124_ = crate::leanh::lean_apply_2(v_f_7114_, v_a_7117_, v_b_7118_);
                v___x_7125_ = (crate::leanh::lean_unbox(v___x_7124_) as u8);
                if v___x_7125_ == 0 {
                    v___x_7126_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_7115_,
                        v_a_7117_,
                        v_b_7118_,
                        v_snd_7120_,
                    );
                    if v_isShared_7123_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7122_, 1, v___x_7126_);
                        v___x_7128_ = v___x_7122_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7129_, 0, v_fst_7119_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7129_, 1, v___x_7126_);
                        v___x_7128_ = v_reuseFailAlloc_7129_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7130_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_7115_,
                        v_a_7117_,
                        v_b_7118_,
                        v_fst_7119_,
                    );
                    if v_isShared_7123_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7122_, 0, v___x_7130_);
                        v___x_7132_ = v___x_7122_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7133_, 0, v___x_7130_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7133_, 1, v_snd_7120_);
                        v___x_7132_ = v_reuseFailAlloc_7133_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7128_;
            }
            3 => {
                return v___x_7132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_partition___redArg(
    mut v_cmp_7137_: *mut crate::leanh::LeanObject,
    mut v_f_7138_: *mut crate::leanh::LeanObject,
    mut v_t_7139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7140_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7140_, 0, v_f_7138_);
    crate::leanh::lean_closure_set(v___f_7140_, 1, v_cmp_7137_);
    v___x_7141_ = l_Std_DTreeMap_partition___redArg___closed__0;
    v___x_7142_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7140_, v___x_7141_, v_t_7139_);
    return v___x_7142_;
}
pub unsafe fn l_Std_DTreeMap_partition(
    mut v_00_u03b1_7143_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7144_: *mut crate::leanh::LeanObject,
    mut v_cmp_7145_: *mut crate::leanh::LeanObject,
    mut v_f_7146_: *mut crate::leanh::LeanObject,
    mut v_t_7147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7148_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7148_, 0, v_f_7146_);
    crate::leanh::lean_closure_set(v___f_7148_, 1, v_cmp_7145_);
    v___x_7149_ = l_Std_DTreeMap_partition___redArg___closed__0;
    v___x_7150_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7148_, v___x_7149_, v_t_7147_);
    return v___x_7150_;
}
pub unsafe fn l_Std_DTreeMap_forM___redArg___lam__0(
    mut v_f_7151_: *mut crate::leanh::LeanObject,
    mut v_x_7152_: *mut crate::leanh::LeanObject,
    mut v_k_7153_: *mut crate::leanh::LeanObject,
    mut v_v_7154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7155_ = crate::leanh::lean_apply_2(v_f_7151_, v_k_7153_, v_v_7154_);
    return v___x_7155_;
}
pub unsafe fn l_Std_DTreeMap_forM___redArg(
    mut v_inst_7156_: *mut crate::leanh::LeanObject,
    mut v_f_7157_: *mut crate::leanh::LeanObject,
    mut v_t_7158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7159_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7159_, 0, v_f_7157_);
    v___x_7160_ = crate::leanh::lean_box(0);
    v___x_7161_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_7156_,
        v___f_7159_,
        v___x_7160_,
        v_t_7158_,
    );
    return v___x_7161_;
}
pub unsafe fn l_Std_DTreeMap_forM(
    mut v_00_u03b1_7162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7163_: *mut crate::leanh::LeanObject,
    mut v_cmp_7164_: *mut crate::leanh::LeanObject,
    mut v_m_7165_: *mut crate::leanh::LeanObject,
    mut v_inst_7166_: *mut crate::leanh::LeanObject,
    mut v_f_7167_: *mut crate::leanh::LeanObject,
    mut v_t_7168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7169_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7169_, 0, v_f_7167_);
    v___x_7170_ = crate::leanh::lean_box(0);
    v___x_7171_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_7166_,
        v___f_7169_,
        v___x_7170_,
        v_t_7168_,
    );
    return v___x_7171_;
}
pub unsafe fn l_Std_DTreeMap_forM___boxed(
    mut v_00_u03b1_7172_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7173_: *mut crate::leanh::LeanObject,
    mut v_cmp_7174_: *mut crate::leanh::LeanObject,
    mut v_m_7175_: *mut crate::leanh::LeanObject,
    mut v_inst_7176_: *mut crate::leanh::LeanObject,
    mut v_f_7177_: *mut crate::leanh::LeanObject,
    mut v_t_7178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7179_ = l_Std_DTreeMap_forM(
        v_00_u03b1_7172_,
        v_00_u03b2_7173_,
        v_cmp_7174_,
        v_m_7175_,
        v_inst_7176_,
        v_f_7177_,
        v_t_7178_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7174_);
    return v_res_7179_;
}
pub unsafe fn l_Std_DTreeMap_forIn___redArg___lam__0(
    mut v_toPure_7180_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_7182_ = crate::leanh::lean_ctor_get(v_____do__lift_7181_, 0);
    crate::leanh::lean_inc(v_a_7182_);
    crate::leanh::lean_dec_ref(v_____do__lift_7181_);
    v___x_7183_ = crate::leanh::lean_apply_2(v_toPure_7180_, crate::leanh::lean_box(0), v_a_7182_);
    return v___x_7183_;
}
pub unsafe fn l_Std_DTreeMap_forIn___redArg(
    mut v_inst_7184_: *mut crate::leanh::LeanObject,
    mut v_f_7185_: *mut crate::leanh::LeanObject,
    mut v_init_7186_: *mut crate::leanh::LeanObject,
    mut v_t_7187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7188_ = crate::leanh::lean_ctor_get(v_inst_7184_, 0);
    v_toBind_7189_ = crate::leanh::lean_ctor_get(v_inst_7184_, 1);
    crate::leanh::lean_inc(v_toBind_7189_);
    v_toPure_7190_ = crate::leanh::lean_ctor_get(v_toApplicative_7188_, 1);
    crate::leanh::lean_inc(v_toPure_7190_);
    v___x_7191_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_7184_,
        v_f_7185_,
        v_init_7186_,
        v_t_7187_,
    );
    v___f_7192_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7192_, 0, v_toPure_7190_);
    v___x_7193_ = crate::leanh::lean_apply_4(
        v_toBind_7189_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7191_,
        v___f_7192_,
    );
    return v___x_7193_;
}
pub unsafe fn l_Std_DTreeMap_forIn(
    mut v_00_u03b1_7194_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7195_: *mut crate::leanh::LeanObject,
    mut v_cmp_7196_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7197_: *mut crate::leanh::LeanObject,
    mut v_m_7198_: *mut crate::leanh::LeanObject,
    mut v_inst_7199_: *mut crate::leanh::LeanObject,
    mut v_f_7200_: *mut crate::leanh::LeanObject,
    mut v_init_7201_: *mut crate::leanh::LeanObject,
    mut v_t_7202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7203_ = crate::leanh::lean_ctor_get(v_inst_7199_, 0);
    v_toBind_7204_ = crate::leanh::lean_ctor_get(v_inst_7199_, 1);
    crate::leanh::lean_inc(v_toBind_7204_);
    v_toPure_7205_ = crate::leanh::lean_ctor_get(v_toApplicative_7203_, 1);
    crate::leanh::lean_inc(v_toPure_7205_);
    v___x_7206_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_7199_,
        v_f_7200_,
        v_init_7201_,
        v_t_7202_,
    );
    v___f_7207_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7207_, 0, v_toPure_7205_);
    v___x_7208_ = crate::leanh::lean_apply_4(
        v_toBind_7204_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7206_,
        v___f_7207_,
    );
    return v___x_7208_;
}
pub unsafe fn l_Std_DTreeMap_forIn___boxed(
    mut v_00_u03b1_7209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7210_: *mut crate::leanh::LeanObject,
    mut v_cmp_7211_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7212_: *mut crate::leanh::LeanObject,
    mut v_m_7213_: *mut crate::leanh::LeanObject,
    mut v_inst_7214_: *mut crate::leanh::LeanObject,
    mut v_f_7215_: *mut crate::leanh::LeanObject,
    mut v_init_7216_: *mut crate::leanh::LeanObject,
    mut v_t_7217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7218_ = l_Std_DTreeMap_forIn(
        v_00_u03b1_7209_,
        v_00_u03b2_7210_,
        v_cmp_7211_,
        v_00_u03b4_7212_,
        v_m_7213_,
        v_inst_7214_,
        v_f_7215_,
        v_init_7216_,
        v_t_7217_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7211_);
    return v_res_7218_;
}
pub unsafe fn l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0(
    mut v_f_7219_: *mut crate::leanh::LeanObject,
    mut v_x_7220_: *mut crate::leanh::LeanObject,
    mut v_k_7221_: *mut crate::leanh::LeanObject,
    mut v_v_7222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7223_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7223_, 0, v_k_7221_);
    crate::leanh::lean_ctor_set(v___x_7223_, 1, v_v_7222_);
    v___x_7224_ = crate::leanh::lean_apply_1(v_f_7219_, v___x_7223_);
    return v___x_7224_;
}
pub unsafe fn l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1(
    mut v_inst_7225_: *mut crate::leanh::LeanObject,
    mut v_t_7226_: *mut crate::leanh::LeanObject,
    mut v_f_7227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7228_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7228_, 0, v_f_7227_);
    v___x_7229_ = crate::leanh::lean_box(0);
    v___x_7230_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_7225_,
        v___f_7228_,
        v___x_7229_,
        v_t_7226_,
    );
    return v___x_7230_;
}
pub unsafe fn l_Std_DTreeMap_instForMSigmaOfMonad___redArg(
    mut v_inst_7231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7232_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7232_, 0, v_inst_7231_);
    return v___f_7232_;
}
pub unsafe fn l_Std_DTreeMap_instForMSigmaOfMonad(
    mut v_00_u03b1_7233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7234_: *mut crate::leanh::LeanObject,
    mut v_cmp_7235_: *mut crate::leanh::LeanObject,
    mut v_m_7236_: *mut crate::leanh::LeanObject,
    mut v_inst_7237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7238_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instForMSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7238_, 0, v_inst_7237_);
    return v___f_7238_;
}
pub unsafe fn l_Std_DTreeMap_instForMSigmaOfMonad___boxed(
    mut v_00_u03b1_7239_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7240_: *mut crate::leanh::LeanObject,
    mut v_cmp_7241_: *mut crate::leanh::LeanObject,
    mut v_m_7242_: *mut crate::leanh::LeanObject,
    mut v_inst_7243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7244_ = l_Std_DTreeMap_instForMSigmaOfMonad(
        v_00_u03b1_7239_,
        v_00_u03b2_7240_,
        v_cmp_7241_,
        v_m_7242_,
        v_inst_7243_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7241_);
    return v_res_7244_;
}
pub unsafe fn l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0(
    mut v_f_7245_: *mut crate::leanh::LeanObject,
    mut v_a_7246_: *mut crate::leanh::LeanObject,
    mut v_b_7247_: *mut crate::leanh::LeanObject,
    mut v_acc_7248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7249_, 0, v_a_7246_);
    crate::leanh::lean_ctor_set(v___x_7249_, 1, v_b_7247_);
    v___x_7250_ = crate::leanh::lean_apply_2(v_f_7245_, v___x_7249_, v_acc_7248_);
    return v___x_7250_;
}
pub unsafe fn l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2(
    mut v_inst_7251_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7252_: *mut crate::leanh::LeanObject,
    mut v_m_7253_: *mut crate::leanh::LeanObject,
    mut v_init_7254_: *mut crate::leanh::LeanObject,
    mut v_f_7255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7256_ = crate::leanh::lean_ctor_get(v_inst_7251_, 0);
    v_toBind_7257_ = crate::leanh::lean_ctor_get(v_inst_7251_, 1);
    crate::leanh::lean_inc(v_toBind_7257_);
    v_toPure_7258_ = crate::leanh::lean_ctor_get(v_toApplicative_7256_, 1);
    crate::leanh::lean_inc(v_toPure_7258_);
    v___f_7259_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7259_, 0, v_f_7255_);
    v___x_7260_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_7251_,
        v___f_7259_,
        v_init_7254_,
        v_m_7253_,
    );
    v___f_7261_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7261_, 0, v_toPure_7258_);
    v___x_7262_ = crate::leanh::lean_apply_4(
        v_toBind_7257_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7260_,
        v___f_7261_,
    );
    return v___x_7262_;
}
pub unsafe fn l_Std_DTreeMap_instForInSigmaOfMonad___redArg(
    mut v_inst_7263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7264_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7264_, 0, v_inst_7263_);
    return v___f_7264_;
}
pub unsafe fn l_Std_DTreeMap_instForInSigmaOfMonad(
    mut v_00_u03b1_7265_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7266_: *mut crate::leanh::LeanObject,
    mut v_cmp_7267_: *mut crate::leanh::LeanObject,
    mut v_m_7268_: *mut crate::leanh::LeanObject,
    mut v_inst_7269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7270_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7270_, 0, v_inst_7269_);
    return v___f_7270_;
}
pub unsafe fn l_Std_DTreeMap_instForInSigmaOfMonad___boxed(
    mut v_00_u03b1_7271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7272_: *mut crate::leanh::LeanObject,
    mut v_cmp_7273_: *mut crate::leanh::LeanObject,
    mut v_m_7274_: *mut crate::leanh::LeanObject,
    mut v_inst_7275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7276_ = l_Std_DTreeMap_instForInSigmaOfMonad(
        v_00_u03b1_7271_,
        v_00_u03b2_7272_,
        v_cmp_7273_,
        v_m_7274_,
        v_inst_7275_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7273_);
    return v_res_7276_;
}
pub unsafe fn l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0(
    mut v_f_7277_: *mut crate::leanh::LeanObject,
    mut v_x_7278_: *mut crate::leanh::LeanObject,
    mut v_k_7279_: *mut crate::leanh::LeanObject,
    mut v_v_7280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7281_, 0, v_k_7279_);
    crate::leanh::lean_ctor_set(v___x_7281_, 1, v_v_7280_);
    v___x_7282_ = crate::leanh::lean_apply_1(v_f_7277_, v___x_7281_);
    return v___x_7282_;
}
pub unsafe fn l_Std_DTreeMap_Const_forMUncurried___redArg(
    mut v_inst_7283_: *mut crate::leanh::LeanObject,
    mut v_f_7284_: *mut crate::leanh::LeanObject,
    mut v_t_7285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7286_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7286_, 0, v_f_7284_);
    v___x_7287_ = crate::leanh::lean_box(0);
    v___x_7288_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_7283_,
        v___f_7286_,
        v___x_7287_,
        v_t_7285_,
    );
    return v___x_7288_;
}
pub unsafe fn l_Std_DTreeMap_Const_forMUncurried(
    mut v_00_u03b1_7289_: *mut crate::leanh::LeanObject,
    mut v_cmp_7290_: *mut crate::leanh::LeanObject,
    mut v_m_7291_: *mut crate::leanh::LeanObject,
    mut v_inst_7292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7293_: *mut crate::leanh::LeanObject,
    mut v_f_7294_: *mut crate::leanh::LeanObject,
    mut v_t_7295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7296_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7296_, 0, v_f_7294_);
    v___x_7297_ = crate::leanh::lean_box(0);
    v___x_7298_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_7292_,
        v___f_7296_,
        v___x_7297_,
        v_t_7295_,
    );
    return v___x_7298_;
}
pub unsafe fn l_Std_DTreeMap_Const_forMUncurried___boxed(
    mut v_00_u03b1_7299_: *mut crate::leanh::LeanObject,
    mut v_cmp_7300_: *mut crate::leanh::LeanObject,
    mut v_m_7301_: *mut crate::leanh::LeanObject,
    mut v_inst_7302_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7303_: *mut crate::leanh::LeanObject,
    mut v_f_7304_: *mut crate::leanh::LeanObject,
    mut v_t_7305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7306_ = l_Std_DTreeMap_Const_forMUncurried(
        v_00_u03b1_7299_,
        v_cmp_7300_,
        v_m_7301_,
        v_inst_7302_,
        v_00_u03b2_7303_,
        v_f_7304_,
        v_t_7305_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7300_);
    return v_res_7306_;
}
pub unsafe fn l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0(
    mut v_f_7307_: *mut crate::leanh::LeanObject,
    mut v_a_7308_: *mut crate::leanh::LeanObject,
    mut v_b_7309_: *mut crate::leanh::LeanObject,
    mut v_acc_7310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7311_, 0, v_a_7308_);
    crate::leanh::lean_ctor_set(v___x_7311_, 1, v_b_7309_);
    v___x_7312_ = crate::leanh::lean_apply_2(v_f_7307_, v___x_7311_, v_acc_7310_);
    return v___x_7312_;
}
pub unsafe fn l_Std_DTreeMap_Const_forInUncurried___redArg(
    mut v_inst_7313_: *mut crate::leanh::LeanObject,
    mut v_f_7314_: *mut crate::leanh::LeanObject,
    mut v_init_7315_: *mut crate::leanh::LeanObject,
    mut v_t_7316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7317_ = crate::leanh::lean_ctor_get(v_inst_7313_, 0);
    v_toBind_7318_ = crate::leanh::lean_ctor_get(v_inst_7313_, 1);
    crate::leanh::lean_inc(v_toBind_7318_);
    v_toPure_7319_ = crate::leanh::lean_ctor_get(v_toApplicative_7317_, 1);
    crate::leanh::lean_inc(v_toPure_7319_);
    v___f_7320_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7320_, 0, v_f_7314_);
    v___x_7321_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_7313_,
        v___f_7320_,
        v_init_7315_,
        v_t_7316_,
    );
    v___f_7322_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7322_, 0, v_toPure_7319_);
    v___x_7323_ = crate::leanh::lean_apply_4(
        v_toBind_7318_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7321_,
        v___f_7322_,
    );
    return v___x_7323_;
}
pub unsafe fn l_Std_DTreeMap_Const_forInUncurried(
    mut v_00_u03b1_7324_: *mut crate::leanh::LeanObject,
    mut v_cmp_7325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7326_: *mut crate::leanh::LeanObject,
    mut v_m_7327_: *mut crate::leanh::LeanObject,
    mut v_inst_7328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7329_: *mut crate::leanh::LeanObject,
    mut v_f_7330_: *mut crate::leanh::LeanObject,
    mut v_init_7331_: *mut crate::leanh::LeanObject,
    mut v_t_7332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7333_ = crate::leanh::lean_ctor_get(v_inst_7328_, 0);
    v_toBind_7334_ = crate::leanh::lean_ctor_get(v_inst_7328_, 1);
    crate::leanh::lean_inc(v_toBind_7334_);
    v_toPure_7335_ = crate::leanh::lean_ctor_get(v_toApplicative_7333_, 1);
    crate::leanh::lean_inc(v_toPure_7335_);
    v___f_7336_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7336_, 0, v_f_7330_);
    v___x_7337_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_7328_,
        v___f_7336_,
        v_init_7331_,
        v_t_7332_,
    );
    v___f_7338_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7338_, 0, v_toPure_7335_);
    v___x_7339_ = crate::leanh::lean_apply_4(
        v_toBind_7334_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7337_,
        v___f_7338_,
    );
    return v___x_7339_;
}
pub unsafe fn l_Std_DTreeMap_Const_forInUncurried___boxed(
    mut v_00_u03b1_7340_: *mut crate::leanh::LeanObject,
    mut v_cmp_7341_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_7342_: *mut crate::leanh::LeanObject,
    mut v_m_7343_: *mut crate::leanh::LeanObject,
    mut v_inst_7344_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7345_: *mut crate::leanh::LeanObject,
    mut v_f_7346_: *mut crate::leanh::LeanObject,
    mut v_init_7347_: *mut crate::leanh::LeanObject,
    mut v_t_7348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7349_ = l_Std_DTreeMap_Const_forInUncurried(
        v_00_u03b1_7340_,
        v_cmp_7341_,
        v_00_u03b4_7342_,
        v_m_7343_,
        v_inst_7344_,
        v_00_u03b2_7345_,
        v_f_7346_,
        v_init_7347_,
        v_t_7348_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7341_);
    return v_res_7349_;
}
pub unsafe fn l_Std_DTreeMap_any___redArg___lam__0(
    mut v_p_7350_: *mut crate::leanh::LeanObject,
    mut v___x_7351_: *mut crate::leanh::LeanObject,
    mut v___x_7352_: *mut crate::leanh::LeanObject,
    mut v_a_7353_: *mut crate::leanh::LeanObject,
    mut v_b_7354_: *mut crate::leanh::LeanObject,
    mut v_acc_7355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: u8 = 0;
    v___x_7356_ = crate::leanh::lean_apply_2(v_p_7350_, v_a_7353_, v_b_7354_);
    v___x_7357_ = (crate::leanh::lean_unbox(v___x_7356_) as u8);
    if v___x_7357_ == 0 {
        let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7358_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7358_, 0, v___x_7351_);
        return v___x_7358_;
    } else {
        let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_7351_);
        v___x_7359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7359_, 0, v___x_7356_);
        v___x_7360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7360_, 0, v___x_7359_);
        crate::leanh::lean_ctor_set(v___x_7360_, 1, v___x_7352_);
        v___x_7361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7361_, 0, v___x_7360_);
        return v___x_7361_;
    }
}
pub unsafe fn l_Std_DTreeMap_any___redArg___lam__0___boxed(
    mut v_p_7362_: *mut crate::leanh::LeanObject,
    mut v___x_7363_: *mut crate::leanh::LeanObject,
    mut v___x_7364_: *mut crate::leanh::LeanObject,
    mut v_a_7365_: *mut crate::leanh::LeanObject,
    mut v_b_7366_: *mut crate::leanh::LeanObject,
    mut v_acc_7367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7368_ = l_Std_DTreeMap_any___redArg___lam__0(
        v_p_7362_,
        v___x_7363_,
        v___x_7364_,
        v_a_7365_,
        v_b_7366_,
        v_acc_7367_,
    );
    crate::leanh::lean_dec_ref(v_acc_7367_);
    return v_res_7368_;
}
pub unsafe fn l_Std_DTreeMap_any___redArg(
    mut v_t_7372_: *mut crate::leanh::LeanObject,
    mut v_p_7373_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: u8 = 0;
    let mut v_val_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: u8 = 0;
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7380_ = l_Std_DTreeMap_foldr___redArg___closed__9;
                v___x_7381_ = crate::leanh::lean_box(0);
                v___x_7382_ = l_Std_DTreeMap_any___redArg___closed__0;
                v___f_7383_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7383_, 0, v_p_7373_);
                crate::leanh::lean_closure_set(v___f_7383_, 1, v___x_7382_);
                crate::leanh::lean_closure_set(v___f_7383_, 2, v___x_7381_);
                v___x_7384_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_7380_,
                    v___f_7383_,
                    v___x_7382_,
                    v_t_7372_,
                );
                v_a_7385_ = crate::leanh::lean_ctor_get(v___x_7384_, 0);
                crate::leanh::lean_inc(v_a_7385_);
                crate::leanh::lean_dec(v___x_7384_);
                v___y_7375_ = v_a_7385_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_7376_ = crate::leanh::lean_ctor_get(v___y_7375_, 0);
                crate::leanh::lean_inc(v_fst_7376_);
                crate::leanh::lean_dec_ref(v___y_7375_);
                if crate::leanh::lean_obj_tag(v_fst_7376_) == 0 {
                    v___x_7377_ = 0;
                    return v___x_7377_;
                } else {
                    v_val_7378_ = crate::leanh::lean_ctor_get(v_fst_7376_, 0);
                    crate::leanh::lean_inc(v_val_7378_);
                    crate::leanh::lean_dec_ref_known(v_fst_7376_, 1);
                    v___x_7379_ = (crate::leanh::lean_unbox(v_val_7378_) as u8);
                    crate::leanh::lean_dec(v_val_7378_);
                    return v___x_7379_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_any___redArg___boxed(
    mut v_t_7386_: *mut crate::leanh::LeanObject,
    mut v_p_7387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7388_: u8 = 0;
    let mut v_r_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7388_ = l_Std_DTreeMap_any___redArg(v_t_7386_, v_p_7387_);
    v_r_7389_ = crate::leanh::lean_box((v_res_7388_) as usize);
    return v_r_7389_;
}
pub unsafe fn l_Std_DTreeMap_any(
    mut v_00_u03b1_7390_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7391_: *mut crate::leanh::LeanObject,
    mut v_cmp_7392_: *mut crate::leanh::LeanObject,
    mut v_t_7393_: *mut crate::leanh::LeanObject,
    mut v_p_7394_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: u8 = 0;
    let mut v_val_7399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: u8 = 0;
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7401_ = l_Std_DTreeMap_foldr___redArg___closed__9;
                v___x_7402_ = crate::leanh::lean_box(0);
                v___x_7403_ = l_Std_DTreeMap_any___redArg___closed__0;
                v___f_7404_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7404_, 0, v_p_7394_);
                crate::leanh::lean_closure_set(v___f_7404_, 1, v___x_7403_);
                crate::leanh::lean_closure_set(v___f_7404_, 2, v___x_7402_);
                v___x_7405_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_7401_,
                    v___f_7404_,
                    v___x_7403_,
                    v_t_7393_,
                );
                v_a_7406_ = crate::leanh::lean_ctor_get(v___x_7405_, 0);
                crate::leanh::lean_inc(v_a_7406_);
                crate::leanh::lean_dec(v___x_7405_);
                v___y_7396_ = v_a_7406_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_7397_ = crate::leanh::lean_ctor_get(v___y_7396_, 0);
                crate::leanh::lean_inc(v_fst_7397_);
                crate::leanh::lean_dec_ref(v___y_7396_);
                if crate::leanh::lean_obj_tag(v_fst_7397_) == 0 {
                    v___x_7398_ = 0;
                    return v___x_7398_;
                } else {
                    v_val_7399_ = crate::leanh::lean_ctor_get(v_fst_7397_, 0);
                    crate::leanh::lean_inc(v_val_7399_);
                    crate::leanh::lean_dec_ref_known(v_fst_7397_, 1);
                    v___x_7400_ = (crate::leanh::lean_unbox(v_val_7399_) as u8);
                    crate::leanh::lean_dec(v_val_7399_);
                    return v___x_7400_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_any___boxed(
    mut v_00_u03b1_7407_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7408_: *mut crate::leanh::LeanObject,
    mut v_cmp_7409_: *mut crate::leanh::LeanObject,
    mut v_t_7410_: *mut crate::leanh::LeanObject,
    mut v_p_7411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7412_: u8 = 0;
    let mut v_r_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7412_ = l_Std_DTreeMap_any(
        v_00_u03b1_7407_,
        v_00_u03b2_7408_,
        v_cmp_7409_,
        v_t_7410_,
        v_p_7411_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7409_);
    v_r_7413_ = crate::leanh::lean_box((v_res_7412_) as usize);
    return v_r_7413_;
}
pub unsafe fn l_Std_DTreeMap_all___redArg___lam__0(
    mut v_p_7414_: *mut crate::leanh::LeanObject,
    mut v___x_7415_: *mut crate::leanh::LeanObject,
    mut v___x_7416_: *mut crate::leanh::LeanObject,
    mut v_a_7417_: *mut crate::leanh::LeanObject,
    mut v_b_7418_: *mut crate::leanh::LeanObject,
    mut v_acc_7419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7421_: u8 = 0;
    v___x_7420_ = crate::leanh::lean_apply_2(v_p_7414_, v_a_7417_, v_b_7418_);
    v___x_7421_ = (crate::leanh::lean_unbox(v___x_7420_) as u8);
    if v___x_7421_ == 0 {
        let mut v___x_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_7416_);
        v___x_7422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7422_, 0, v___x_7420_);
        v___x_7423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7423_, 0, v___x_7422_);
        crate::leanh::lean_ctor_set(v___x_7423_, 1, v___x_7415_);
        v___x_7424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7424_, 0, v___x_7423_);
        return v___x_7424_;
    } else {
        let mut v___x_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7425_, 0, v___x_7416_);
        return v___x_7425_;
    }
}
pub unsafe fn l_Std_DTreeMap_all___redArg___lam__0___boxed(
    mut v_p_7426_: *mut crate::leanh::LeanObject,
    mut v___x_7427_: *mut crate::leanh::LeanObject,
    mut v___x_7428_: *mut crate::leanh::LeanObject,
    mut v_a_7429_: *mut crate::leanh::LeanObject,
    mut v_b_7430_: *mut crate::leanh::LeanObject,
    mut v_acc_7431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7432_ = l_Std_DTreeMap_all___redArg___lam__0(
        v_p_7426_,
        v___x_7427_,
        v___x_7428_,
        v_a_7429_,
        v_b_7430_,
        v_acc_7431_,
    );
    crate::leanh::lean_dec_ref(v_acc_7431_);
    return v_res_7432_;
}
pub unsafe fn l_Std_DTreeMap_all___redArg(
    mut v_t_7433_: *mut crate::leanh::LeanObject,
    mut v_p_7434_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: u8 = 0;
    let mut v_val_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7440_: u8 = 0;
    let mut v___x_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7441_ = l_Std_DTreeMap_foldr___redArg___closed__9;
                v___x_7442_ = crate::leanh::lean_box(0);
                v___x_7443_ = l_Std_DTreeMap_any___redArg___closed__0;
                v___f_7444_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7444_, 0, v_p_7434_);
                crate::leanh::lean_closure_set(v___f_7444_, 1, v___x_7442_);
                crate::leanh::lean_closure_set(v___f_7444_, 2, v___x_7443_);
                v___x_7445_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_7441_,
                    v___f_7444_,
                    v___x_7443_,
                    v_t_7433_,
                );
                v_a_7446_ = crate::leanh::lean_ctor_get(v___x_7445_, 0);
                crate::leanh::lean_inc(v_a_7446_);
                crate::leanh::lean_dec(v___x_7445_);
                v___y_7436_ = v_a_7446_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_7437_ = crate::leanh::lean_ctor_get(v___y_7436_, 0);
                crate::leanh::lean_inc(v_fst_7437_);
                crate::leanh::lean_dec_ref(v___y_7436_);
                if crate::leanh::lean_obj_tag(v_fst_7437_) == 0 {
                    v___x_7438_ = 1;
                    return v___x_7438_;
                } else {
                    v_val_7439_ = crate::leanh::lean_ctor_get(v_fst_7437_, 0);
                    crate::leanh::lean_inc(v_val_7439_);
                    crate::leanh::lean_dec_ref_known(v_fst_7437_, 1);
                    v___x_7440_ = (crate::leanh::lean_unbox(v_val_7439_) as u8);
                    crate::leanh::lean_dec(v_val_7439_);
                    return v___x_7440_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_all___redArg___boxed(
    mut v_t_7447_: *mut crate::leanh::LeanObject,
    mut v_p_7448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7449_: u8 = 0;
    let mut v_r_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7449_ = l_Std_DTreeMap_all___redArg(v_t_7447_, v_p_7448_);
    v_r_7450_ = crate::leanh::lean_box((v_res_7449_) as usize);
    return v_r_7450_;
}
pub unsafe fn l_Std_DTreeMap_all(
    mut v_00_u03b1_7451_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7452_: *mut crate::leanh::LeanObject,
    mut v_cmp_7453_: *mut crate::leanh::LeanObject,
    mut v_t_7454_: *mut crate::leanh::LeanObject,
    mut v_p_7455_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: u8 = 0;
    let mut v_val_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7461_: u8 = 0;
    let mut v___x_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7462_ = l_Std_DTreeMap_foldr___redArg___closed__9;
                v___x_7463_ = crate::leanh::lean_box(0);
                v___x_7464_ = l_Std_DTreeMap_any___redArg___closed__0;
                v___f_7465_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7465_, 0, v_p_7455_);
                crate::leanh::lean_closure_set(v___f_7465_, 1, v___x_7463_);
                crate::leanh::lean_closure_set(v___f_7465_, 2, v___x_7464_);
                v___x_7466_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_7462_,
                    v___f_7465_,
                    v___x_7464_,
                    v_t_7454_,
                );
                v_a_7467_ = crate::leanh::lean_ctor_get(v___x_7466_, 0);
                crate::leanh::lean_inc(v_a_7467_);
                crate::leanh::lean_dec(v___x_7466_);
                v___y_7457_ = v_a_7467_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_7458_ = crate::leanh::lean_ctor_get(v___y_7457_, 0);
                crate::leanh::lean_inc(v_fst_7458_);
                crate::leanh::lean_dec_ref(v___y_7457_);
                if crate::leanh::lean_obj_tag(v_fst_7458_) == 0 {
                    v___x_7459_ = 1;
                    return v___x_7459_;
                } else {
                    v_val_7460_ = crate::leanh::lean_ctor_get(v_fst_7458_, 0);
                    crate::leanh::lean_inc(v_val_7460_);
                    crate::leanh::lean_dec_ref_known(v_fst_7458_, 1);
                    v___x_7461_ = (crate::leanh::lean_unbox(v_val_7460_) as u8);
                    crate::leanh::lean_dec(v_val_7460_);
                    return v___x_7461_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_all___boxed(
    mut v_00_u03b1_7468_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7469_: *mut crate::leanh::LeanObject,
    mut v_cmp_7470_: *mut crate::leanh::LeanObject,
    mut v_t_7471_: *mut crate::leanh::LeanObject,
    mut v_p_7472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7473_: u8 = 0;
    let mut v_r_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7473_ = l_Std_DTreeMap_all(
        v_00_u03b1_7468_,
        v_00_u03b2_7469_,
        v_cmp_7470_,
        v_t_7471_,
        v_p_7472_,
    );
    crate::leanh::lean_dec_ref(v_cmp_7470_);
    v_r_7474_ = crate::leanh::lean_box((v_res_7473_) as usize);
    return v_r_7474_;
}
pub unsafe fn l_Std_DTreeMap_keys___redArg___lam__0(
    mut v_x1_7475_: *mut crate::leanh::LeanObject,
    mut v_x2_7476_: *mut crate::leanh::LeanObject,
    mut v_x3_7477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7478_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7478_, 0, v_x1_7475_);
    crate::leanh::lean_ctor_set(v___x_7478_, 1, v_x3_7477_);
    return v___x_7478_;
}
pub unsafe fn l_Std_DTreeMap_keys___redArg___lam__0___boxed(
    mut v_x1_7479_: *mut crate::leanh::LeanObject,
    mut v_x2_7480_: *mut crate::leanh::LeanObject,
    mut v_x3_7481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7482_ = l_Std_DTreeMap_keys___redArg___lam__0(v_x1_7479_, v_x2_7480_, v_x3_7481_);
    crate::leanh::lean_dec(v_x2_7480_);
    return v_res_7482_;
}
pub unsafe fn l_Std_DTreeMap_keys___redArg(
    mut v_t_7484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7485_ = l_Std_DTreeMap_keys___redArg___closed__0;
    v___x_7486_ = crate::leanh::lean_box(0);
    v___x_7487_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7488_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7487_,
        v___f_7485_,
        v___x_7486_,
        v_t_7484_,
    );
    return v___x_7488_;
}
pub unsafe fn l_Std_DTreeMap_keys(
    mut v_00_u03b1_7489_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7490_: *mut crate::leanh::LeanObject,
    mut v_cmp_7491_: *mut crate::leanh::LeanObject,
    mut v_t_7492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7493_ = l_Std_DTreeMap_keys___redArg___closed__0;
    v___x_7494_ = crate::leanh::lean_box(0);
    v___x_7495_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7496_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7495_,
        v___f_7493_,
        v___x_7494_,
        v_t_7492_,
    );
    return v___x_7496_;
}
pub unsafe fn l_Std_DTreeMap_keys___boxed(
    mut v_00_u03b1_7497_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7498_: *mut crate::leanh::LeanObject,
    mut v_cmp_7499_: *mut crate::leanh::LeanObject,
    mut v_t_7500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7501_ = l_Std_DTreeMap_keys(v_00_u03b1_7497_, v_00_u03b2_7498_, v_cmp_7499_, v_t_7500_);
    crate::leanh::lean_dec_ref(v_cmp_7499_);
    return v_res_7501_;
}
pub unsafe fn l_Std_DTreeMap_keysArray___redArg___lam__0(
    mut v_l_7502_: *mut crate::leanh::LeanObject,
    mut v_k_7503_: *mut crate::leanh::LeanObject,
    mut v_x_7504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7505_ = lean_array_push(v_l_7502_, v_k_7503_);
    return v___x_7505_;
}
pub unsafe fn l_Std_DTreeMap_keysArray___redArg___lam__0___boxed(
    mut v_l_7506_: *mut crate::leanh::LeanObject,
    mut v_k_7507_: *mut crate::leanh::LeanObject,
    mut v_x_7508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7509_ = l_Std_DTreeMap_keysArray___redArg___lam__0(v_l_7506_, v_k_7507_, v_x_7508_);
    crate::leanh::lean_dec(v_x_7508_);
    return v_res_7509_;
}
pub unsafe fn l_Std_DTreeMap_keysArray___redArg(
    mut v_t_7511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7512_ = l_Std_DTreeMap_keysArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_7511_) == 0 {
                    v_size_7517_ = crate::leanh::lean_ctor_get(v_t_7511_, 0);
                    crate::leanh::lean_inc(v_size_7517_);
                    v___y_7514_ = v_size_7517_;
                    state = 1;
                    continue;
                } else {
                    v___x_7518_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7514_ = v___x_7518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7515_ = lean_mk_empty_array_with_capacity(v___y_7514_);
                crate::leanh::lean_dec(v___y_7514_);
                v___x_7516_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7512_,
                    v___x_7515_,
                    v_t_7511_,
                );
                return v___x_7516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_keysArray(
    mut v_00_u03b1_7519_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7520_: *mut crate::leanh::LeanObject,
    mut v_cmp_7521_: *mut crate::leanh::LeanObject,
    mut v_t_7522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7523_ = l_Std_DTreeMap_keysArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_7522_) == 0 {
                    v_size_7528_ = crate::leanh::lean_ctor_get(v_t_7522_, 0);
                    crate::leanh::lean_inc(v_size_7528_);
                    v___y_7525_ = v_size_7528_;
                    state = 1;
                    continue;
                } else {
                    v___x_7529_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7525_ = v___x_7529_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7526_ = lean_mk_empty_array_with_capacity(v___y_7525_);
                crate::leanh::lean_dec(v___y_7525_);
                v___x_7527_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7523_,
                    v___x_7526_,
                    v_t_7522_,
                );
                return v___x_7527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_keysArray___boxed(
    mut v_00_u03b1_7530_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7531_: *mut crate::leanh::LeanObject,
    mut v_cmp_7532_: *mut crate::leanh::LeanObject,
    mut v_t_7533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7534_ =
        l_Std_DTreeMap_keysArray(v_00_u03b1_7530_, v_00_u03b2_7531_, v_cmp_7532_, v_t_7533_);
    crate::leanh::lean_dec_ref(v_cmp_7532_);
    return v_res_7534_;
}
pub unsafe fn l_Std_DTreeMap_values___redArg___lam__0(
    mut v_x1_7535_: *mut crate::leanh::LeanObject,
    mut v_x2_7536_: *mut crate::leanh::LeanObject,
    mut v_x3_7537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7538_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7538_, 0, v_x2_7536_);
    crate::leanh::lean_ctor_set(v___x_7538_, 1, v_x3_7537_);
    return v___x_7538_;
}
pub unsafe fn l_Std_DTreeMap_values___redArg___lam__0___boxed(
    mut v_x1_7539_: *mut crate::leanh::LeanObject,
    mut v_x2_7540_: *mut crate::leanh::LeanObject,
    mut v_x3_7541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7542_ = l_Std_DTreeMap_values___redArg___lam__0(v_x1_7539_, v_x2_7540_, v_x3_7541_);
    crate::leanh::lean_dec(v_x1_7539_);
    return v_res_7542_;
}
pub unsafe fn l_Std_DTreeMap_values___redArg(
    mut v_t_7544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7545_ = l_Std_DTreeMap_values___redArg___closed__0;
    v___x_7546_ = crate::leanh::lean_box(0);
    v___x_7547_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7548_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7547_,
        v___f_7545_,
        v___x_7546_,
        v_t_7544_,
    );
    return v___x_7548_;
}
pub unsafe fn l_Std_DTreeMap_values(
    mut v_00_u03b1_7549_: *mut crate::leanh::LeanObject,
    mut v_cmp_7550_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7551_: *mut crate::leanh::LeanObject,
    mut v_t_7552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7553_ = l_Std_DTreeMap_values___redArg___closed__0;
    v___x_7554_ = crate::leanh::lean_box(0);
    v___x_7555_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7556_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7555_,
        v___f_7553_,
        v___x_7554_,
        v_t_7552_,
    );
    return v___x_7556_;
}
pub unsafe fn l_Std_DTreeMap_values___boxed(
    mut v_00_u03b1_7557_: *mut crate::leanh::LeanObject,
    mut v_cmp_7558_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7559_: *mut crate::leanh::LeanObject,
    mut v_t_7560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7561_ = l_Std_DTreeMap_values(v_00_u03b1_7557_, v_cmp_7558_, v_00_u03b2_7559_, v_t_7560_);
    crate::leanh::lean_dec_ref(v_cmp_7558_);
    return v_res_7561_;
}
pub unsafe fn l_Std_DTreeMap_valuesArray___redArg___lam__0(
    mut v_l_7562_: *mut crate::leanh::LeanObject,
    mut v_x_7563_: *mut crate::leanh::LeanObject,
    mut v_v_7564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7565_ = lean_array_push(v_l_7562_, v_v_7564_);
    return v___x_7565_;
}
pub unsafe fn l_Std_DTreeMap_valuesArray___redArg___lam__0___boxed(
    mut v_l_7566_: *mut crate::leanh::LeanObject,
    mut v_x_7567_: *mut crate::leanh::LeanObject,
    mut v_v_7568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7569_ = l_Std_DTreeMap_valuesArray___redArg___lam__0(v_l_7566_, v_x_7567_, v_v_7568_);
    crate::leanh::lean_dec(v_x_7567_);
    return v_res_7569_;
}
pub unsafe fn l_Std_DTreeMap_valuesArray___redArg(
    mut v_t_7571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7572_ = l_Std_DTreeMap_valuesArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_7571_) == 0 {
                    v_size_7577_ = crate::leanh::lean_ctor_get(v_t_7571_, 0);
                    crate::leanh::lean_inc(v_size_7577_);
                    v___y_7574_ = v_size_7577_;
                    state = 1;
                    continue;
                } else {
                    v___x_7578_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7574_ = v___x_7578_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7575_ = lean_mk_empty_array_with_capacity(v___y_7574_);
                crate::leanh::lean_dec(v___y_7574_);
                v___x_7576_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7572_,
                    v___x_7575_,
                    v_t_7571_,
                );
                return v___x_7576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_valuesArray(
    mut v_00_u03b1_7579_: *mut crate::leanh::LeanObject,
    mut v_cmp_7580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7581_: *mut crate::leanh::LeanObject,
    mut v_t_7582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7583_ = l_Std_DTreeMap_valuesArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_7582_) == 0 {
                    v_size_7588_ = crate::leanh::lean_ctor_get(v_t_7582_, 0);
                    crate::leanh::lean_inc(v_size_7588_);
                    v___y_7585_ = v_size_7588_;
                    state = 1;
                    continue;
                } else {
                    v___x_7589_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7585_ = v___x_7589_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7586_ = lean_mk_empty_array_with_capacity(v___y_7585_);
                crate::leanh::lean_dec(v___y_7585_);
                v___x_7587_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7583_,
                    v___x_7586_,
                    v_t_7582_,
                );
                return v___x_7587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_valuesArray___boxed(
    mut v_00_u03b1_7590_: *mut crate::leanh::LeanObject,
    mut v_cmp_7591_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7592_: *mut crate::leanh::LeanObject,
    mut v_t_7593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7594_ =
        l_Std_DTreeMap_valuesArray(v_00_u03b1_7590_, v_cmp_7591_, v_00_u03b2_7592_, v_t_7593_);
    crate::leanh::lean_dec_ref(v_cmp_7591_);
    return v_res_7594_;
}
pub unsafe fn l_Std_DTreeMap_toList___redArg___lam__0(
    mut v_x1_7595_: *mut crate::leanh::LeanObject,
    mut v_x2_7596_: *mut crate::leanh::LeanObject,
    mut v_x3_7597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7598_, 0, v_x1_7595_);
    crate::leanh::lean_ctor_set(v___x_7598_, 1, v_x2_7596_);
    v___x_7599_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7599_, 0, v___x_7598_);
    crate::leanh::lean_ctor_set(v___x_7599_, 1, v_x3_7597_);
    return v___x_7599_;
}
pub unsafe fn l_Std_DTreeMap_toList___redArg(
    mut v_t_7601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7602_ = l_Std_DTreeMap_toList___redArg___closed__0;
    v___x_7603_ = crate::leanh::lean_box(0);
    v___x_7604_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7605_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7604_,
        v___f_7602_,
        v___x_7603_,
        v_t_7601_,
    );
    return v___x_7605_;
}
pub unsafe fn l_Std_DTreeMap_toList(
    mut v_00_u03b1_7606_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7607_: *mut crate::leanh::LeanObject,
    mut v_cmp_7608_: *mut crate::leanh::LeanObject,
    mut v_t_7609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7610_ = l_Std_DTreeMap_toList___redArg___closed__0;
    v___x_7611_ = crate::leanh::lean_box(0);
    v___x_7612_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7613_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7612_,
        v___f_7610_,
        v___x_7611_,
        v_t_7609_,
    );
    return v___x_7613_;
}
pub unsafe fn l_Std_DTreeMap_toList___boxed(
    mut v_00_u03b1_7614_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7615_: *mut crate::leanh::LeanObject,
    mut v_cmp_7616_: *mut crate::leanh::LeanObject,
    mut v_t_7617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7618_ = l_Std_DTreeMap_toList(v_00_u03b1_7614_, v_00_u03b2_7615_, v_cmp_7616_, v_t_7617_);
    crate::leanh::lean_dec_ref(v_cmp_7616_);
    return v_res_7618_;
}
pub unsafe fn _init_l_Std_DTreeMap_ofList___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7619_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26_once),
        _init_l_Std_DTreeMap___auto__1___closed__26,
    );
    return v___x_7619_;
}
pub unsafe fn l_Std_DTreeMap_ofList___redArg___lam__0(
    mut v_cmp_7620_: *mut crate::leanh::LeanObject,
    mut v_a_7621_: *mut crate::leanh::LeanObject,
    mut v_x_7622_: *mut crate::leanh::LeanObject,
    mut v___y_7623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_7624_ = crate::leanh::lean_ctor_get(v_a_7621_, 0);
    crate::leanh::lean_inc(v_fst_7624_);
    v_snd_7625_ = crate::leanh::lean_ctor_get(v_a_7621_, 1);
    crate::leanh::lean_inc(v_snd_7625_);
    crate::leanh::lean_dec_ref(v_a_7621_);
    v_r_7626_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_7620_,
        v_fst_7624_,
        v_snd_7625_,
        v___y_7623_,
    );
    v___x_7627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7627_, 0, v_r_7626_);
    return v___x_7627_;
}
pub unsafe fn l_Std_DTreeMap_ofList___redArg(
    mut v_l_7628_: *mut crate::leanh::LeanObject,
    mut v_cmp_7629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7630_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7630_, 0, v_cmp_7629_);
    v___x_7631_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7632_ = crate::leanh::lean_box(1);
    v___x_7633_ = l_List_forIn_x27_loop___redArg(v___x_7631_, v___f_7630_, v_l_7628_, v_r_7632_);
    return v___x_7633_;
}
pub unsafe fn l_Std_DTreeMap_ofList___redArg___boxed(
    mut v_l_7634_: *mut crate::leanh::LeanObject,
    mut v_cmp_7635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7636_ = l_Std_DTreeMap_ofList___redArg(v_l_7634_, v_cmp_7635_);
    crate::leanh::lean_dec(v_l_7634_);
    return v_res_7636_;
}
pub unsafe fn l_Std_DTreeMap_ofList(
    mut v_00_u03b1_7637_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7638_: *mut crate::leanh::LeanObject,
    mut v_l_7639_: *mut crate::leanh::LeanObject,
    mut v_cmp_7640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7641_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7641_, 0, v_cmp_7640_);
    v___x_7642_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7643_ = crate::leanh::lean_box(1);
    v___x_7644_ = l_List_forIn_x27_loop___redArg(v___x_7642_, v___f_7641_, v_l_7639_, v_r_7643_);
    return v___x_7644_;
}
pub unsafe fn l_Std_DTreeMap_ofList___boxed(
    mut v_00_u03b1_7645_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7646_: *mut crate::leanh::LeanObject,
    mut v_l_7647_: *mut crate::leanh::LeanObject,
    mut v_cmp_7648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7649_ = l_Std_DTreeMap_ofList(v_00_u03b1_7645_, v_00_u03b2_7646_, v_l_7647_, v_cmp_7648_);
    crate::leanh::lean_dec(v_l_7647_);
    return v_res_7649_;
}
pub unsafe fn l_Std_DTreeMap_toArray___redArg___lam__0(
    mut v_l_7650_: *mut crate::leanh::LeanObject,
    mut v_k_7651_: *mut crate::leanh::LeanObject,
    mut v_v_7652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7653_, 0, v_k_7651_);
    crate::leanh::lean_ctor_set(v___x_7653_, 1, v_v_7652_);
    v___x_7654_ = lean_array_push(v_l_7650_, v___x_7653_);
    return v___x_7654_;
}
pub unsafe fn l_Std_DTreeMap_toArray___redArg(
    mut v_t_7656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7657_ = l_Std_DTreeMap_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_7656_) == 0 {
                    v_size_7662_ = crate::leanh::lean_ctor_get(v_t_7656_, 0);
                    crate::leanh::lean_inc(v_size_7662_);
                    v___y_7659_ = v_size_7662_;
                    state = 1;
                    continue;
                } else {
                    v___x_7663_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7659_ = v___x_7663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7660_ = lean_mk_empty_array_with_capacity(v___y_7659_);
                crate::leanh::lean_dec(v___y_7659_);
                v___x_7661_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7657_,
                    v___x_7660_,
                    v_t_7656_,
                );
                return v___x_7661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_toArray(
    mut v_00_u03b1_7664_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7665_: *mut crate::leanh::LeanObject,
    mut v_cmp_7666_: *mut crate::leanh::LeanObject,
    mut v_t_7667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7668_ = l_Std_DTreeMap_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_7667_) == 0 {
                    v_size_7673_ = crate::leanh::lean_ctor_get(v_t_7667_, 0);
                    crate::leanh::lean_inc(v_size_7673_);
                    v___y_7670_ = v_size_7673_;
                    state = 1;
                    continue;
                } else {
                    v___x_7674_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7670_ = v___x_7674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7671_ = lean_mk_empty_array_with_capacity(v___y_7670_);
                crate::leanh::lean_dec(v___y_7670_);
                v___x_7672_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_7668_,
                    v___x_7671_,
                    v_t_7667_,
                );
                return v___x_7672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_toArray___boxed(
    mut v_00_u03b1_7675_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7676_: *mut crate::leanh::LeanObject,
    mut v_cmp_7677_: *mut crate::leanh::LeanObject,
    mut v_t_7678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7679_ =
        l_Std_DTreeMap_toArray(v_00_u03b1_7675_, v_00_u03b2_7676_, v_cmp_7677_, v_t_7678_);
    crate::leanh::lean_dec_ref(v_cmp_7677_);
    return v_res_7679_;
}
pub unsafe fn _init_l_Std_DTreeMap_ofArray___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26_once),
        _init_l_Std_DTreeMap___auto__1___closed__26,
    );
    return v___x_7680_;
}
pub unsafe fn l_Std_DTreeMap_ofArray___redArg(
    mut v_a_7681_: *mut crate::leanh::LeanObject,
    mut v_cmp_7682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7686_: usize = 0;
    let mut v___x_7687_: usize = 0;
    let mut v___x_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7683_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7683_, 0, v_cmp_7682_);
    v___x_7684_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7685_ = crate::leanh::lean_box(1);
    v_sz_7686_ = lean_array_size(v_a_7681_);
    v___x_7687_ = 0usize;
    v___x_7688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7684_,
        v_a_7681_,
        v___f_7683_,
        v_sz_7686_,
        v___x_7687_,
        v_r_7685_,
    );
    return v___x_7688_;
}
pub unsafe fn l_Std_DTreeMap_ofArray(
    mut v_00_u03b1_7689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7690_: *mut crate::leanh::LeanObject,
    mut v_a_7691_: *mut crate::leanh::LeanObject,
    mut v_cmp_7692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7696_: usize = 0;
    let mut v___x_7697_: usize = 0;
    let mut v___x_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7693_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7693_, 0, v_cmp_7692_);
    v___x_7694_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7695_ = crate::leanh::lean_box(1);
    v_sz_7696_ = lean_array_size(v_a_7691_);
    v___x_7697_ = 0usize;
    v___x_7698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7694_,
        v_a_7691_,
        v___f_7693_,
        v_sz_7696_,
        v___x_7697_,
        v_r_7695_,
    );
    return v___x_7698_;
}
pub unsafe fn l_Std_DTreeMap_modify___redArg(
    mut v_cmp_7699_: *mut crate::leanh::LeanObject,
    mut v_t_7700_: *mut crate::leanh::LeanObject,
    mut v_a_7701_: *mut crate::leanh::LeanObject,
    mut v_f_7702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7703_ =
        l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_7699_, v_a_7701_, v_f_7702_, v_t_7700_);
    return v___x_7703_;
}
pub unsafe fn l_Std_DTreeMap_modify(
    mut v_00_u03b1_7704_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7705_: *mut crate::leanh::LeanObject,
    mut v_cmp_7706_: *mut crate::leanh::LeanObject,
    mut v_inst_7707_: *mut crate::leanh::LeanObject,
    mut v_t_7708_: *mut crate::leanh::LeanObject,
    mut v_a_7709_: *mut crate::leanh::LeanObject,
    mut v_f_7710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7711_ =
        l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_7706_, v_a_7709_, v_f_7710_, v_t_7708_);
    return v___x_7711_;
}
pub unsafe fn l_Std_DTreeMap_alter___redArg(
    mut v_cmp_7712_: *mut crate::leanh::LeanObject,
    mut v_t_7713_: *mut crate::leanh::LeanObject,
    mut v_a_7714_: *mut crate::leanh::LeanObject,
    mut v_f_7715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7716_ =
        l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_7712_, v_a_7714_, v_f_7715_, v_t_7713_);
    return v___x_7716_;
}
pub unsafe fn l_Std_DTreeMap_alter(
    mut v_00_u03b1_7717_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7718_: *mut crate::leanh::LeanObject,
    mut v_cmp_7719_: *mut crate::leanh::LeanObject,
    mut v_inst_7720_: *mut crate::leanh::LeanObject,
    mut v_t_7721_: *mut crate::leanh::LeanObject,
    mut v_a_7722_: *mut crate::leanh::LeanObject,
    mut v_f_7723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7724_ =
        l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_7719_, v_a_7722_, v_f_7723_, v_t_7721_);
    return v___x_7724_;
}
pub unsafe fn l_Std_DTreeMap_mergeWith___redArg___lam__0(
    mut v_b_u2082_7725_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_7726_: *mut crate::leanh::LeanObject,
    mut v_a_7727_: *mut crate::leanh::LeanObject,
    mut v_x_7728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7733_: u8 = 0;
    let mut v___x_7734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7728_) == 0 {
                    crate::leanh::lean_dec(v_a_7727_);
                    crate::leanh::lean_dec(v_mergeFn_7726_);
                    v___x_7729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7729_, 0, v_b_u2082_7725_);
                    return v___x_7729_;
                } else {
                    v_val_7730_ = crate::leanh::lean_ctor_get(v_x_7728_, 0);
                    v_isSharedCheck_7738_ = (!crate::leanh::lean_is_exclusive(v_x_7728_)) as u8;
                    if v_isSharedCheck_7738_ == 0 {
                        v___x_7732_ = v_x_7728_;
                        v_isShared_7733_ = v_isSharedCheck_7738_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7730_);
                        crate::leanh::lean_dec(v_x_7728_);
                        v___x_7732_ = crate::leanh::lean_box(0);
                        v_isShared_7733_ = v_isSharedCheck_7738_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7734_ = crate::leanh::lean_apply_3(
                    v_mergeFn_7726_,
                    v_a_7727_,
                    v_val_7730_,
                    v_b_u2082_7725_,
                );
                if v_isShared_7733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7732_, 0, v___x_7734_);
                    v___x_7736_ = v___x_7732_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7737_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7737_, 0, v___x_7734_);
                    v___x_7736_ = v_reuseFailAlloc_7737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_mergeWith___redArg___lam__1(
    mut v_mergeFn_7739_: *mut crate::leanh::LeanObject,
    mut v_cmp_7740_: *mut crate::leanh::LeanObject,
    mut v_t_7741_: *mut crate::leanh::LeanObject,
    mut v_a_7742_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_7743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_7742_);
    v___f_7744_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_mergeWith___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7744_, 0, v_b_u2082_7743_);
    crate::leanh::lean_closure_set(v___f_7744_, 1, v_mergeFn_7739_);
    crate::leanh::lean_closure_set(v___f_7744_, 2, v_a_7742_);
    v___x_7745_ =
        l_Std_DTreeMap_Internal_Impl_alter___redArg(v_cmp_7740_, v_a_7742_, v___f_7744_, v_t_7741_);
    return v___x_7745_;
}
pub unsafe fn l_Std_DTreeMap_mergeWith___redArg(
    mut v_cmp_7746_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_7747_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_7748_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_7749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7750_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7750_, 0, v_mergeFn_7747_);
    crate::leanh::lean_closure_set(v___f_7750_, 1, v_cmp_7746_);
    v___x_7751_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7750_, v_t_u2081_7748_, v_t_u2082_7749_);
    return v___x_7751_;
}
pub unsafe fn l_Std_DTreeMap_mergeWith(
    mut v_00_u03b1_7752_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7753_: *mut crate::leanh::LeanObject,
    mut v_cmp_7754_: *mut crate::leanh::LeanObject,
    mut v_inst_7755_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_7756_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_7757_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_7758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7759_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7759_, 0, v_mergeFn_7756_);
    crate::leanh::lean_closure_set(v___f_7759_, 1, v_cmp_7754_);
    v___x_7760_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7759_, v_t_u2081_7757_, v_t_u2082_7758_);
    return v___x_7760_;
}
pub unsafe fn l_Std_DTreeMap_Const_toList___redArg___lam__0(
    mut v_x1_7761_: *mut crate::leanh::LeanObject,
    mut v_x2_7762_: *mut crate::leanh::LeanObject,
    mut v_x3_7763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7764_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7764_, 0, v_x1_7761_);
    crate::leanh::lean_ctor_set(v___x_7764_, 1, v_x2_7762_);
    v___x_7765_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7765_, 0, v___x_7764_);
    crate::leanh::lean_ctor_set(v___x_7765_, 1, v_x3_7763_);
    return v___x_7765_;
}
pub unsafe fn l_Std_DTreeMap_Const_toList___redArg(
    mut v_t_7767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7768_ = l_Std_DTreeMap_Const_toList___redArg___closed__0;
    v___x_7769_ = crate::leanh::lean_box(0);
    v___x_7770_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7771_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7770_,
        v___f_7768_,
        v___x_7769_,
        v_t_7767_,
    );
    return v___x_7771_;
}
pub unsafe fn l_Std_DTreeMap_Const_toList(
    mut v_00_u03b1_7772_: *mut crate::leanh::LeanObject,
    mut v_cmp_7773_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7774_: *mut crate::leanh::LeanObject,
    mut v_t_7775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7776_ = l_Std_DTreeMap_Const_toList___redArg___closed__0;
    v___x_7777_ = crate::leanh::lean_box(0);
    v___x_7778_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_7779_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_7778_,
        v___f_7776_,
        v___x_7777_,
        v_t_7775_,
    );
    return v___x_7779_;
}
pub unsafe fn l_Std_DTreeMap_Const_toList___boxed(
    mut v_00_u03b1_7780_: *mut crate::leanh::LeanObject,
    mut v_cmp_7781_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7782_: *mut crate::leanh::LeanObject,
    mut v_t_7783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7784_ =
        l_Std_DTreeMap_Const_toList(v_00_u03b1_7780_, v_cmp_7781_, v_00_u03b2_7782_, v_t_7783_);
    crate::leanh::lean_dec_ref(v_cmp_7781_);
    return v_res_7784_;
}
pub unsafe fn _init_l_Std_DTreeMap_Const_ofList___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7785_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26_once),
        _init_l_Std_DTreeMap___auto__1___closed__26,
    );
    return v___x_7785_;
}
pub unsafe fn l_Std_DTreeMap_Const_ofList___redArg___lam__0(
    mut v_cmp_7786_: *mut crate::leanh::LeanObject,
    mut v_a_7787_: *mut crate::leanh::LeanObject,
    mut v_x_7788_: *mut crate::leanh::LeanObject,
    mut v___y_7789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_7790_ = crate::leanh::lean_ctor_get(v_a_7787_, 0);
    crate::leanh::lean_inc(v_fst_7790_);
    v_snd_7791_ = crate::leanh::lean_ctor_get(v_a_7787_, 1);
    crate::leanh::lean_inc(v_snd_7791_);
    crate::leanh::lean_dec_ref(v_a_7787_);
    v_r_7792_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_7786_,
        v_fst_7790_,
        v_snd_7791_,
        v___y_7789_,
    );
    v___x_7793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7793_, 0, v_r_7792_);
    return v___x_7793_;
}
pub unsafe fn l_Std_DTreeMap_Const_ofList___redArg(
    mut v_l_7794_: *mut crate::leanh::LeanObject,
    mut v_cmp_7795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7796_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7796_, 0, v_cmp_7795_);
    v___x_7797_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7798_ = crate::leanh::lean_box(1);
    v___x_7799_ = l_List_forIn_x27_loop___redArg(v___x_7797_, v___f_7796_, v_l_7794_, v_r_7798_);
    return v___x_7799_;
}
pub unsafe fn l_Std_DTreeMap_Const_ofList___redArg___boxed(
    mut v_l_7800_: *mut crate::leanh::LeanObject,
    mut v_cmp_7801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7802_ = l_Std_DTreeMap_Const_ofList___redArg(v_l_7800_, v_cmp_7801_);
    crate::leanh::lean_dec(v_l_7800_);
    return v_res_7802_;
}
pub unsafe fn l_Std_DTreeMap_Const_ofList(
    mut v_00_u03b1_7803_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7804_: *mut crate::leanh::LeanObject,
    mut v_l_7805_: *mut crate::leanh::LeanObject,
    mut v_cmp_7806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7807_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7807_, 0, v_cmp_7806_);
    v___x_7808_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7809_ = crate::leanh::lean_box(1);
    v___x_7810_ = l_List_forIn_x27_loop___redArg(v___x_7808_, v___f_7807_, v_l_7805_, v_r_7809_);
    return v___x_7810_;
}
pub unsafe fn l_Std_DTreeMap_Const_ofList___boxed(
    mut v_00_u03b1_7811_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7812_: *mut crate::leanh::LeanObject,
    mut v_l_7813_: *mut crate::leanh::LeanObject,
    mut v_cmp_7814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7815_ =
        l_Std_DTreeMap_Const_ofList(v_00_u03b1_7811_, v_00_u03b2_7812_, v_l_7813_, v_cmp_7814_);
    crate::leanh::lean_dec(v_l_7813_);
    return v_res_7815_;
}
pub unsafe fn l_Std_DTreeMap_Const_toArray___redArg___lam__0(
    mut v_acc_7816_: *mut crate::leanh::LeanObject,
    mut v_k_7817_: *mut crate::leanh::LeanObject,
    mut v_v_7818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7819_, 0, v_k_7817_);
    crate::leanh::lean_ctor_set(v___x_7819_, 1, v_v_7818_);
    v___x_7820_ = lean_array_push(v_acc_7816_, v___x_7819_);
    return v___x_7820_;
}
pub unsafe fn l_Std_DTreeMap_Const_toArray___redArg(
    mut v_t_7824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7825_ = l_Std_DTreeMap_Const_toArray___redArg___closed__0;
    v___x_7826_ = l_Std_DTreeMap_Const_toArray___redArg___closed__1;
    v___x_7827_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7825_, v___x_7826_, v_t_7824_);
    return v___x_7827_;
}
pub unsafe fn l_Std_DTreeMap_Const_toArray(
    mut v_00_u03b1_7828_: *mut crate::leanh::LeanObject,
    mut v_cmp_7829_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7830_: *mut crate::leanh::LeanObject,
    mut v_t_7831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7832_ = l_Std_DTreeMap_Const_toArray___redArg___closed__0;
    v___x_7833_ = l_Std_DTreeMap_Const_toArray___redArg___closed__1;
    v___x_7834_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7832_, v___x_7833_, v_t_7831_);
    return v___x_7834_;
}
pub unsafe fn l_Std_DTreeMap_Const_toArray___boxed(
    mut v_00_u03b1_7835_: *mut crate::leanh::LeanObject,
    mut v_cmp_7836_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7837_: *mut crate::leanh::LeanObject,
    mut v_t_7838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7839_ =
        l_Std_DTreeMap_Const_toArray(v_00_u03b1_7835_, v_cmp_7836_, v_00_u03b2_7837_, v_t_7838_);
    crate::leanh::lean_dec_ref(v_cmp_7836_);
    return v_res_7839_;
}
pub unsafe fn _init_l_Std_DTreeMap_Const_ofArray___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7840_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26_once),
        _init_l_Std_DTreeMap___auto__1___closed__26,
    );
    return v___x_7840_;
}
pub unsafe fn l_Std_DTreeMap_Const_ofArray___redArg(
    mut v_a_7841_: *mut crate::leanh::LeanObject,
    mut v_cmp_7842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7846_: usize = 0;
    let mut v___x_7847_: usize = 0;
    let mut v___x_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7843_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7843_, 0, v_cmp_7842_);
    v___x_7844_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7845_ = crate::leanh::lean_box(1);
    v_sz_7846_ = lean_array_size(v_a_7841_);
    v___x_7847_ = 0usize;
    v___x_7848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7844_,
        v_a_7841_,
        v___f_7843_,
        v_sz_7846_,
        v___x_7847_,
        v_r_7845_,
    );
    return v___x_7848_;
}
pub unsafe fn l_Std_DTreeMap_Const_ofArray(
    mut v_00_u03b1_7849_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7850_: *mut crate::leanh::LeanObject,
    mut v_a_7851_: *mut crate::leanh::LeanObject,
    mut v_cmp_7852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7856_: usize = 0;
    let mut v___x_7857_: usize = 0;
    let mut v___x_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7853_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7853_, 0, v_cmp_7852_);
    v___x_7854_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7855_ = crate::leanh::lean_box(1);
    v_sz_7856_ = lean_array_size(v_a_7851_);
    v___x_7857_ = 0usize;
    v___x_7858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7854_,
        v_a_7851_,
        v___f_7853_,
        v_sz_7856_,
        v___x_7857_,
        v_r_7855_,
    );
    return v___x_7858_;
}
pub unsafe fn _init_l_Std_DTreeMap_Const_unitOfList___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_7859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7859_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26_once),
        _init_l_Std_DTreeMap___auto__1___closed__26,
    );
    return v___x_7859_;
}
pub unsafe fn l_Std_DTreeMap_Const_unitOfList___redArg___lam__0(
    mut v_cmp_7860_: *mut crate::leanh::LeanObject,
    mut v_a_7861_: *mut crate::leanh::LeanObject,
    mut v_x_7862_: *mut crate::leanh::LeanObject,
    mut v___y_7863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7864_: u8 = 0;
    crate::leanh::lean_inc(v___y_7863_);
    crate::leanh::lean_inc(v_a_7861_);
    crate::leanh::lean_inc_ref(v_cmp_7860_);
    v___x_7864_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_7860_, v_a_7861_, v___y_7863_);
    if v___x_7864_ == 0 {
        let mut v___x_7865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7865_ = crate::leanh::lean_box(0);
        v___x_7866_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_7860_,
            v_a_7861_,
            v___x_7865_,
            v___y_7863_,
        );
        v___x_7867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7867_, 0, v___x_7866_);
        return v___x_7867_;
    } else {
        let mut v___x_7868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_7861_);
        crate::leanh::lean_dec_ref(v_cmp_7860_);
        v___x_7868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7868_, 0, v___y_7863_);
        return v___x_7868_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_unitOfList___redArg(
    mut v_l_7869_: *mut crate::leanh::LeanObject,
    mut v_cmp_7870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7871_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7871_, 0, v_cmp_7870_);
    v___x_7872_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7873_ = crate::leanh::lean_box(1);
    v___x_7874_ = l_List_forIn_x27_loop___redArg(v___x_7872_, v___f_7871_, v_l_7869_, v_r_7873_);
    return v___x_7874_;
}
pub unsafe fn l_Std_DTreeMap_Const_unitOfList___redArg___boxed(
    mut v_l_7875_: *mut crate::leanh::LeanObject,
    mut v_cmp_7876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7877_ = l_Std_DTreeMap_Const_unitOfList___redArg(v_l_7875_, v_cmp_7876_);
    crate::leanh::lean_dec(v_l_7875_);
    return v_res_7877_;
}
pub unsafe fn l_Std_DTreeMap_Const_unitOfList(
    mut v_00_u03b1_7878_: *mut crate::leanh::LeanObject,
    mut v_l_7879_: *mut crate::leanh::LeanObject,
    mut v_cmp_7880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7881_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7881_, 0, v_cmp_7880_);
    v___x_7882_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7883_ = crate::leanh::lean_box(1);
    v___x_7884_ = l_List_forIn_x27_loop___redArg(v___x_7882_, v___f_7881_, v_l_7879_, v_r_7883_);
    return v___x_7884_;
}
pub unsafe fn l_Std_DTreeMap_Const_unitOfList___boxed(
    mut v_00_u03b1_7885_: *mut crate::leanh::LeanObject,
    mut v_l_7886_: *mut crate::leanh::LeanObject,
    mut v_cmp_7887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7888_ = l_Std_DTreeMap_Const_unitOfList(v_00_u03b1_7885_, v_l_7886_, v_cmp_7887_);
    crate::leanh::lean_dec(v_l_7886_);
    return v_res_7888_;
}
pub unsafe fn _init_l_Std_DTreeMap_Const_unitOfArray___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_7889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7889_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_DTreeMap___auto__1___closed__26_once),
        _init_l_Std_DTreeMap___auto__1___closed__26,
    );
    return v___x_7889_;
}
pub unsafe fn l_Std_DTreeMap_Const_unitOfArray___redArg(
    mut v_a_7890_: *mut crate::leanh::LeanObject,
    mut v_cmp_7891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7895_: usize = 0;
    let mut v___x_7896_: usize = 0;
    let mut v___x_7897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7892_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7892_, 0, v_cmp_7891_);
    v___x_7893_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7894_ = crate::leanh::lean_box(1);
    v_sz_7895_ = lean_array_size(v_a_7890_);
    v___x_7896_ = 0usize;
    v___x_7897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7893_,
        v_a_7890_,
        v___f_7892_,
        v_sz_7895_,
        v___x_7896_,
        v_r_7894_,
    );
    return v___x_7897_;
}
pub unsafe fn l_Std_DTreeMap_Const_unitOfArray(
    mut v_00_u03b1_7898_: *mut crate::leanh::LeanObject,
    mut v_a_7899_: *mut crate::leanh::LeanObject,
    mut v_cmp_7900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7904_: usize = 0;
    let mut v___x_7905_: usize = 0;
    let mut v___x_7906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7901_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7901_, 0, v_cmp_7900_);
    v___x_7902_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v_r_7903_ = crate::leanh::lean_box(1);
    v_sz_7904_ = lean_array_size(v_a_7899_);
    v___x_7905_ = 0usize;
    v___x_7906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7902_,
        v_a_7899_,
        v___f_7901_,
        v_sz_7904_,
        v___x_7905_,
        v_r_7903_,
    );
    return v___x_7906_;
}
pub unsafe fn l_Std_DTreeMap_Const_modify___redArg(
    mut v_cmp_7907_: *mut crate::leanh::LeanObject,
    mut v_t_7908_: *mut crate::leanh::LeanObject,
    mut v_a_7909_: *mut crate::leanh::LeanObject,
    mut v_f_7910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7911_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_7907_,
        v_a_7909_,
        v_f_7910_,
        v_t_7908_,
    );
    return v___x_7911_;
}
pub unsafe fn l_Std_DTreeMap_Const_modify(
    mut v_00_u03b1_7912_: *mut crate::leanh::LeanObject,
    mut v_cmp_7913_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7914_: *mut crate::leanh::LeanObject,
    mut v_t_7915_: *mut crate::leanh::LeanObject,
    mut v_a_7916_: *mut crate::leanh::LeanObject,
    mut v_f_7917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7918_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_7913_,
        v_a_7916_,
        v_f_7917_,
        v_t_7915_,
    );
    return v___x_7918_;
}
pub unsafe fn l_Std_DTreeMap_Const_alter___redArg(
    mut v_cmp_7919_: *mut crate::leanh::LeanObject,
    mut v_t_7920_: *mut crate::leanh::LeanObject,
    mut v_a_7921_: *mut crate::leanh::LeanObject,
    mut v_f_7922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7923_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_7919_,
        v_a_7921_,
        v_f_7922_,
        v_t_7920_,
    );
    return v___x_7923_;
}
pub unsafe fn l_Std_DTreeMap_Const_alter(
    mut v_00_u03b1_7924_: *mut crate::leanh::LeanObject,
    mut v_cmp_7925_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7926_: *mut crate::leanh::LeanObject,
    mut v_t_7927_: *mut crate::leanh::LeanObject,
    mut v_a_7928_: *mut crate::leanh::LeanObject,
    mut v_f_7929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7930_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_7925_,
        v_a_7928_,
        v_f_7929_,
        v_t_7927_,
    );
    return v___x_7930_;
}
pub unsafe fn l_Std_DTreeMap_Const_mergeWith___redArg___lam__1(
    mut v_mergeFn_7931_: *mut crate::leanh::LeanObject,
    mut v_cmp_7932_: *mut crate::leanh::LeanObject,
    mut v_t_7933_: *mut crate::leanh::LeanObject,
    mut v_a_7934_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_7935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_7934_);
    v___f_7936_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_mergeWith___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7936_, 0, v_b_u2082_7935_);
    crate::leanh::lean_closure_set(v___f_7936_, 1, v_mergeFn_7931_);
    crate::leanh::lean_closure_set(v___f_7936_, 2, v_a_7934_);
    v___x_7937_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_7932_,
        v_a_7934_,
        v___f_7936_,
        v_t_7933_,
    );
    return v___x_7937_;
}
pub unsafe fn l_Std_DTreeMap_Const_mergeWith___redArg(
    mut v_cmp_7938_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_7939_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_7940_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_7941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7942_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7942_, 0, v_mergeFn_7939_);
    crate::leanh::lean_closure_set(v___f_7942_, 1, v_cmp_7938_);
    v___x_7943_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7942_, v_t_u2081_7940_, v_t_u2082_7941_);
    return v___x_7943_;
}
pub unsafe fn l_Std_DTreeMap_Const_mergeWith(
    mut v_00_u03b1_7944_: *mut crate::leanh::LeanObject,
    mut v_cmp_7945_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7946_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_7947_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_7948_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_7949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7950_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7950_, 0, v_mergeFn_7947_);
    crate::leanh::lean_closure_set(v___f_7950_, 1, v_cmp_7945_);
    v___x_7951_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_7950_, v_t_u2081_7948_, v_t_u2082_7949_);
    return v___x_7951_;
}
pub unsafe fn l_Std_DTreeMap_insertMany___redArg___lam__0(
    mut v_cmp_7952_: *mut crate::leanh::LeanObject,
    mut v_x_7953_: *mut crate::leanh::LeanObject,
    mut v_____s_7954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_7955_ = crate::leanh::lean_ctor_get(v_x_7953_, 0);
    crate::leanh::lean_inc(v_fst_7955_);
    v_snd_7956_ = crate::leanh::lean_ctor_get(v_x_7953_, 1);
    crate::leanh::lean_inc(v_snd_7956_);
    crate::leanh::lean_dec_ref(v_x_7953_);
    v_r_7957_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_7952_,
        v_fst_7955_,
        v_snd_7956_,
        v_____s_7954_,
    );
    v___x_7958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7958_, 0, v_r_7957_);
    return v___x_7958_;
}
pub unsafe fn l_Std_DTreeMap_insertMany___redArg(
    mut v_cmp_7959_: *mut crate::leanh::LeanObject,
    mut v_inst_7960_: *mut crate::leanh::LeanObject,
    mut v_t_7961_: *mut crate::leanh::LeanObject,
    mut v_l_7962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7963_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7963_, 0, v_cmp_7959_);
    v___x_7964_ = crate::leanh::lean_apply_4(
        v_inst_7960_,
        crate::leanh::lean_box(0),
        v_l_7962_,
        v_t_7961_,
        v___f_7963_,
    );
    return v___x_7964_;
}
pub unsafe fn l_Std_DTreeMap_insertMany(
    mut v_00_u03b1_7965_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7966_: *mut crate::leanh::LeanObject,
    mut v_cmp_7967_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_7968_: *mut crate::leanh::LeanObject,
    mut v_inst_7969_: *mut crate::leanh::LeanObject,
    mut v_t_7970_: *mut crate::leanh::LeanObject,
    mut v_l_7971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7972_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7972_, 0, v_cmp_7967_);
    v___x_7973_ = crate::leanh::lean_apply_4(
        v_inst_7969_,
        crate::leanh::lean_box(0),
        v_l_7971_,
        v_t_7970_,
        v___f_7972_,
    );
    return v___x_7973_;
}
pub unsafe fn l_Std_DTreeMap_insertManyIfNew___redArg___lam__0(
    mut v_cmp_7974_: *mut crate::leanh::LeanObject,
    mut v_x_7975_: *mut crate::leanh::LeanObject,
    mut v_____s_7976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7979_: u8 = 0;
    v_fst_7977_ = crate::leanh::lean_ctor_get(v_x_7975_, 0);
    crate::leanh::lean_inc_n(v_fst_7977_, 2);
    v_snd_7978_ = crate::leanh::lean_ctor_get(v_x_7975_, 1);
    crate::leanh::lean_inc(v_snd_7978_);
    crate::leanh::lean_dec_ref(v_x_7975_);
    crate::leanh::lean_inc(v_____s_7976_);
    crate::leanh::lean_inc_ref(v_cmp_7974_);
    v___x_7979_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_7974_, v_fst_7977_, v_____s_7976_);
    if v___x_7979_ == 0 {
        let mut v___x_7980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7980_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_7974_,
            v_fst_7977_,
            v_snd_7978_,
            v_____s_7976_,
        );
        v___x_7981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7981_, 0, v___x_7980_);
        return v___x_7981_;
    } else {
        let mut v___x_7982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_snd_7978_);
        crate::leanh::lean_dec(v_fst_7977_);
        crate::leanh::lean_dec_ref(v_cmp_7974_);
        v___x_7982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7982_, 0, v_____s_7976_);
        return v___x_7982_;
    }
}
pub unsafe fn l_Std_DTreeMap_insertManyIfNew___redArg(
    mut v_cmp_7983_: *mut crate::leanh::LeanObject,
    mut v_inst_7984_: *mut crate::leanh::LeanObject,
    mut v_t_7985_: *mut crate::leanh::LeanObject,
    mut v_l_7986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7987_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_insertManyIfNew___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7987_, 0, v_cmp_7983_);
    v___x_7988_ = crate::leanh::lean_apply_4(
        v_inst_7984_,
        crate::leanh::lean_box(0),
        v_l_7986_,
        v_t_7985_,
        v___f_7987_,
    );
    return v___x_7988_;
}
pub unsafe fn l_Std_DTreeMap_insertManyIfNew(
    mut v_00_u03b1_7989_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7990_: *mut crate::leanh::LeanObject,
    mut v_cmp_7991_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_7992_: *mut crate::leanh::LeanObject,
    mut v_inst_7993_: *mut crate::leanh::LeanObject,
    mut v_t_7994_: *mut crate::leanh::LeanObject,
    mut v_l_7995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7996_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_insertManyIfNew___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7996_, 0, v_cmp_7991_);
    v___x_7997_ = crate::leanh::lean_apply_4(
        v_inst_7993_,
        crate::leanh::lean_box(0),
        v_l_7995_,
        v_t_7994_,
        v___f_7996_,
    );
    return v___x_7997_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(
    mut v_cmp_7998_: *mut crate::leanh::LeanObject,
    mut v_k_7999_: *mut crate::leanh::LeanObject,
    mut v_v_8000_: *mut crate::leanh::LeanObject,
    mut v_t_8001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8009_: u8 = 0;
    let mut v___x_8010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8011_: u8 = 0;
    let mut v_impl_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: u8 = 0;
    let mut v___x_8023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8030_: u8 = 0;
    let mut v_size_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8039_: u8 = 0;
    let mut v___x_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8042_: u8 = 0;
    let mut v___x_8043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8068_: u8 = 0;
    let mut v_unused_8069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8082_: u8 = 0;
    let mut v___x_8084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8086_: u8 = 0;
    let mut v_unused_8087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8093_: u8 = 0;
    let mut v_unused_8094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8105_: u8 = 0;
    let mut v___x_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8113_: u8 = 0;
    let mut v_unused_8114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8121_: u8 = 0;
    let mut v_k_8122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8126_: u8 = 0;
    let mut v___x_8127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8137_: u8 = 0;
    let mut v_unused_8138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8141_: u8 = 0;
    let mut v_unused_8142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_8152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8162_: u8 = 0;
    let mut v___x_8163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8170_: u8 = 0;
    let mut v_size_8171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8179_: u8 = 0;
    let mut v___x_8181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8182_: u8 = 0;
    let mut v___x_8183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8207_: u8 = 0;
    let mut v_unused_8208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8220_: u8 = 0;
    let mut v___x_8222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8224_: u8 = 0;
    let mut v_unused_8225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8231_: u8 = 0;
    let mut v_unused_8232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8243_: u8 = 0;
    let mut v_k_8244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8248_: u8 = 0;
    let mut v___x_8249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8259_: u8 = 0;
    let mut v_unused_8260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8263_: u8 = 0;
    let mut v_unused_8264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8271_: u8 = 0;
    let mut v___x_8272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8279_: u8 = 0;
    let mut v_unused_8280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8287_: u8 = 0;
    let mut v___x_8288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_8001_) == 0 {
                    v_size_8002_ = crate::leanh::lean_ctor_get(v_t_8001_, 0);
                    v_k_8003_ = crate::leanh::lean_ctor_get(v_t_8001_, 1);
                    v_v_8004_ = crate::leanh::lean_ctor_get(v_t_8001_, 2);
                    v_l_8005_ = crate::leanh::lean_ctor_get(v_t_8001_, 3);
                    v_r_8006_ = crate::leanh::lean_ctor_get(v_t_8001_, 4);
                    v_isSharedCheck_8287_ = (!crate::leanh::lean_is_exclusive(v_t_8001_)) as u8;
                    if v_isSharedCheck_8287_ == 0 {
                        v___x_8008_ = v_t_8001_;
                        v_isShared_8009_ = v_isSharedCheck_8287_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_8006_);
                        crate::leanh::lean_inc(v_l_8005_);
                        crate::leanh::lean_inc(v_v_8004_);
                        crate::leanh::lean_inc(v_k_8003_);
                        crate::leanh::lean_inc(v_size_8002_);
                        crate::leanh::lean_dec(v_t_8001_);
                        v___x_8008_ = crate::leanh::lean_box(0);
                        v_isShared_8009_ = v_isSharedCheck_8287_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_7998_);
                    v___x_8288_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8289_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8289_, 0, v___x_8288_);
                    crate::leanh::lean_ctor_set(v___x_8289_, 1, v_k_7999_);
                    crate::leanh::lean_ctor_set(v___x_8289_, 2, v_v_8000_);
                    crate::leanh::lean_ctor_set(v___x_8289_, 3, v_t_8001_);
                    crate::leanh::lean_ctor_set(v___x_8289_, 4, v_t_8001_);
                    return v___x_8289_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_7998_);
                crate::leanh::lean_inc(v_k_8003_);
                crate::leanh::lean_inc(v_k_7999_);
                v___x_8010_ = crate::leanh::lean_apply_2(v_cmp_7998_, v_k_7999_, v_k_8003_);
                v___x_8011_ = (crate::leanh::lean_unbox(v___x_8010_) as u8);
                match v___x_8011_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_8002_);
                        v_impl_8012_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_7998_, v_k_7999_, v_v_8000_, v_l_8005_);
                        v___x_8013_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_8006_) == 0 {
                            v_size_8014_ = crate::leanh::lean_ctor_get(v_r_8006_, 0);
                            v_size_8015_ = crate::leanh::lean_ctor_get(v_impl_8012_, 0);
                            crate::leanh::lean_inc(v_size_8015_);
                            v_k_8016_ = crate::leanh::lean_ctor_get(v_impl_8012_, 1);
                            crate::leanh::lean_inc(v_k_8016_);
                            v_v_8017_ = crate::leanh::lean_ctor_get(v_impl_8012_, 2);
                            crate::leanh::lean_inc(v_v_8017_);
                            v_l_8018_ = crate::leanh::lean_ctor_get(v_impl_8012_, 3);
                            crate::leanh::lean_inc(v_l_8018_);
                            v_r_8019_ = crate::leanh::lean_ctor_get(v_impl_8012_, 4);
                            crate::leanh::lean_inc(v_r_8019_);
                            v___x_8020_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_8021_ = lean_nat_mul(v___x_8020_, v_size_8014_);
                            v___x_8022_ = lean_nat_dec_lt(v___x_8021_, v_size_8015_);
                            crate::leanh::lean_dec(v___x_8021_);
                            if v___x_8022_ == 0 {
                                crate::leanh::lean_dec(v_r_8019_);
                                crate::leanh::lean_dec(v_l_8018_);
                                crate::leanh::lean_dec(v_v_8017_);
                                crate::leanh::lean_dec(v_k_8016_);
                                v___x_8023_ = lean_nat_add(v___x_8013_, v_size_8015_);
                                crate::leanh::lean_dec(v_size_8015_);
                                v___x_8024_ = lean_nat_add(v___x_8023_, v_size_8014_);
                                crate::leanh::lean_dec(v___x_8023_);
                                if v_isShared_8009_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_8008_, 3, v_impl_8012_);
                                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8024_);
                                    v___x_8026_ = v___x_8008_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_8027_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8027_,
                                        0,
                                        v___x_8024_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8027_,
                                        1,
                                        v_k_8003_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8027_,
                                        2,
                                        v_v_8004_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8027_,
                                        3,
                                        v_impl_8012_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8027_,
                                        4,
                                        v_r_8006_,
                                    );
                                    v___x_8026_ = v_reuseFailAlloc_8027_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_8093_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_8012_)) as u8;
                                if v_isSharedCheck_8093_ == 0 {
                                    v_unused_8094_ = crate::leanh::lean_ctor_get(v_impl_8012_, 4);
                                    crate::leanh::lean_dec(v_unused_8094_);
                                    v_unused_8095_ = crate::leanh::lean_ctor_get(v_impl_8012_, 3);
                                    crate::leanh::lean_dec(v_unused_8095_);
                                    v_unused_8096_ = crate::leanh::lean_ctor_get(v_impl_8012_, 2);
                                    crate::leanh::lean_dec(v_unused_8096_);
                                    v_unused_8097_ = crate::leanh::lean_ctor_get(v_impl_8012_, 1);
                                    crate::leanh::lean_dec(v_unused_8097_);
                                    v_unused_8098_ = crate::leanh::lean_ctor_get(v_impl_8012_, 0);
                                    crate::leanh::lean_dec(v_unused_8098_);
                                    v___x_8029_ = v_impl_8012_;
                                    v_isShared_8030_ = v_isSharedCheck_8093_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_8012_);
                                    v___x_8029_ = crate::leanh::lean_box(0);
                                    v_isShared_8030_ = v_isSharedCheck_8093_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_8099_ = crate::leanh::lean_ctor_get(v_impl_8012_, 3);
                            crate::leanh::lean_inc(v_l_8099_);
                            if crate::leanh::lean_obj_tag(v_l_8099_) == 0 {
                                v_r_8100_ = crate::leanh::lean_ctor_get(v_impl_8012_, 4);
                                v_k_8101_ = crate::leanh::lean_ctor_get(v_impl_8012_, 1);
                                v_v_8102_ = crate::leanh::lean_ctor_get(v_impl_8012_, 2);
                                v_isSharedCheck_8113_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_8012_)) as u8;
                                if v_isSharedCheck_8113_ == 0 {
                                    v_unused_8114_ = crate::leanh::lean_ctor_get(v_impl_8012_, 3);
                                    crate::leanh::lean_dec(v_unused_8114_);
                                    v_unused_8115_ = crate::leanh::lean_ctor_get(v_impl_8012_, 0);
                                    crate::leanh::lean_dec(v_unused_8115_);
                                    v___x_8104_ = v_impl_8012_;
                                    v_isShared_8105_ = v_isSharedCheck_8113_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_8100_);
                                    crate::leanh::lean_inc(v_v_8102_);
                                    crate::leanh::lean_inc(v_k_8101_);
                                    crate::leanh::lean_dec(v_impl_8012_);
                                    v___x_8104_ = crate::leanh::lean_box(0);
                                    v_isShared_8105_ = v_isSharedCheck_8113_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_8116_ = crate::leanh::lean_ctor_get(v_impl_8012_, 4);
                                crate::leanh::lean_inc(v_r_8116_);
                                if crate::leanh::lean_obj_tag(v_r_8116_) == 0 {
                                    v_k_8117_ = crate::leanh::lean_ctor_get(v_impl_8012_, 1);
                                    v_v_8118_ = crate::leanh::lean_ctor_get(v_impl_8012_, 2);
                                    v_isSharedCheck_8141_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_8012_)) as u8;
                                    if v_isSharedCheck_8141_ == 0 {
                                        v_unused_8142_ =
                                            crate::leanh::lean_ctor_get(v_impl_8012_, 4);
                                        crate::leanh::lean_dec(v_unused_8142_);
                                        v_unused_8143_ =
                                            crate::leanh::lean_ctor_get(v_impl_8012_, 3);
                                        crate::leanh::lean_dec(v_unused_8143_);
                                        v_unused_8144_ =
                                            crate::leanh::lean_ctor_get(v_impl_8012_, 0);
                                        crate::leanh::lean_dec(v_unused_8144_);
                                        v___x_8120_ = v_impl_8012_;
                                        v_isShared_8121_ = v_isSharedCheck_8141_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_8118_);
                                        crate::leanh::lean_inc(v_k_8117_);
                                        crate::leanh::lean_dec(v_impl_8012_);
                                        v___x_8120_ = crate::leanh::lean_box(0);
                                        v_isShared_8121_ = v_isSharedCheck_8141_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_8145_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_8009_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_8008_, 4, v_r_8116_);
                                        crate::leanh::lean_ctor_set(v___x_8008_, 3, v_impl_8012_);
                                        crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8145_);
                                        v___x_8147_ = v___x_8008_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_8148_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8148_,
                                            0,
                                            v___x_8145_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8148_,
                                            1,
                                            v_k_8003_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8148_,
                                            2,
                                            v_v_8004_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8148_,
                                            3,
                                            v_impl_8012_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8148_,
                                            4,
                                            v_r_8116_,
                                        );
                                        v___x_8147_ = v_reuseFailAlloc_8148_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_8004_);
                        crate::leanh::lean_dec(v_k_8003_);
                        crate::leanh::lean_dec_ref(v_cmp_7998_);
                        if v_isShared_8009_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8008_, 2, v_v_8000_);
                            crate::leanh::lean_ctor_set(v___x_8008_, 1, v_k_7999_);
                            v___x_8150_ = v___x_8008_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_8151_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8151_, 0, v_size_8002_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8151_, 1, v_k_7999_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8151_, 2, v_v_8000_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8151_, 3, v_l_8005_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8151_, 4, v_r_8006_);
                            v___x_8150_ = v_reuseFailAlloc_8151_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_8002_);
                        v_impl_8152_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_7998_, v_k_7999_, v_v_8000_, v_r_8006_);
                        v___x_8153_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_8005_) == 0 {
                            v_size_8154_ = crate::leanh::lean_ctor_get(v_l_8005_, 0);
                            v_size_8155_ = crate::leanh::lean_ctor_get(v_impl_8152_, 0);
                            crate::leanh::lean_inc(v_size_8155_);
                            v_k_8156_ = crate::leanh::lean_ctor_get(v_impl_8152_, 1);
                            crate::leanh::lean_inc(v_k_8156_);
                            v_v_8157_ = crate::leanh::lean_ctor_get(v_impl_8152_, 2);
                            crate::leanh::lean_inc(v_v_8157_);
                            v_l_8158_ = crate::leanh::lean_ctor_get(v_impl_8152_, 3);
                            crate::leanh::lean_inc(v_l_8158_);
                            v_r_8159_ = crate::leanh::lean_ctor_get(v_impl_8152_, 4);
                            crate::leanh::lean_inc(v_r_8159_);
                            v___x_8160_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_8161_ = lean_nat_mul(v___x_8160_, v_size_8154_);
                            v___x_8162_ = lean_nat_dec_lt(v___x_8161_, v_size_8155_);
                            crate::leanh::lean_dec(v___x_8161_);
                            if v___x_8162_ == 0 {
                                crate::leanh::lean_dec(v_r_8159_);
                                crate::leanh::lean_dec(v_l_8158_);
                                crate::leanh::lean_dec(v_v_8157_);
                                crate::leanh::lean_dec(v_k_8156_);
                                v___x_8163_ = lean_nat_add(v___x_8153_, v_size_8154_);
                                v___x_8164_ = lean_nat_add(v___x_8163_, v_size_8155_);
                                crate::leanh::lean_dec(v_size_8155_);
                                crate::leanh::lean_dec(v___x_8163_);
                                if v_isShared_8009_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_8008_, 4, v_impl_8152_);
                                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8164_);
                                    v___x_8166_ = v___x_8008_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_8167_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8167_,
                                        0,
                                        v___x_8164_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8167_,
                                        1,
                                        v_k_8003_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8167_,
                                        2,
                                        v_v_8004_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8167_,
                                        3,
                                        v_l_8005_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8167_,
                                        4,
                                        v_impl_8152_,
                                    );
                                    v___x_8166_ = v_reuseFailAlloc_8167_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_8231_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_8152_)) as u8;
                                if v_isSharedCheck_8231_ == 0 {
                                    v_unused_8232_ = crate::leanh::lean_ctor_get(v_impl_8152_, 4);
                                    crate::leanh::lean_dec(v_unused_8232_);
                                    v_unused_8233_ = crate::leanh::lean_ctor_get(v_impl_8152_, 3);
                                    crate::leanh::lean_dec(v_unused_8233_);
                                    v_unused_8234_ = crate::leanh::lean_ctor_get(v_impl_8152_, 2);
                                    crate::leanh::lean_dec(v_unused_8234_);
                                    v_unused_8235_ = crate::leanh::lean_ctor_get(v_impl_8152_, 1);
                                    crate::leanh::lean_dec(v_unused_8235_);
                                    v_unused_8236_ = crate::leanh::lean_ctor_get(v_impl_8152_, 0);
                                    crate::leanh::lean_dec(v_unused_8236_);
                                    v___x_8169_ = v_impl_8152_;
                                    v_isShared_8170_ = v_isSharedCheck_8231_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_8152_);
                                    v___x_8169_ = crate::leanh::lean_box(0);
                                    v_isShared_8170_ = v_isSharedCheck_8231_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_8237_ = crate::leanh::lean_ctor_get(v_impl_8152_, 3);
                            crate::leanh::lean_inc(v_l_8237_);
                            if crate::leanh::lean_obj_tag(v_l_8237_) == 0 {
                                v_r_8238_ = crate::leanh::lean_ctor_get(v_impl_8152_, 4);
                                v_k_8239_ = crate::leanh::lean_ctor_get(v_impl_8152_, 1);
                                v_v_8240_ = crate::leanh::lean_ctor_get(v_impl_8152_, 2);
                                v_isSharedCheck_8263_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_8152_)) as u8;
                                if v_isSharedCheck_8263_ == 0 {
                                    v_unused_8264_ = crate::leanh::lean_ctor_get(v_impl_8152_, 3);
                                    crate::leanh::lean_dec(v_unused_8264_);
                                    v_unused_8265_ = crate::leanh::lean_ctor_get(v_impl_8152_, 0);
                                    crate::leanh::lean_dec(v_unused_8265_);
                                    v___x_8242_ = v_impl_8152_;
                                    v_isShared_8243_ = v_isSharedCheck_8263_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_8238_);
                                    crate::leanh::lean_inc(v_v_8240_);
                                    crate::leanh::lean_inc(v_k_8239_);
                                    crate::leanh::lean_dec(v_impl_8152_);
                                    v___x_8242_ = crate::leanh::lean_box(0);
                                    v_isShared_8243_ = v_isSharedCheck_8263_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_8266_ = crate::leanh::lean_ctor_get(v_impl_8152_, 4);
                                crate::leanh::lean_inc(v_r_8266_);
                                if crate::leanh::lean_obj_tag(v_r_8266_) == 0 {
                                    v_k_8267_ = crate::leanh::lean_ctor_get(v_impl_8152_, 1);
                                    v_v_8268_ = crate::leanh::lean_ctor_get(v_impl_8152_, 2);
                                    v_isSharedCheck_8279_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_8152_)) as u8;
                                    if v_isSharedCheck_8279_ == 0 {
                                        v_unused_8280_ =
                                            crate::leanh::lean_ctor_get(v_impl_8152_, 4);
                                        crate::leanh::lean_dec(v_unused_8280_);
                                        v_unused_8281_ =
                                            crate::leanh::lean_ctor_get(v_impl_8152_, 3);
                                        crate::leanh::lean_dec(v_unused_8281_);
                                        v_unused_8282_ =
                                            crate::leanh::lean_ctor_get(v_impl_8152_, 0);
                                        crate::leanh::lean_dec(v_unused_8282_);
                                        v___x_8270_ = v_impl_8152_;
                                        v_isShared_8271_ = v_isSharedCheck_8279_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_8268_);
                                        crate::leanh::lean_inc(v_k_8267_);
                                        crate::leanh::lean_dec(v_impl_8152_);
                                        v___x_8270_ = crate::leanh::lean_box(0);
                                        v_isShared_8271_ = v_isSharedCheck_8279_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_8283_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_8009_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_8008_, 4, v_impl_8152_);
                                        crate::leanh::lean_ctor_set(v___x_8008_, 3, v_r_8266_);
                                        crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8283_);
                                        v___x_8285_ = v___x_8008_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_8286_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8286_,
                                            0,
                                            v___x_8283_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8286_,
                                            1,
                                            v_k_8003_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8286_,
                                            2,
                                            v_v_8004_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8286_,
                                            3,
                                            v_r_8266_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8286_,
                                            4,
                                            v_impl_8152_,
                                        );
                                        v___x_8285_ = v_reuseFailAlloc_8286_;
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
                return v___x_8026_;
            }
            3 => {
                v_size_8031_ = crate::leanh::lean_ctor_get(v_l_8018_, 0);
                v_size_8032_ = crate::leanh::lean_ctor_get(v_r_8019_, 0);
                v_k_8033_ = crate::leanh::lean_ctor_get(v_r_8019_, 1);
                v_v_8034_ = crate::leanh::lean_ctor_get(v_r_8019_, 2);
                v_l_8035_ = crate::leanh::lean_ctor_get(v_r_8019_, 3);
                v_r_8036_ = crate::leanh::lean_ctor_get(v_r_8019_, 4);
                v___x_8037_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_8038_ = lean_nat_mul(v___x_8037_, v_size_8031_);
                v___x_8039_ = lean_nat_dec_lt(v_size_8032_, v___x_8038_);
                crate::leanh::lean_dec(v___x_8038_);
                if v___x_8039_ == 0 {
                    crate::leanh::lean_inc(v_r_8036_);
                    crate::leanh::lean_inc(v_l_8035_);
                    crate::leanh::lean_inc(v_v_8034_);
                    crate::leanh::lean_inc(v_k_8033_);
                    v_isSharedCheck_8068_ = (!crate::leanh::lean_is_exclusive(v_r_8019_)) as u8;
                    if v_isSharedCheck_8068_ == 0 {
                        v_unused_8069_ = crate::leanh::lean_ctor_get(v_r_8019_, 4);
                        crate::leanh::lean_dec(v_unused_8069_);
                        v_unused_8070_ = crate::leanh::lean_ctor_get(v_r_8019_, 3);
                        crate::leanh::lean_dec(v_unused_8070_);
                        v_unused_8071_ = crate::leanh::lean_ctor_get(v_r_8019_, 2);
                        crate::leanh::lean_dec(v_unused_8071_);
                        v_unused_8072_ = crate::leanh::lean_ctor_get(v_r_8019_, 1);
                        crate::leanh::lean_dec(v_unused_8072_);
                        v_unused_8073_ = crate::leanh::lean_ctor_get(v_r_8019_, 0);
                        crate::leanh::lean_dec(v_unused_8073_);
                        v___x_8041_ = v_r_8019_;
                        v_isShared_8042_ = v_isSharedCheck_8068_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_8019_);
                        v___x_8041_ = crate::leanh::lean_box(0);
                        v_isShared_8042_ = v_isSharedCheck_8068_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8008_);
                    v___x_8074_ = lean_nat_add(v___x_8013_, v_size_8015_);
                    crate::leanh::lean_dec(v_size_8015_);
                    v___x_8075_ = lean_nat_add(v___x_8074_, v_size_8014_);
                    crate::leanh::lean_dec(v___x_8074_);
                    v___x_8076_ = lean_nat_add(v___x_8013_, v_size_8014_);
                    v___x_8077_ = lean_nat_add(v___x_8076_, v_size_8032_);
                    crate::leanh::lean_dec(v___x_8076_);
                    crate::leanh::lean_inc_ref(v_r_8006_);
                    if v_isShared_8030_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8029_, 4, v_r_8006_);
                        crate::leanh::lean_ctor_set(v___x_8029_, 3, v_r_8019_);
                        crate::leanh::lean_ctor_set(v___x_8029_, 2, v_v_8004_);
                        crate::leanh::lean_ctor_set(v___x_8029_, 1, v_k_8003_);
                        crate::leanh::lean_ctor_set(v___x_8029_, 0, v___x_8077_);
                        v___x_8079_ = v___x_8029_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_8092_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8092_, 0, v___x_8077_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8092_, 1, v_k_8003_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8092_, 2, v_v_8004_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8092_, 3, v_r_8019_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8092_, 4, v_r_8006_);
                        v___x_8079_ = v_reuseFailAlloc_8092_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_8043_ = lean_nat_add(v___x_8013_, v_size_8015_);
                crate::leanh::lean_dec(v_size_8015_);
                v___x_8044_ = lean_nat_add(v___x_8043_, v_size_8014_);
                crate::leanh::lean_dec(v___x_8043_);
                v___x_8056_ = lean_nat_add(v___x_8013_, v_size_8031_);
                if crate::leanh::lean_obj_tag(v_l_8035_) == 0 {
                    v_size_8066_ = crate::leanh::lean_ctor_get(v_l_8035_, 0);
                    crate::leanh::lean_inc(v_size_8066_);
                    v___y_8058_ = v_size_8066_;
                    state = 8;
                    continue;
                } else {
                    v___x_8067_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8058_ = v___x_8067_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_8049_ = lean_nat_add(v___y_8046_, v___y_8048_);
                crate::leanh::lean_dec(v___y_8048_);
                crate::leanh::lean_dec(v___y_8046_);
                if v_isShared_8042_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8041_, 4, v_r_8006_);
                    crate::leanh::lean_ctor_set(v___x_8041_, 3, v_r_8036_);
                    crate::leanh::lean_ctor_set(v___x_8041_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v___x_8041_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v___x_8041_, 0, v___x_8049_);
                    v___x_8051_ = v___x_8041_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8055_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8055_, 0, v___x_8049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8055_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8055_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8055_, 3, v_r_8036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8055_, 4, v_r_8006_);
                    v___x_8051_ = v_reuseFailAlloc_8055_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_8030_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8029_, 4, v___x_8051_);
                    crate::leanh::lean_ctor_set(v___x_8029_, 3, v___y_8047_);
                    crate::leanh::lean_ctor_set(v___x_8029_, 2, v_v_8034_);
                    crate::leanh::lean_ctor_set(v___x_8029_, 1, v_k_8033_);
                    crate::leanh::lean_ctor_set(v___x_8029_, 0, v___x_8044_);
                    v___x_8053_ = v___x_8029_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8054_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8054_, 0, v___x_8044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8054_, 1, v_k_8033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8054_, 2, v_v_8034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8054_, 3, v___y_8047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8054_, 4, v___x_8051_);
                    v___x_8053_ = v_reuseFailAlloc_8054_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8053_;
            }
            8 => {
                v___x_8059_ = lean_nat_add(v___x_8056_, v___y_8058_);
                crate::leanh::lean_dec(v___y_8058_);
                crate::leanh::lean_dec(v___x_8056_);
                if v_isShared_8009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8008_, 4, v_l_8035_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 3, v_l_8018_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 2, v_v_8017_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 1, v_k_8016_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8059_);
                    v___x_8061_ = v___x_8008_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8065_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8065_, 0, v___x_8059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8065_, 1, v_k_8016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8065_, 2, v_v_8017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8065_, 3, v_l_8018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8065_, 4, v_l_8035_);
                    v___x_8061_ = v_reuseFailAlloc_8065_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_8062_ = lean_nat_add(v___x_8013_, v_size_8014_);
                if crate::leanh::lean_obj_tag(v_r_8036_) == 0 {
                    v_size_8063_ = crate::leanh::lean_ctor_get(v_r_8036_, 0);
                    crate::leanh::lean_inc(v_size_8063_);
                    v___y_8046_ = v___x_8062_;
                    v___y_8047_ = v___x_8061_;
                    v___y_8048_ = v_size_8063_;
                    state = 5;
                    continue;
                } else {
                    v___x_8064_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8046_ = v___x_8062_;
                    v___y_8047_ = v___x_8061_;
                    v___y_8048_ = v___x_8064_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_8086_ = (!crate::leanh::lean_is_exclusive(v_r_8006_)) as u8;
                if v_isSharedCheck_8086_ == 0 {
                    v_unused_8087_ = crate::leanh::lean_ctor_get(v_r_8006_, 4);
                    crate::leanh::lean_dec(v_unused_8087_);
                    v_unused_8088_ = crate::leanh::lean_ctor_get(v_r_8006_, 3);
                    crate::leanh::lean_dec(v_unused_8088_);
                    v_unused_8089_ = crate::leanh::lean_ctor_get(v_r_8006_, 2);
                    crate::leanh::lean_dec(v_unused_8089_);
                    v_unused_8090_ = crate::leanh::lean_ctor_get(v_r_8006_, 1);
                    crate::leanh::lean_dec(v_unused_8090_);
                    v_unused_8091_ = crate::leanh::lean_ctor_get(v_r_8006_, 0);
                    crate::leanh::lean_dec(v_unused_8091_);
                    v___x_8081_ = v_r_8006_;
                    v_isShared_8082_ = v_isSharedCheck_8086_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_8006_);
                    v___x_8081_ = crate::leanh::lean_box(0);
                    v_isShared_8082_ = v_isSharedCheck_8086_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_8082_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8081_, 4, v___x_8079_);
                    crate::leanh::lean_ctor_set(v___x_8081_, 3, v_l_8018_);
                    crate::leanh::lean_ctor_set(v___x_8081_, 2, v_v_8017_);
                    crate::leanh::lean_ctor_set(v___x_8081_, 1, v_k_8016_);
                    crate::leanh::lean_ctor_set(v___x_8081_, 0, v___x_8075_);
                    v___x_8084_ = v___x_8081_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8085_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 0, v___x_8075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 1, v_k_8016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 2, v_v_8017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 3, v_l_8018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 4, v___x_8079_);
                    v___x_8084_ = v_reuseFailAlloc_8085_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8084_;
            }
            13 => {
                v___x_8106_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_8100_);
                if v_isShared_8105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8104_, 3, v_r_8100_);
                    crate::leanh::lean_ctor_set(v___x_8104_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v___x_8104_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v___x_8104_, 0, v___x_8013_);
                    v___x_8108_ = v___x_8104_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_8112_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 0, v___x_8013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 3, v_r_8100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 4, v_r_8100_);
                    v___x_8108_ = v_reuseFailAlloc_8112_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_8009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8008_, 4, v___x_8108_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 3, v_l_8099_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 2, v_v_8102_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 1, v_k_8101_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8106_);
                    v___x_8110_ = v___x_8008_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8111_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8111_, 0, v___x_8106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8111_, 1, v_k_8101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8111_, 2, v_v_8102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8111_, 3, v_l_8099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8111_, 4, v___x_8108_);
                    v___x_8110_ = v_reuseFailAlloc_8111_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8110_;
            }
            16 => {
                v_k_8122_ = crate::leanh::lean_ctor_get(v_r_8116_, 1);
                v_v_8123_ = crate::leanh::lean_ctor_get(v_r_8116_, 2);
                v_isSharedCheck_8137_ = (!crate::leanh::lean_is_exclusive(v_r_8116_)) as u8;
                if v_isSharedCheck_8137_ == 0 {
                    v_unused_8138_ = crate::leanh::lean_ctor_get(v_r_8116_, 4);
                    crate::leanh::lean_dec(v_unused_8138_);
                    v_unused_8139_ = crate::leanh::lean_ctor_get(v_r_8116_, 3);
                    crate::leanh::lean_dec(v_unused_8139_);
                    v_unused_8140_ = crate::leanh::lean_ctor_get(v_r_8116_, 0);
                    crate::leanh::lean_dec(v_unused_8140_);
                    v___x_8125_ = v_r_8116_;
                    v_isShared_8126_ = v_isSharedCheck_8137_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_8123_);
                    crate::leanh::lean_inc(v_k_8122_);
                    crate::leanh::lean_dec(v_r_8116_);
                    v___x_8125_ = crate::leanh::lean_box(0);
                    v_isShared_8126_ = v_isSharedCheck_8137_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_8127_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_8126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8125_, 4, v_l_8099_);
                    crate::leanh::lean_ctor_set(v___x_8125_, 3, v_l_8099_);
                    crate::leanh::lean_ctor_set(v___x_8125_, 2, v_v_8118_);
                    crate::leanh::lean_ctor_set(v___x_8125_, 1, v_k_8117_);
                    crate::leanh::lean_ctor_set(v___x_8125_, 0, v___x_8013_);
                    v___x_8129_ = v___x_8125_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_8136_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8136_, 0, v___x_8013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8136_, 1, v_k_8117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8136_, 2, v_v_8118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8136_, 3, v_l_8099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8136_, 4, v_l_8099_);
                    v___x_8129_ = v_reuseFailAlloc_8136_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_8121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8120_, 4, v_l_8099_);
                    crate::leanh::lean_ctor_set(v___x_8120_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v___x_8120_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v___x_8120_, 0, v___x_8013_);
                    v___x_8131_ = v___x_8120_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_8135_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8135_, 0, v___x_8013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8135_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8135_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8135_, 3, v_l_8099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8135_, 4, v_l_8099_);
                    v___x_8131_ = v_reuseFailAlloc_8135_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_8009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8008_, 4, v___x_8131_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 3, v___x_8129_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 2, v_v_8123_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 1, v_k_8122_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8127_);
                    v___x_8133_ = v___x_8008_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_8134_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8134_, 0, v___x_8127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8134_, 1, v_k_8122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8134_, 2, v_v_8123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8134_, 3, v___x_8129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8134_, 4, v___x_8131_);
                    v___x_8133_ = v_reuseFailAlloc_8134_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_8133_;
            }
            21 => {
                return v___x_8147_;
            }
            22 => {
                return v___x_8150_;
            }
            23 => {
                return v___x_8166_;
            }
            24 => {
                v_size_8171_ = crate::leanh::lean_ctor_get(v_l_8158_, 0);
                v_k_8172_ = crate::leanh::lean_ctor_get(v_l_8158_, 1);
                v_v_8173_ = crate::leanh::lean_ctor_get(v_l_8158_, 2);
                v_l_8174_ = crate::leanh::lean_ctor_get(v_l_8158_, 3);
                v_r_8175_ = crate::leanh::lean_ctor_get(v_l_8158_, 4);
                v_size_8176_ = crate::leanh::lean_ctor_get(v_r_8159_, 0);
                v___x_8177_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_8178_ = lean_nat_mul(v___x_8177_, v_size_8176_);
                v___x_8179_ = lean_nat_dec_lt(v_size_8171_, v___x_8178_);
                crate::leanh::lean_dec(v___x_8178_);
                if v___x_8179_ == 0 {
                    crate::leanh::lean_inc(v_r_8175_);
                    crate::leanh::lean_inc(v_l_8174_);
                    crate::leanh::lean_inc(v_v_8173_);
                    crate::leanh::lean_inc(v_k_8172_);
                    v_isSharedCheck_8207_ = (!crate::leanh::lean_is_exclusive(v_l_8158_)) as u8;
                    if v_isSharedCheck_8207_ == 0 {
                        v_unused_8208_ = crate::leanh::lean_ctor_get(v_l_8158_, 4);
                        crate::leanh::lean_dec(v_unused_8208_);
                        v_unused_8209_ = crate::leanh::lean_ctor_get(v_l_8158_, 3);
                        crate::leanh::lean_dec(v_unused_8209_);
                        v_unused_8210_ = crate::leanh::lean_ctor_get(v_l_8158_, 2);
                        crate::leanh::lean_dec(v_unused_8210_);
                        v_unused_8211_ = crate::leanh::lean_ctor_get(v_l_8158_, 1);
                        crate::leanh::lean_dec(v_unused_8211_);
                        v_unused_8212_ = crate::leanh::lean_ctor_get(v_l_8158_, 0);
                        crate::leanh::lean_dec(v_unused_8212_);
                        v___x_8181_ = v_l_8158_;
                        v_isShared_8182_ = v_isSharedCheck_8207_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_8158_);
                        v___x_8181_ = crate::leanh::lean_box(0);
                        v_isShared_8182_ = v_isSharedCheck_8207_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8008_);
                    v___x_8213_ = lean_nat_add(v___x_8153_, v_size_8154_);
                    v___x_8214_ = lean_nat_add(v___x_8213_, v_size_8155_);
                    crate::leanh::lean_dec(v_size_8155_);
                    v___x_8215_ = lean_nat_add(v___x_8213_, v_size_8171_);
                    crate::leanh::lean_dec(v___x_8213_);
                    crate::leanh::lean_inc_ref(v_l_8005_);
                    if v_isShared_8170_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8169_, 4, v_l_8158_);
                        crate::leanh::lean_ctor_set(v___x_8169_, 3, v_l_8005_);
                        crate::leanh::lean_ctor_set(v___x_8169_, 2, v_v_8004_);
                        crate::leanh::lean_ctor_set(v___x_8169_, 1, v_k_8003_);
                        crate::leanh::lean_ctor_set(v___x_8169_, 0, v___x_8215_);
                        v___x_8217_ = v___x_8169_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_8230_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8230_, 0, v___x_8215_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8230_, 1, v_k_8003_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8230_, 2, v_v_8004_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8230_, 3, v_l_8005_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8230_, 4, v_l_8158_);
                        v___x_8217_ = v_reuseFailAlloc_8230_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_8183_ = lean_nat_add(v___x_8153_, v_size_8154_);
                v___x_8184_ = lean_nat_add(v___x_8183_, v_size_8155_);
                crate::leanh::lean_dec(v_size_8155_);
                if crate::leanh::lean_obj_tag(v_l_8174_) == 0 {
                    v_size_8205_ = crate::leanh::lean_ctor_get(v_l_8174_, 0);
                    crate::leanh::lean_inc(v_size_8205_);
                    v___y_8197_ = v_size_8205_;
                    state = 29;
                    continue;
                } else {
                    v___x_8206_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8197_ = v___x_8206_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_8189_ = lean_nat_add(v___y_8187_, v___y_8188_);
                crate::leanh::lean_dec(v___y_8188_);
                crate::leanh::lean_dec(v___y_8187_);
                if v_isShared_8182_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8181_, 4, v_r_8159_);
                    crate::leanh::lean_ctor_set(v___x_8181_, 3, v_r_8175_);
                    crate::leanh::lean_ctor_set(v___x_8181_, 2, v_v_8157_);
                    crate::leanh::lean_ctor_set(v___x_8181_, 1, v_k_8156_);
                    crate::leanh::lean_ctor_set(v___x_8181_, 0, v___x_8189_);
                    v___x_8191_ = v___x_8181_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_8195_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 0, v___x_8189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 1, v_k_8156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 2, v_v_8157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 3, v_r_8175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 4, v_r_8159_);
                    v___x_8191_ = v_reuseFailAlloc_8195_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_8170_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8169_, 4, v___x_8191_);
                    crate::leanh::lean_ctor_set(v___x_8169_, 3, v___y_8186_);
                    crate::leanh::lean_ctor_set(v___x_8169_, 2, v_v_8173_);
                    crate::leanh::lean_ctor_set(v___x_8169_, 1, v_k_8172_);
                    crate::leanh::lean_ctor_set(v___x_8169_, 0, v___x_8184_);
                    v___x_8193_ = v___x_8169_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_8194_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8194_, 0, v___x_8184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8194_, 1, v_k_8172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8194_, 2, v_v_8173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8194_, 3, v___y_8186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8194_, 4, v___x_8191_);
                    v___x_8193_ = v_reuseFailAlloc_8194_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_8193_;
            }
            29 => {
                v___x_8198_ = lean_nat_add(v___x_8183_, v___y_8197_);
                crate::leanh::lean_dec(v___y_8197_);
                crate::leanh::lean_dec(v___x_8183_);
                if v_isShared_8009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8008_, 4, v_l_8174_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8198_);
                    v___x_8200_ = v___x_8008_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_8204_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8204_, 0, v___x_8198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8204_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8204_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8204_, 3, v_l_8005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8204_, 4, v_l_8174_);
                    v___x_8200_ = v_reuseFailAlloc_8204_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_8201_ = lean_nat_add(v___x_8153_, v_size_8176_);
                if crate::leanh::lean_obj_tag(v_r_8175_) == 0 {
                    v_size_8202_ = crate::leanh::lean_ctor_get(v_r_8175_, 0);
                    crate::leanh::lean_inc(v_size_8202_);
                    v___y_8186_ = v___x_8200_;
                    v___y_8187_ = v___x_8201_;
                    v___y_8188_ = v_size_8202_;
                    state = 26;
                    continue;
                } else {
                    v___x_8203_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8186_ = v___x_8200_;
                    v___y_8187_ = v___x_8201_;
                    v___y_8188_ = v___x_8203_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_8224_ = (!crate::leanh::lean_is_exclusive(v_l_8005_)) as u8;
                if v_isSharedCheck_8224_ == 0 {
                    v_unused_8225_ = crate::leanh::lean_ctor_get(v_l_8005_, 4);
                    crate::leanh::lean_dec(v_unused_8225_);
                    v_unused_8226_ = crate::leanh::lean_ctor_get(v_l_8005_, 3);
                    crate::leanh::lean_dec(v_unused_8226_);
                    v_unused_8227_ = crate::leanh::lean_ctor_get(v_l_8005_, 2);
                    crate::leanh::lean_dec(v_unused_8227_);
                    v_unused_8228_ = crate::leanh::lean_ctor_get(v_l_8005_, 1);
                    crate::leanh::lean_dec(v_unused_8228_);
                    v_unused_8229_ = crate::leanh::lean_ctor_get(v_l_8005_, 0);
                    crate::leanh::lean_dec(v_unused_8229_);
                    v___x_8219_ = v_l_8005_;
                    v_isShared_8220_ = v_isSharedCheck_8224_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_8005_);
                    v___x_8219_ = crate::leanh::lean_box(0);
                    v_isShared_8220_ = v_isSharedCheck_8224_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_8220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8219_, 4, v_r_8159_);
                    crate::leanh::lean_ctor_set(v___x_8219_, 3, v___x_8217_);
                    crate::leanh::lean_ctor_set(v___x_8219_, 2, v_v_8157_);
                    crate::leanh::lean_ctor_set(v___x_8219_, 1, v_k_8156_);
                    crate::leanh::lean_ctor_set(v___x_8219_, 0, v___x_8214_);
                    v___x_8222_ = v___x_8219_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_8223_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8223_, 0, v___x_8214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8223_, 1, v_k_8156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8223_, 2, v_v_8157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8223_, 3, v___x_8217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8223_, 4, v_r_8159_);
                    v___x_8222_ = v_reuseFailAlloc_8223_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_8222_;
            }
            34 => {
                v_k_8244_ = crate::leanh::lean_ctor_get(v_l_8237_, 1);
                v_v_8245_ = crate::leanh::lean_ctor_get(v_l_8237_, 2);
                v_isSharedCheck_8259_ = (!crate::leanh::lean_is_exclusive(v_l_8237_)) as u8;
                if v_isSharedCheck_8259_ == 0 {
                    v_unused_8260_ = crate::leanh::lean_ctor_get(v_l_8237_, 4);
                    crate::leanh::lean_dec(v_unused_8260_);
                    v_unused_8261_ = crate::leanh::lean_ctor_get(v_l_8237_, 3);
                    crate::leanh::lean_dec(v_unused_8261_);
                    v_unused_8262_ = crate::leanh::lean_ctor_get(v_l_8237_, 0);
                    crate::leanh::lean_dec(v_unused_8262_);
                    v___x_8247_ = v_l_8237_;
                    v_isShared_8248_ = v_isSharedCheck_8259_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_8245_);
                    crate::leanh::lean_inc(v_k_8244_);
                    crate::leanh::lean_dec(v_l_8237_);
                    v___x_8247_ = crate::leanh::lean_box(0);
                    v_isShared_8248_ = v_isSharedCheck_8259_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_8249_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_8238_, 2);
                if v_isShared_8248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8247_, 4, v_r_8238_);
                    crate::leanh::lean_ctor_set(v___x_8247_, 3, v_r_8238_);
                    crate::leanh::lean_ctor_set(v___x_8247_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v___x_8247_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v___x_8247_, 0, v___x_8153_);
                    v___x_8251_ = v___x_8247_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_8258_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8258_, 0, v___x_8153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8258_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8258_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8258_, 3, v_r_8238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8258_, 4, v_r_8238_);
                    v___x_8251_ = v_reuseFailAlloc_8258_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_8238_);
                if v_isShared_8243_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8242_, 3, v_r_8238_);
                    crate::leanh::lean_ctor_set(v___x_8242_, 0, v___x_8153_);
                    v___x_8253_ = v___x_8242_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_8257_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8257_, 0, v___x_8153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8257_, 1, v_k_8239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8257_, 2, v_v_8240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8257_, 3, v_r_8238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8257_, 4, v_r_8238_);
                    v___x_8253_ = v_reuseFailAlloc_8257_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_8009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8008_, 4, v___x_8253_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 3, v___x_8251_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 2, v_v_8245_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 1, v_k_8244_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8249_);
                    v___x_8255_ = v___x_8008_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_8256_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8256_, 0, v___x_8249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8256_, 1, v_k_8244_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8256_, 2, v_v_8245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8256_, 3, v___x_8251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8256_, 4, v___x_8253_);
                    v___x_8255_ = v_reuseFailAlloc_8256_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_8255_;
            }
            39 => {
                v___x_8272_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_8271_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8270_, 4, v_l_8237_);
                    crate::leanh::lean_ctor_set(v___x_8270_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v___x_8270_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v___x_8270_, 0, v___x_8153_);
                    v___x_8274_ = v___x_8270_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_8278_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8278_, 0, v___x_8153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8278_, 1, v_k_8003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8278_, 2, v_v_8004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8278_, 3, v_l_8237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8278_, 4, v_l_8237_);
                    v___x_8274_ = v_reuseFailAlloc_8278_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_8009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8008_, 4, v_r_8266_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 3, v___x_8274_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 2, v_v_8268_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 1, v_k_8267_);
                    crate::leanh::lean_ctor_set(v___x_8008_, 0, v___x_8272_);
                    v___x_8276_ = v___x_8008_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_8277_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8277_, 0, v___x_8272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8277_, 1, v_k_8267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8277_, 2, v_v_8268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8277_, 3, v___x_8274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8277_, 4, v_r_8266_);
                    v___x_8276_ = v_reuseFailAlloc_8277_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_8276_;
            }
            42 => {
                return v___x_8285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(
    mut v_cmp_8290_: *mut crate::leanh::LeanObject,
    mut v_init_8291_: *mut crate::leanh::LeanObject,
    mut v_x_8292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8292_) == 0 {
                    v_k_8293_ = crate::leanh::lean_ctor_get(v_x_8292_, 1);
                    crate::leanh::lean_inc(v_k_8293_);
                    v_v_8294_ = crate::leanh::lean_ctor_get(v_x_8292_, 2);
                    crate::leanh::lean_inc(v_v_8294_);
                    v_l_8295_ = crate::leanh::lean_ctor_get(v_x_8292_, 3);
                    crate::leanh::lean_inc(v_l_8295_);
                    v_r_8296_ = crate::leanh::lean_ctor_get(v_x_8292_, 4);
                    crate::leanh::lean_inc(v_r_8296_);
                    crate::leanh::lean_dec_ref_known(v_x_8292_, 5);
                    crate::leanh::lean_inc_ref_n(v_cmp_8290_, 2);
                    v___x_8297_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_8290_, v_init_8291_, v_l_8295_);
                    v_a_8298_ = crate::leanh::lean_ctor_get(v___x_8297_, 0);
                    crate::leanh::lean_inc(v_a_8298_);
                    crate::leanh::lean_dec_ref(v___x_8297_);
                    v_r_8299_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_8290_, v_k_8293_, v_v_8294_, v_a_8298_);
                    v_init_8291_ = v_r_8299_;
                    v_x_8292_ = v_r_8296_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_8290_);
                    v___x_8301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8301_, 0, v_init_8291_);
                    return v___x_8301_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(
    mut v_cmp_8302_: *mut crate::leanh::LeanObject,
    mut v_k_8303_: *mut crate::leanh::LeanObject,
    mut v_t_8304_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_8305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: u8 = 0;
    let mut v___x_8311_: u8 = 0;
    let mut v___x_8313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_8304_) == 0 {
                    v_k_8305_ = crate::leanh::lean_ctor_get(v_t_8304_, 1);
                    crate::leanh::lean_inc(v_k_8305_);
                    v_l_8306_ = crate::leanh::lean_ctor_get(v_t_8304_, 3);
                    crate::leanh::lean_inc(v_l_8306_);
                    v_r_8307_ = crate::leanh::lean_ctor_get(v_t_8304_, 4);
                    crate::leanh::lean_inc(v_r_8307_);
                    crate::leanh::lean_dec_ref_known(v_t_8304_, 5);
                    crate::leanh::lean_inc_ref(v_cmp_8302_);
                    crate::leanh::lean_inc(v_k_8303_);
                    v___x_8308_ = crate::leanh::lean_apply_2(v_cmp_8302_, v_k_8303_, v_k_8305_);
                    v___x_8309_ = (crate::leanh::lean_unbox(v___x_8308_) as u8);
                    match v___x_8309_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_8307_);
                            v_t_8304_ = v_l_8306_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_8307_);
                            crate::leanh::lean_dec(v_l_8306_);
                            crate::leanh::lean_dec(v_k_8303_);
                            crate::leanh::lean_dec_ref(v_cmp_8302_);
                            v___x_8311_ = 1;
                            return v___x_8311_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_8306_);
                            v_t_8304_ = v_r_8307_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_8303_);
                    crate::leanh::lean_dec_ref(v_cmp_8302_);
                    v___x_8313_ = 0;
                    return v___x_8313_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg___boxed(
    mut v_cmp_8314_: *mut crate::leanh::LeanObject,
    mut v_k_8315_: *mut crate::leanh::LeanObject,
    mut v_t_8316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8317_: u8 = 0;
    let mut v_r_8318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8317_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_8314_, v_k_8315_, v_t_8316_);
    v_r_8318_ = crate::leanh::lean_box((v_res_8317_) as usize);
    return v_r_8318_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(
    mut v_cmp_8319_: *mut crate::leanh::LeanObject,
    mut v_init_8320_: *mut crate::leanh::LeanObject,
    mut v_x_8321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8328_: u8 = 0;
    let mut v___x_8329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8321_) == 0 {
                    v_k_8322_ = crate::leanh::lean_ctor_get(v_x_8321_, 1);
                    crate::leanh::lean_inc_n(v_k_8322_, 2);
                    v_v_8323_ = crate::leanh::lean_ctor_get(v_x_8321_, 2);
                    crate::leanh::lean_inc(v_v_8323_);
                    v_l_8324_ = crate::leanh::lean_ctor_get(v_x_8321_, 3);
                    crate::leanh::lean_inc(v_l_8324_);
                    v_r_8325_ = crate::leanh::lean_ctor_get(v_x_8321_, 4);
                    crate::leanh::lean_inc(v_r_8325_);
                    crate::leanh::lean_dec_ref_known(v_x_8321_, 5);
                    crate::leanh::lean_inc_ref_n(v_cmp_8319_, 2);
                    v___x_8326_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_8319_, v_init_8320_, v_l_8324_);
                    v_a_8327_ = crate::leanh::lean_ctor_get(v___x_8326_, 0);
                    crate::leanh::lean_inc_n(v_a_8327_, 2);
                    crate::leanh::lean_dec_ref(v___x_8326_);
                    v___x_8328_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_8319_, v_k_8322_, v_a_8327_);
                    if v___x_8328_ == 0 {
                        crate::leanh::lean_inc_ref(v_cmp_8319_);
                        v___x_8329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_8319_, v_k_8322_, v_v_8323_, v_a_8327_);
                        v_init_8320_ = v___x_8329_;
                        v_x_8321_ = v_r_8325_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_8323_);
                        crate::leanh::lean_dec(v_k_8322_);
                        v_init_8320_ = v_a_8327_;
                        v_x_8321_ = v_r_8325_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_8319_);
                    v___x_8332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8332_, 0, v_init_8320_);
                    return v___x_8332_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
    mut v_cmp_8333_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8334_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8339_: u8 = 0;
    let mut v___x_8340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_u2081_8334_) == 0 {
                    v_size_8348_ = crate::leanh::lean_ctor_get(v_t_u2081_8334_, 0);
                    crate::leanh::lean_inc(v_size_8348_);
                    v___y_8345_ = v_size_8348_;
                    state = 2;
                    continue;
                } else {
                    v___x_8349_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8345_ = v___x_8349_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_8339_ = lean_nat_dec_le(v___y_8337_, v___y_8338_);
                crate::leanh::lean_dec(v___y_8338_);
                crate::leanh::lean_dec(v___y_8337_);
                if v___x_8339_ == 0 {
                    v___x_8340_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_8333_, v_t_u2081_8334_, v_t_u2082_8335_);
                    v_a_8341_ = crate::leanh::lean_ctor_get(v___x_8340_, 0);
                    crate::leanh::lean_inc(v_a_8341_);
                    crate::leanh::lean_dec_ref(v___x_8340_);
                    return v_a_8341_;
                } else {
                    v___x_8342_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_8333_, v_t_u2082_8335_, v_t_u2081_8334_);
                    v_a_8343_ = crate::leanh::lean_ctor_get(v___x_8342_, 0);
                    crate::leanh::lean_inc(v_a_8343_);
                    crate::leanh::lean_dec_ref(v___x_8342_);
                    return v_a_8343_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_t_u2082_8335_) == 0 {
                    v_size_8346_ = crate::leanh::lean_ctor_get(v_t_u2082_8335_, 0);
                    crate::leanh::lean_inc(v_size_8346_);
                    v___y_8337_ = v___y_8345_;
                    v___y_8338_ = v_size_8346_;
                    state = 1;
                    continue;
                } else {
                    v___x_8347_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8337_ = v___y_8345_;
                    v___y_8338_ = v___x_8347_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_union___redArg(
    mut v_cmp_8350_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8351_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8353_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_8350_,
        v_t_u2081_8351_,
        v_t_u2082_8352_,
    );
    return v___x_8353_;
}
pub unsafe fn l_Std_DTreeMap_union(
    mut v_00_u03b1_8354_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8355_: *mut crate::leanh::LeanObject,
    mut v_cmp_8356_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8357_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8359_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_8356_,
        v_t_u2081_8357_,
        v_t_u2082_8358_,
    );
    return v___x_8359_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0(
    mut v_00_u03b1_8360_: *mut crate::leanh::LeanObject,
    mut v_cmp_8361_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8362_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8363_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8364_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_8365_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_8366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8367_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_8361_,
        v_t_u2081_8363_,
        v_t_u2082_8364_,
    );
    return v___x_8367_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(
    mut v_00_u03b1_8368_: *mut crate::leanh::LeanObject,
    mut v_cmp_8369_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8370_: *mut crate::leanh::LeanObject,
    mut v_k_8371_: *mut crate::leanh::LeanObject,
    mut v_t_8372_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8373_: u8 = 0;
    v___x_8373_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_8369_, v_k_8371_, v_t_8372_);
    return v___x_8373_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___boxed(
    mut v_00_u03b1_8374_: *mut crate::leanh::LeanObject,
    mut v_cmp_8375_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8376_: *mut crate::leanh::LeanObject,
    mut v_k_8377_: *mut crate::leanh::LeanObject,
    mut v_t_8378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8379_: u8 = 0;
    let mut v_r_8380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8379_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0(v_00_u03b1_8374_, v_cmp_8375_, v_00_u03b2_8376_, v_k_8377_, v_t_8378_);
    v_r_8380_ = crate::leanh::lean_box((v_res_8379_) as usize);
    return v_r_8380_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1(
    mut v_00_u03b1_8381_: *mut crate::leanh::LeanObject,
    mut v_cmp_8382_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8383_: *mut crate::leanh::LeanObject,
    mut v_k_8384_: *mut crate::leanh::LeanObject,
    mut v_v_8385_: *mut crate::leanh::LeanObject,
    mut v_t_8386_: *mut crate::leanh::LeanObject,
    mut v_hl_8387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_8382_, v_k_8384_, v_v_8385_, v_t_8386_);
    return v___x_8388_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2(
    mut v_00_u03b1_8389_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8390_: *mut crate::leanh::LeanObject,
    mut v_cmp_8391_: *mut crate::leanh::LeanObject,
    mut v_init_8392_: *mut crate::leanh::LeanObject,
    mut v_x_8393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8394_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__2___redArg(v_cmp_8391_, v_init_8392_, v_x_8393_);
    return v___x_8394_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3(
    mut v_00_u03b1_8395_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8396_: *mut crate::leanh::LeanObject,
    mut v_cmp_8397_: *mut crate::leanh::LeanObject,
    mut v_init_8398_: *mut crate::leanh::LeanObject,
    mut v_x_8399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8400_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__3___redArg(v_cmp_8397_, v_init_8398_, v_x_8399_);
    return v___x_8400_;
}
pub unsafe fn l_Std_DTreeMap_instUnion___redArg(
    mut v_cmp_8401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8402_ =
        crate::leanh::lean_alloc_closure(l_Std_DTreeMap_union as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_8402_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8402_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8402_, 2, v_cmp_8401_);
    return v___x_8402_;
}
pub unsafe fn l_Std_DTreeMap_instUnion(
    mut v_00_u03b1_8403_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8404_: *mut crate::leanh::LeanObject,
    mut v_cmp_8405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8406_ =
        crate::leanh::lean_alloc_closure(l_Std_DTreeMap_union as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_8406_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8406_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8406_, 2, v_cmp_8405_);
    return v___x_8406_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(
    mut v_cmp_8407_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_8408_: *mut crate::leanh::LeanObject,
    mut v_t_8409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_8409_) == 0 {
        let mut v_k_8410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_8411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_8412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_8413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8414_: u8 = 0;
        v_k_8410_ = crate::leanh::lean_ctor_get(v_t_8409_, 1);
        crate::leanh::lean_inc_n(v_k_8410_, 2);
        v_v_8411_ = crate::leanh::lean_ctor_get(v_t_8409_, 2);
        crate::leanh::lean_inc(v_v_8411_);
        v_l_8412_ = crate::leanh::lean_ctor_get(v_t_8409_, 3);
        crate::leanh::lean_inc(v_l_8412_);
        v_r_8413_ = crate::leanh::lean_ctor_get(v_t_8409_, 4);
        crate::leanh::lean_inc(v_r_8413_);
        crate::leanh::lean_dec_ref_known(v_t_8409_, 5);
        crate::leanh::lean_inc(v_m_u2082_8408_);
        crate::leanh::lean_inc_ref(v_cmp_8407_);
        v___x_8414_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_8407_, v_k_8410_, v_m_u2082_8408_);
        if v___x_8414_ == 0 {
            let mut v_impl_8415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_impl_8416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_v_8411_);
            crate::leanh::lean_dec(v_k_8410_);
            crate::leanh::lean_inc(v_m_u2082_8408_);
            crate::leanh::lean_inc_ref(v_cmp_8407_);
            v_impl_8415_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_8407_, v_m_u2082_8408_, v_l_8412_);
            v_impl_8416_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_8407_, v_m_u2082_8408_, v_r_8413_);
            v___x_8417_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_8415_, v_impl_8416_);
            return v___x_8417_;
        } else {
            let mut v_impl_8418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_impl_8419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_m_u2082_8408_);
            crate::leanh::lean_inc_ref(v_cmp_8407_);
            v_impl_8418_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_8407_, v_m_u2082_8408_, v_l_8412_);
            v_impl_8419_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_8407_, v_m_u2082_8408_, v_r_8413_);
            v___x_8420_ = l_Std_DTreeMap_Internal_Impl_link___redArg(
                v_k_8410_,
                v_v_8411_,
                v_impl_8418_,
                v_impl_8419_,
            );
            return v___x_8420_;
        }
    } else {
        crate::leanh::lean_dec(v_m_u2082_8408_);
        crate::leanh::lean_dec_ref(v_cmp_8407_);
        return v_t_8409_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(
    mut v_cmp_8421_: *mut crate::leanh::LeanObject,
    mut v_t_8422_: *mut crate::leanh::LeanObject,
    mut v_k_8423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8429_: u8 = 0;
    let mut v___x_8431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_8422_) == 0 {
                    v_k_8424_ = crate::leanh::lean_ctor_get(v_t_8422_, 1);
                    crate::leanh::lean_inc_n(v_k_8424_, 2);
                    v_v_8425_ = crate::leanh::lean_ctor_get(v_t_8422_, 2);
                    crate::leanh::lean_inc(v_v_8425_);
                    v_l_8426_ = crate::leanh::lean_ctor_get(v_t_8422_, 3);
                    crate::leanh::lean_inc(v_l_8426_);
                    v_r_8427_ = crate::leanh::lean_ctor_get(v_t_8422_, 4);
                    crate::leanh::lean_inc(v_r_8427_);
                    crate::leanh::lean_dec_ref_known(v_t_8422_, 5);
                    crate::leanh::lean_inc_ref(v_cmp_8421_);
                    crate::leanh::lean_inc(v_k_8423_);
                    v___x_8428_ = crate::leanh::lean_apply_2(v_cmp_8421_, v_k_8423_, v_k_8424_);
                    v___x_8429_ = (crate::leanh::lean_unbox(v___x_8428_) as u8);
                    match v___x_8429_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_8427_);
                            crate::leanh::lean_dec(v_v_8425_);
                            crate::leanh::lean_dec(v_k_8424_);
                            v_t_8422_ = v_l_8426_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_8427_);
                            crate::leanh::lean_dec(v_l_8426_);
                            crate::leanh::lean_dec(v_k_8423_);
                            crate::leanh::lean_dec_ref(v_cmp_8421_);
                            v___x_8431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8431_, 0, v_k_8424_);
                            crate::leanh::lean_ctor_set(v___x_8431_, 1, v_v_8425_);
                            v___x_8432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8432_, 0, v___x_8431_);
                            return v___x_8432_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_8426_);
                            crate::leanh::lean_dec(v_v_8425_);
                            crate::leanh::lean_dec(v_k_8424_);
                            v_t_8422_ = v_r_8427_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_8423_);
                    crate::leanh::lean_dec_ref(v_cmp_8421_);
                    v___x_8434_ = crate::leanh::lean_box(0);
                    return v___x_8434_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_cmp_8435_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8436_: *mut crate::leanh::LeanObject,
    mut v_init_8437_: *mut crate::leanh::LeanObject,
    mut v_x_8438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_8448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8438_) == 0 {
                    v_k_8439_ = crate::leanh::lean_ctor_get(v_x_8438_, 1);
                    crate::leanh::lean_inc(v_k_8439_);
                    v_l_8440_ = crate::leanh::lean_ctor_get(v_x_8438_, 3);
                    crate::leanh::lean_inc(v_l_8440_);
                    v_r_8441_ = crate::leanh::lean_ctor_get(v_x_8438_, 4);
                    crate::leanh::lean_inc(v_r_8441_);
                    crate::leanh::lean_dec_ref_known(v_x_8438_, 5);
                    crate::leanh::lean_inc_n(v_m_u2081_8436_, 2);
                    crate::leanh::lean_inc_ref_n(v_cmp_8435_, 2);
                    v___x_8442_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_8435_, v_m_u2081_8436_, v_init_8437_, v_l_8440_);
                    v___x_8443_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_8435_, v_m_u2081_8436_, v_k_8439_);
                    if crate::leanh::lean_obj_tag(v___x_8443_) == 0 {
                        v_init_8437_ = v___x_8442_;
                        v_x_8438_ = v_r_8441_;
                        state = 0;
                        continue;
                    } else {
                        v_val_8445_ = crate::leanh::lean_ctor_get(v___x_8443_, 0);
                        crate::leanh::lean_inc(v_val_8445_);
                        crate::leanh::lean_dec_ref_known(v___x_8443_, 1);
                        v_fst_8446_ = crate::leanh::lean_ctor_get(v_val_8445_, 0);
                        crate::leanh::lean_inc(v_fst_8446_);
                        v_snd_8447_ = crate::leanh::lean_ctor_get(v_val_8445_, 1);
                        crate::leanh::lean_inc(v_snd_8447_);
                        crate::leanh::lean_dec(v_val_8445_);
                        crate::leanh::lean_inc_ref(v_cmp_8435_);
                        v_impl_8448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__1___redArg(v_cmp_8435_, v_fst_8446_, v_snd_8447_, v___x_8442_);
                        v_init_8437_ = v_impl_8448_;
                        v_x_8438_ = v_r_8441_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_m_u2081_8436_);
                    crate::leanh::lean_dec_ref(v_cmp_8435_);
                    return v_init_8437_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(
    mut v_cmp_8450_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8451_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_8452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8453_ = crate::leanh::lean_box(1);
    v___x_8454_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_8450_, v_m_u2081_8451_, v___x_8453_, v_m_u2082_8452_);
    return v___x_8454_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
    mut v_cmp_8455_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8456_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_8457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8461_: u8 = 0;
    let mut v___x_8462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_u2081_8456_) == 0 {
                    v_size_8468_ = crate::leanh::lean_ctor_get(v_m_u2081_8456_, 0);
                    crate::leanh::lean_inc(v_size_8468_);
                    v___y_8465_ = v_size_8468_;
                    state = 2;
                    continue;
                } else {
                    v___x_8469_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8465_ = v___x_8469_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_8461_ = lean_nat_dec_le(v___y_8459_, v___y_8460_);
                crate::leanh::lean_dec(v___y_8460_);
                crate::leanh::lean_dec(v___y_8459_);
                if v___x_8461_ == 0 {
                    v___x_8462_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_8455_, v_m_u2081_8456_, v_m_u2082_8457_);
                    return v___x_8462_;
                } else {
                    v___x_8463_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_8455_, v_m_u2082_8457_, v_m_u2081_8456_);
                    return v___x_8463_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_m_u2082_8457_) == 0 {
                    v_size_8466_ = crate::leanh::lean_ctor_get(v_m_u2082_8457_, 0);
                    crate::leanh::lean_inc(v_size_8466_);
                    v___y_8459_ = v___y_8465_;
                    v___y_8460_ = v_size_8466_;
                    state = 1;
                    continue;
                } else {
                    v___x_8467_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8459_ = v___y_8465_;
                    v___y_8460_ = v___x_8467_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_inter___redArg(
    mut v_cmp_8470_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8471_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8473_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_8470_,
        v_t_u2081_8471_,
        v_t_u2082_8472_,
    );
    return v___x_8473_;
}
pub unsafe fn l_Std_DTreeMap_inter(
    mut v_00_u03b1_8474_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8475_: *mut crate::leanh::LeanObject,
    mut v_cmp_8476_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8477_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8479_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_8476_,
        v_t_u2081_8477_,
        v_t_u2082_8478_,
    );
    return v___x_8479_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0(
    mut v_00_u03b1_8480_: *mut crate::leanh::LeanObject,
    mut v_cmp_8481_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8482_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8483_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_8484_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_8485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8486_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_8481_,
        v_m_u2081_8483_,
        v_m_u2082_8484_,
    );
    return v___x_8486_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0(
    mut v_00_u03b1_8487_: *mut crate::leanh::LeanObject,
    mut v_cmp_8488_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8489_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8490_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_8491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8492_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0___redArg(v_cmp_8488_, v_m_u2081_8490_, v_m_u2082_8491_);
    return v___x_8492_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1(
    mut v_00_u03b1_8493_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8494_: *mut crate::leanh::LeanObject,
    mut v_cmp_8495_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_8496_: *mut crate::leanh::LeanObject,
    mut v_t_8497_: *mut crate::leanh::LeanObject,
    mut v_hl_8498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8499_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__1___redArg(v_cmp_8495_, v_m_u2082_8496_, v_t_8497_);
    return v___x_8499_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1(
    mut v_00_u03b1_8500_: *mut crate::leanh::LeanObject,
    mut v_cmp_8501_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8502_: *mut crate::leanh::LeanObject,
    mut v_t_8503_: *mut crate::leanh::LeanObject,
    mut v_k_8504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8505_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__1___redArg(v_cmp_8501_, v_t_8503_, v_k_8504_);
    return v___x_8505_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2___redArg(
    mut v_cmp_8506_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8507_: *mut crate::leanh::LeanObject,
    mut v_init_8508_: *mut crate::leanh::LeanObject,
    mut v_t_8509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8510_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_8506_, v_m_u2081_8507_, v_init_8508_, v_t_8509_);
    return v___x_8510_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2(
    mut v_00_u03b1_8511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8512_: *mut crate::leanh::LeanObject,
    mut v_cmp_8513_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8514_: *mut crate::leanh::LeanObject,
    mut v_init_8515_: *mut crate::leanh::LeanObject,
    mut v_t_8516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8517_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_8513_, v_m_u2081_8514_, v_init_8515_, v_t_8516_);
    return v___x_8517_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b1_8518_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8519_: *mut crate::leanh::LeanObject,
    mut v_cmp_8520_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_8521_: *mut crate::leanh::LeanObject,
    mut v_init_8522_: *mut crate::leanh::LeanObject,
    mut v_x_8523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8524_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0_spec__0_spec__2_spec__3___redArg(v_cmp_8520_, v_m_u2081_8521_, v_init_8522_, v_x_8523_);
    return v___x_8524_;
}
pub unsafe fn l_Std_DTreeMap_instInter___redArg(
    mut v_cmp_8525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8526_ =
        crate::leanh::lean_alloc_closure(l_Std_DTreeMap_inter as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_8526_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8526_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8526_, 2, v_cmp_8525_);
    return v___x_8526_;
}
pub unsafe fn l_Std_DTreeMap_instInter(
    mut v_00_u03b1_8527_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8528_: *mut crate::leanh::LeanObject,
    mut v_cmp_8529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8530_ =
        crate::leanh::lean_alloc_closure(l_Std_DTreeMap_inter as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_8530_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8530_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8530_, 2, v_cmp_8529_);
    return v___x_8530_;
}
pub unsafe fn l_Std_DTreeMap_beq___redArg(
    mut v_cmp_8531_: *mut crate::leanh::LeanObject,
    mut v_inst_8532_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8533_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8534_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8535_: u8 = 0;
    v___x_8535_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_8531_,
        v_inst_8532_,
        v_t_u2081_8533_,
        v_t_u2082_8534_,
    );
    return v___x_8535_;
}
pub unsafe fn l_Std_DTreeMap_beq___redArg___boxed(
    mut v_cmp_8536_: *mut crate::leanh::LeanObject,
    mut v_inst_8537_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8538_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8540_: u8 = 0;
    let mut v_r_8541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8540_ =
        l_Std_DTreeMap_beq___redArg(v_cmp_8536_, v_inst_8537_, v_t_u2081_8538_, v_t_u2082_8539_);
    v_r_8541_ = crate::leanh::lean_box((v_res_8540_) as usize);
    return v_r_8541_;
}
pub unsafe fn l_Std_DTreeMap_beq(
    mut v_00_u03b1_8542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8543_: *mut crate::leanh::LeanObject,
    mut v_cmp_8544_: *mut crate::leanh::LeanObject,
    mut v_inst_8545_: *mut crate::leanh::LeanObject,
    mut v_inst_8546_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8547_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8548_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8549_: u8 = 0;
    v___x_8549_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(
        v_cmp_8544_,
        v_inst_8546_,
        v_t_u2081_8547_,
        v_t_u2082_8548_,
    );
    return v___x_8549_;
}
pub unsafe fn l_Std_DTreeMap_beq___boxed(
    mut v_00_u03b1_8550_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8551_: *mut crate::leanh::LeanObject,
    mut v_cmp_8552_: *mut crate::leanh::LeanObject,
    mut v_inst_8553_: *mut crate::leanh::LeanObject,
    mut v_inst_8554_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8555_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8557_: u8 = 0;
    let mut v_r_8558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8557_ = l_Std_DTreeMap_beq(
        v_00_u03b1_8550_,
        v_00_u03b2_8551_,
        v_cmp_8552_,
        v_inst_8553_,
        v_inst_8554_,
        v_t_u2081_8555_,
        v_t_u2082_8556_,
    );
    v_r_8558_ = crate::leanh::lean_box((v_res_8557_) as usize);
    return v_r_8558_;
}
pub unsafe fn l_Std_DTreeMap_instBEqOfLawfulEqCmp___redArg(
    mut v_cmp_8559_: *mut crate::leanh::LeanObject,
    mut v_inst_8560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8561_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_beq___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___x_8561_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8561_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8561_, 2, v_cmp_8559_);
    crate::leanh::lean_closure_set(v___x_8561_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8561_, 4, v_inst_8560_);
    return v___x_8561_;
}
pub unsafe fn l_Std_DTreeMap_instBEqOfLawfulEqCmp(
    mut v_00_u03b1_8562_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8563_: *mut crate::leanh::LeanObject,
    mut v_cmp_8564_: *mut crate::leanh::LeanObject,
    mut v_inst_8565_: *mut crate::leanh::LeanObject,
    mut v_inst_8566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8567_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_beq___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___x_8567_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8567_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8567_, 2, v_cmp_8564_);
    crate::leanh::lean_closure_set(v___x_8567_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_8567_, 4, v_inst_8566_);
    return v___x_8567_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___redArg(
    mut v_cmp_8568_: *mut crate::leanh::LeanObject,
    mut v_inst_8569_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8570_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8571_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8572_: u8 = 0;
    v___x_8572_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_8568_,
        v_inst_8569_,
        v_t_u2081_8570_,
        v_t_u2082_8571_,
    );
    return v___x_8572_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___redArg___boxed(
    mut v_cmp_8573_: *mut crate::leanh::LeanObject,
    mut v_inst_8574_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8575_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8577_: u8 = 0;
    let mut v_r_8578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8577_ = l_Std_DTreeMap_Const_beq___redArg(
        v_cmp_8573_,
        v_inst_8574_,
        v_t_u2081_8575_,
        v_t_u2082_8576_,
    );
    v_r_8578_ = crate::leanh::lean_box((v_res_8577_) as usize);
    return v_r_8578_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq(
    mut v_00_u03b1_8579_: *mut crate::leanh::LeanObject,
    mut v_cmp_8580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8581_: *mut crate::leanh::LeanObject,
    mut v_inst_8582_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8583_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8584_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_8585_: u8 = 0;
    v___x_8585_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_8580_,
        v_inst_8582_,
        v_t_u2081_8583_,
        v_t_u2082_8584_,
    );
    return v___x_8585_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___boxed(
    mut v_00_u03b1_8586_: *mut crate::leanh::LeanObject,
    mut v_cmp_8587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8588_: *mut crate::leanh::LeanObject,
    mut v_inst_8589_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_8590_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_8591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8592_: u8 = 0;
    let mut v_r_8593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8592_ = l_Std_DTreeMap_Const_beq(
        v_00_u03b1_8586_,
        v_cmp_8587_,
        v_00_u03b2_8588_,
        v_inst_8589_,
        v_t_u2081_8590_,
        v_t_u2082_8591_,
    );
    v_r_8593_ = crate::leanh::lean_box((v_res_8592_) as usize);
    return v_r_8593_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(
    mut v_cmp_8594_: *mut crate::leanh::LeanObject,
    mut v_k_8595_: *mut crate::leanh::LeanObject,
    mut v_t_8596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8603_: u8 = 0;
    let mut v___x_8604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8605_: u8 = 0;
    let mut v_impl_8606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8616_: u8 = 0;
    let mut v___x_8617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8624_: u8 = 0;
    let mut v_size_8625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8633_: u8 = 0;
    let mut v___x_8635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8636_: u8 = 0;
    let mut v___x_8637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8661_: u8 = 0;
    let mut v_unused_8662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8674_: u8 = 0;
    let mut v___x_8676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8678_: u8 = 0;
    let mut v_unused_8679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8685_: u8 = 0;
    let mut v_unused_8686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8703_: u8 = 0;
    let mut v_size_8704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8713_: u8 = 0;
    let mut v_unused_8714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8720_: u8 = 0;
    let mut v_k_8721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8725_: u8 = 0;
    let mut v___x_8726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8736_: u8 = 0;
    let mut v_unused_8737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8740_: u8 = 0;
    let mut v_unused_8741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8749_: u8 = 0;
    let mut v___x_8750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8757_: u8 = 0;
    let mut v_unused_8758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8766_: u8 = 0;
    let mut v___x_8768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8774_: u8 = 0;
    let mut v_unused_8775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8791_: u8 = 0;
    let mut v___x_8793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8794_: u8 = 0;
    let mut v___x_8795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_8796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8802_: u8 = 0;
    let mut v___x_8803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8810_: u8 = 0;
    let mut v_size_8811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8819_: u8 = 0;
    let mut v___x_8821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8822_: u8 = 0;
    let mut v___x_8823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8847_: u8 = 0;
    let mut v_unused_8848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8862_: u8 = 0;
    let mut v_unused_8863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8870_: u8 = 0;
    let mut v_k_8871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8888_: u8 = 0;
    let mut v___x_8889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8899_: u8 = 0;
    let mut v_unused_8900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8921_: u8 = 0;
    let mut v_unused_8922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8927_: u8 = 0;
    let mut v_unused_8928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8935_: u8 = 0;
    let mut v___x_8936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_8937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8943_: u8 = 0;
    let mut v___x_8944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8951_: u8 = 0;
    let mut v_size_8952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8960_: u8 = 0;
    let mut v___x_8962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8963_: u8 = 0;
    let mut v___x_8964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8975_: u8 = 0;
    let mut v___x_8977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8979_: u8 = 0;
    let mut v_unused_8980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8998_: u8 = 0;
    let mut v_unused_8999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9014_: u8 = 0;
    let mut v_unused_9015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9022_: u8 = 0;
    let mut v_k_9023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9043_: u8 = 0;
    let mut v_unused_9044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9051_: u8 = 0;
    let mut v_k_9052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9058_: u8 = 0;
    let mut v___x_9059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9069_: u8 = 0;
    let mut v_unused_9070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9073_: u8 = 0;
    let mut v_unused_9074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9085_: u8 = 0;
    let mut v_unused_9086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_9091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_9097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_9098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9101_: u8 = 0;
    let mut v___x_9102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9109_: u8 = 0;
    let mut v_size_9110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_9114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_9115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9118_: u8 = 0;
    let mut v___x_9120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9121_: u8 = 0;
    let mut v___x_9122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9147_: u8 = 0;
    let mut v_unused_9148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9161_: u8 = 0;
    let mut v___x_9163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9165_: u8 = 0;
    let mut v_unused_9166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9172_: u8 = 0;
    let mut v_unused_9173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_9183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_9184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9190_: u8 = 0;
    let mut v_size_9191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9200_: u8 = 0;
    let mut v_unused_9201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9207_: u8 = 0;
    let mut v___x_9208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9215_: u8 = 0;
    let mut v_unused_9216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_9219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9224_: u8 = 0;
    let mut v_k_9225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9229_: u8 = 0;
    let mut v___x_9230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9240_: u8 = 0;
    let mut v_unused_9241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9244_: u8 = 0;
    let mut v_unused_9245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9255_: u8 = 0;
    let mut v_unused_9256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_8596_) == 0 {
                    v_k_8597_ = crate::leanh::lean_ctor_get(v_t_8596_, 1);
                    v_v_8598_ = crate::leanh::lean_ctor_get(v_t_8596_, 2);
                    v_l_8599_ = crate::leanh::lean_ctor_get(v_t_8596_, 3);
                    v_r_8600_ = crate::leanh::lean_ctor_get(v_t_8596_, 4);
                    v_isSharedCheck_9255_ = (!crate::leanh::lean_is_exclusive(v_t_8596_)) as u8;
                    if v_isSharedCheck_9255_ == 0 {
                        v_unused_9256_ = crate::leanh::lean_ctor_get(v_t_8596_, 0);
                        crate::leanh::lean_dec(v_unused_9256_);
                        v___x_8602_ = v_t_8596_;
                        v_isShared_8603_ = v_isSharedCheck_9255_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_8600_);
                        crate::leanh::lean_inc(v_l_8599_);
                        crate::leanh::lean_inc(v_v_8598_);
                        crate::leanh::lean_inc(v_k_8597_);
                        crate::leanh::lean_dec(v_t_8596_);
                        v___x_8602_ = crate::leanh::lean_box(0);
                        v_isShared_8603_ = v_isSharedCheck_9255_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_8595_);
                    crate::leanh::lean_dec_ref(v_cmp_8594_);
                    return v_t_8596_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_8594_);
                crate::leanh::lean_inc(v_k_8597_);
                crate::leanh::lean_inc(v_k_8595_);
                v___x_8604_ = crate::leanh::lean_apply_2(v_cmp_8594_, v_k_8595_, v_k_8597_);
                v___x_8605_ = (crate::leanh::lean_unbox(v___x_8604_) as u8);
                match v___x_8605_ {
                    0 => {
                        v_impl_8606_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_8594_, v_k_8595_, v_l_8599_);
                        v___x_8607_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_8606_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_8600_) == 0 {
                                v_size_8608_ = crate::leanh::lean_ctor_get(v_impl_8606_, 0);
                                crate::leanh::lean_inc(v_size_8608_);
                                v_size_8609_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                v_k_8610_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                v_v_8611_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                v_l_8612_ = crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                crate::leanh::lean_inc(v_l_8612_);
                                v_r_8613_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                v___x_8614_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_8615_ = lean_nat_mul(v___x_8614_, v_size_8608_);
                                v___x_8616_ = lean_nat_dec_lt(v___x_8615_, v_size_8609_);
                                crate::leanh::lean_dec(v___x_8615_);
                                if v___x_8616_ == 0 {
                                    crate::leanh::lean_dec(v_l_8612_);
                                    v___x_8617_ = lean_nat_add(v___x_8607_, v_size_8608_);
                                    crate::leanh::lean_dec(v_size_8608_);
                                    v___x_8618_ = lean_nat_add(v___x_8617_, v_size_8609_);
                                    crate::leanh::lean_dec(v___x_8617_);
                                    if v_isShared_8603_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_8602_, 3, v_impl_8606_);
                                        crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8618_);
                                        v___x_8620_ = v___x_8602_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_8621_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8621_,
                                            0,
                                            v___x_8618_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8621_,
                                            1,
                                            v_k_8597_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8621_,
                                            2,
                                            v_v_8598_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8621_,
                                            3,
                                            v_impl_8606_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8621_,
                                            4,
                                            v_r_8600_,
                                        );
                                        v___x_8620_ = v_reuseFailAlloc_8621_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_8613_);
                                    crate::leanh::lean_inc(v_v_8611_);
                                    crate::leanh::lean_inc(v_k_8610_);
                                    crate::leanh::lean_inc(v_size_8609_);
                                    v_isSharedCheck_8685_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                                    if v_isSharedCheck_8685_ == 0 {
                                        v_unused_8686_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                        crate::leanh::lean_dec(v_unused_8686_);
                                        v_unused_8687_ = crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                        crate::leanh::lean_dec(v_unused_8687_);
                                        v_unused_8688_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                        crate::leanh::lean_dec(v_unused_8688_);
                                        v_unused_8689_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                        crate::leanh::lean_dec(v_unused_8689_);
                                        v_unused_8690_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                        crate::leanh::lean_dec(v_unused_8690_);
                                        v___x_8623_ = v_r_8600_;
                                        v_isShared_8624_ = v_isSharedCheck_8685_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_8600_);
                                        v___x_8623_ = crate::leanh::lean_box(0);
                                        v_isShared_8624_ = v_isSharedCheck_8685_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_8691_ = crate::leanh::lean_ctor_get(v_impl_8606_, 0);
                                crate::leanh::lean_inc(v_size_8691_);
                                v___x_8692_ = lean_nat_add(v___x_8607_, v_size_8691_);
                                crate::leanh::lean_dec(v_size_8691_);
                                if v_isShared_8603_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v_impl_8606_);
                                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8692_);
                                    v___x_8694_ = v___x_8602_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_8695_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8695_,
                                        0,
                                        v___x_8692_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8695_,
                                        1,
                                        v_k_8597_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8695_,
                                        2,
                                        v_v_8598_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8695_,
                                        3,
                                        v_impl_8606_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8695_,
                                        4,
                                        v_r_8600_,
                                    );
                                    v___x_8694_ = v_reuseFailAlloc_8695_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_r_8600_) == 0 {
                                v_l_8696_ = crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                crate::leanh::lean_inc(v_l_8696_);
                                if crate::leanh::lean_obj_tag(v_l_8696_) == 0 {
                                    v_r_8697_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                    crate::leanh::lean_inc(v_r_8697_);
                                    if crate::leanh::lean_obj_tag(v_r_8697_) == 0 {
                                        v_size_8698_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                        v_k_8699_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                        v_v_8700_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                        v_isSharedCheck_8713_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                                        if v_isSharedCheck_8713_ == 0 {
                                            v_unused_8714_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                            crate::leanh::lean_dec(v_unused_8714_);
                                            v_unused_8715_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                            crate::leanh::lean_dec(v_unused_8715_);
                                            v___x_8702_ = v_r_8600_;
                                            v_isShared_8703_ = v_isSharedCheck_8713_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_8700_);
                                            crate::leanh::lean_inc(v_k_8699_);
                                            crate::leanh::lean_inc(v_size_8698_);
                                            crate::leanh::lean_dec(v_r_8600_);
                                            v___x_8702_ = crate::leanh::lean_box(0);
                                            v_isShared_8703_ = v_isSharedCheck_8713_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_8716_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                        v_v_8717_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                        v_isSharedCheck_8740_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                                        if v_isSharedCheck_8740_ == 0 {
                                            v_unused_8741_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                            crate::leanh::lean_dec(v_unused_8741_);
                                            v_unused_8742_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                            crate::leanh::lean_dec(v_unused_8742_);
                                            v_unused_8743_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                            crate::leanh::lean_dec(v_unused_8743_);
                                            v___x_8719_ = v_r_8600_;
                                            v_isShared_8720_ = v_isSharedCheck_8740_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_8717_);
                                            crate::leanh::lean_inc(v_k_8716_);
                                            crate::leanh::lean_dec(v_r_8600_);
                                            v___x_8719_ = crate::leanh::lean_box(0);
                                            v_isShared_8720_ = v_isSharedCheck_8740_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_8744_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                    crate::leanh::lean_inc(v_r_8744_);
                                    if crate::leanh::lean_obj_tag(v_r_8744_) == 0 {
                                        v_k_8745_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                        v_v_8746_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                        v_isSharedCheck_8757_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                                        if v_isSharedCheck_8757_ == 0 {
                                            v_unused_8758_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                            crate::leanh::lean_dec(v_unused_8758_);
                                            v_unused_8759_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                            crate::leanh::lean_dec(v_unused_8759_);
                                            v_unused_8760_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                            crate::leanh::lean_dec(v_unused_8760_);
                                            v___x_8748_ = v_r_8600_;
                                            v_isShared_8749_ = v_isSharedCheck_8757_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_8746_);
                                            crate::leanh::lean_inc(v_k_8745_);
                                            crate::leanh::lean_dec(v_r_8600_);
                                            v___x_8748_ = crate::leanh::lean_box(0);
                                            v_isShared_8749_ = v_isSharedCheck_8757_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_8761_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                        v_k_8762_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                        v_v_8763_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                        v_isSharedCheck_8774_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                                        if v_isSharedCheck_8774_ == 0 {
                                            v_unused_8775_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                            crate::leanh::lean_dec(v_unused_8775_);
                                            v_unused_8776_ =
                                                crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                            crate::leanh::lean_dec(v_unused_8776_);
                                            v___x_8765_ = v_r_8600_;
                                            v_isShared_8766_ = v_isSharedCheck_8774_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_8763_);
                                            crate::leanh::lean_inc(v_k_8762_);
                                            crate::leanh::lean_inc(v_size_8761_);
                                            crate::leanh::lean_dec(v_r_8600_);
                                            v___x_8765_ = crate::leanh::lean_box(0);
                                            v_isShared_8766_ = v_isSharedCheck_8774_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_8603_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v_r_8600_);
                                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8607_);
                                    v___x_8778_ = v___x_8602_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_8779_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8779_,
                                        0,
                                        v___x_8607_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8779_,
                                        1,
                                        v_k_8597_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8779_,
                                        2,
                                        v_v_8598_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8779_,
                                        3,
                                        v_r_8600_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_8779_,
                                        4,
                                        v_r_8600_,
                                    );
                                    v___x_8778_ = v_reuseFailAlloc_8779_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_8602_);
                        crate::leanh::lean_dec(v_v_8598_);
                        crate::leanh::lean_dec(v_k_8597_);
                        crate::leanh::lean_dec(v_k_8595_);
                        crate::leanh::lean_dec_ref(v_cmp_8594_);
                        if crate::leanh::lean_obj_tag(v_l_8599_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_8600_) == 0 {
                                v_size_8780_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                v_k_8781_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                v_v_8782_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                v_l_8783_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                v_r_8784_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                crate::leanh::lean_inc(v_r_8784_);
                                v_size_8785_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                v_k_8786_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                v_v_8787_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                v_l_8788_ = crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                crate::leanh::lean_inc(v_l_8788_);
                                v_r_8789_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                v___x_8790_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_8791_ = lean_nat_dec_lt(v_size_8780_, v_size_8785_);
                                if v___x_8791_ == 0 {
                                    crate::leanh::lean_inc(v_l_8783_);
                                    crate::leanh::lean_inc(v_v_8782_);
                                    crate::leanh::lean_inc(v_k_8781_);
                                    v_isSharedCheck_8927_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                                    if v_isSharedCheck_8927_ == 0 {
                                        v_unused_8928_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                        crate::leanh::lean_dec(v_unused_8928_);
                                        v_unused_8929_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                        crate::leanh::lean_dec(v_unused_8929_);
                                        v_unused_8930_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                        crate::leanh::lean_dec(v_unused_8930_);
                                        v_unused_8931_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                        crate::leanh::lean_dec(v_unused_8931_);
                                        v_unused_8932_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                        crate::leanh::lean_dec(v_unused_8932_);
                                        v___x_8793_ = v_l_8599_;
                                        v_isShared_8794_ = v_isSharedCheck_8927_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_8599_);
                                        v___x_8793_ = crate::leanh::lean_box(0);
                                        v_isShared_8794_ = v_isSharedCheck_8927_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_8789_);
                                    crate::leanh::lean_inc(v_v_8787_);
                                    crate::leanh::lean_inc(v_k_8786_);
                                    v_isSharedCheck_9085_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                                    if v_isSharedCheck_9085_ == 0 {
                                        v_unused_9086_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                                        crate::leanh::lean_dec(v_unused_9086_);
                                        v_unused_9087_ = crate::leanh::lean_ctor_get(v_r_8600_, 3);
                                        crate::leanh::lean_dec(v_unused_9087_);
                                        v_unused_9088_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                                        crate::leanh::lean_dec(v_unused_9088_);
                                        v_unused_9089_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                                        crate::leanh::lean_dec(v_unused_9089_);
                                        v_unused_9090_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                                        crate::leanh::lean_dec(v_unused_9090_);
                                        v___x_8934_ = v_r_8600_;
                                        v_isShared_8935_ = v_isSharedCheck_9085_;
                                        state = 51;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_8600_);
                                        v___x_8934_ = crate::leanh::lean_box(0);
                                        v_isShared_8935_ = v_isSharedCheck_9085_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_8599_;
                            }
                        } else {
                            return v_r_8600_;
                        }
                    }
                    _ => {
                        v_impl_9091_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_8594_, v_k_8595_, v_r_8600_);
                        v___x_9092_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_9091_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_8599_) == 0 {
                                v_size_9093_ = crate::leanh::lean_ctor_get(v_impl_9091_, 0);
                                crate::leanh::lean_inc(v_size_9093_);
                                v_size_9094_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                v_k_9095_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                v_v_9096_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                v_l_9097_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                v_r_9098_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                crate::leanh::lean_inc(v_r_9098_);
                                v___x_9099_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_9100_ = lean_nat_mul(v___x_9099_, v_size_9093_);
                                v___x_9101_ = lean_nat_dec_lt(v___x_9100_, v_size_9094_);
                                crate::leanh::lean_dec(v___x_9100_);
                                if v___x_9101_ == 0 {
                                    crate::leanh::lean_dec(v_r_9098_);
                                    v___x_9102_ = lean_nat_add(v___x_9092_, v_size_9094_);
                                    v___x_9103_ = lean_nat_add(v___x_9102_, v_size_9093_);
                                    crate::leanh::lean_dec(v_size_9093_);
                                    crate::leanh::lean_dec(v___x_9102_);
                                    if v_isShared_8603_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_8602_, 4, v_impl_9091_);
                                        crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_9103_);
                                        v___x_9105_ = v___x_8602_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_9106_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_9106_,
                                            0,
                                            v___x_9103_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_9106_,
                                            1,
                                            v_k_8597_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_9106_,
                                            2,
                                            v_v_8598_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_9106_,
                                            3,
                                            v_l_8599_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_9106_,
                                            4,
                                            v_impl_9091_,
                                        );
                                        v___x_9105_ = v_reuseFailAlloc_9106_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_9097_);
                                    crate::leanh::lean_inc(v_v_9096_);
                                    crate::leanh::lean_inc(v_k_9095_);
                                    crate::leanh::lean_inc(v_size_9094_);
                                    v_isSharedCheck_9172_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                                    if v_isSharedCheck_9172_ == 0 {
                                        v_unused_9173_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                        crate::leanh::lean_dec(v_unused_9173_);
                                        v_unused_9174_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                        crate::leanh::lean_dec(v_unused_9174_);
                                        v_unused_9175_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                        crate::leanh::lean_dec(v_unused_9175_);
                                        v_unused_9176_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                        crate::leanh::lean_dec(v_unused_9176_);
                                        v_unused_9177_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                        crate::leanh::lean_dec(v_unused_9177_);
                                        v___x_9108_ = v_l_8599_;
                                        v_isShared_9109_ = v_isSharedCheck_9172_;
                                        state = 75;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_8599_);
                                        v___x_9108_ = crate::leanh::lean_box(0);
                                        v_isShared_9109_ = v_isSharedCheck_9172_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_9178_ = crate::leanh::lean_ctor_get(v_impl_9091_, 0);
                                crate::leanh::lean_inc(v_size_9178_);
                                v___x_9179_ = lean_nat_add(v___x_9092_, v_size_9178_);
                                crate::leanh::lean_dec(v_size_9178_);
                                if v_isShared_8603_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v_impl_9091_);
                                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_9179_);
                                    v___x_9181_ = v___x_8602_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_9182_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9182_,
                                        0,
                                        v___x_9179_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9182_,
                                        1,
                                        v_k_8597_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9182_,
                                        2,
                                        v_v_8598_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9182_,
                                        3,
                                        v_l_8599_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9182_,
                                        4,
                                        v_impl_9091_,
                                    );
                                    v___x_9181_ = v_reuseFailAlloc_9182_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_l_8599_) == 0 {
                                v_l_9183_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                if crate::leanh::lean_obj_tag(v_l_9183_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_9183_);
                                    v_r_9184_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                    crate::leanh::lean_inc(v_r_9184_);
                                    if crate::leanh::lean_obj_tag(v_r_9184_) == 0 {
                                        v_size_9185_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                        v_k_9186_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                        v_v_9187_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                        v_isSharedCheck_9200_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                                        if v_isSharedCheck_9200_ == 0 {
                                            v_unused_9201_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                            crate::leanh::lean_dec(v_unused_9201_);
                                            v_unused_9202_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                            crate::leanh::lean_dec(v_unused_9202_);
                                            v___x_9189_ = v_l_8599_;
                                            v_isShared_9190_ = v_isSharedCheck_9200_;
                                            state = 86;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_9187_);
                                            crate::leanh::lean_inc(v_k_9186_);
                                            crate::leanh::lean_inc(v_size_9185_);
                                            crate::leanh::lean_dec(v_l_8599_);
                                            v___x_9189_ = crate::leanh::lean_box(0);
                                            v_isShared_9190_ = v_isSharedCheck_9200_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_9203_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                        v_v_9204_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                        v_isSharedCheck_9215_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                                        if v_isSharedCheck_9215_ == 0 {
                                            v_unused_9216_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                            crate::leanh::lean_dec(v_unused_9216_);
                                            v_unused_9217_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                            crate::leanh::lean_dec(v_unused_9217_);
                                            v_unused_9218_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                            crate::leanh::lean_dec(v_unused_9218_);
                                            v___x_9206_ = v_l_8599_;
                                            v_isShared_9207_ = v_isSharedCheck_9215_;
                                            state = 89;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_9204_);
                                            crate::leanh::lean_inc(v_k_9203_);
                                            crate::leanh::lean_dec(v_l_8599_);
                                            v___x_9206_ = crate::leanh::lean_box(0);
                                            v_isShared_9207_ = v_isSharedCheck_9215_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_9219_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                    crate::leanh::lean_inc(v_r_9219_);
                                    if crate::leanh::lean_obj_tag(v_r_9219_) == 0 {
                                        crate::leanh::lean_inc(v_l_9183_);
                                        v_k_9220_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                        v_v_9221_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                        v_isSharedCheck_9244_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                                        if v_isSharedCheck_9244_ == 0 {
                                            v_unused_9245_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                            crate::leanh::lean_dec(v_unused_9245_);
                                            v_unused_9246_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                            crate::leanh::lean_dec(v_unused_9246_);
                                            v_unused_9247_ =
                                                crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                            crate::leanh::lean_dec(v_unused_9247_);
                                            v___x_9223_ = v_l_8599_;
                                            v_isShared_9224_ = v_isSharedCheck_9244_;
                                            state = 92;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_9221_);
                                            crate::leanh::lean_inc(v_k_9220_);
                                            crate::leanh::lean_dec(v_l_8599_);
                                            v___x_9223_ = crate::leanh::lean_box(0);
                                            v_isShared_9224_ = v_isSharedCheck_9244_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_9248_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_8603_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_8602_, 4, v_r_9219_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_8602_,
                                                0,
                                                v___x_9248_,
                                            );
                                            v___x_9250_ = v___x_8602_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_9251_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_9251_,
                                                0,
                                                v___x_9248_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_9251_,
                                                1,
                                                v_k_8597_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_9251_,
                                                2,
                                                v_v_8598_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_9251_,
                                                3,
                                                v_l_8599_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_9251_,
                                                4,
                                                v_r_9219_,
                                            );
                                            v___x_9250_ = v_reuseFailAlloc_9251_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_8603_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v_l_8599_);
                                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_9092_);
                                    v___x_9253_ = v___x_8602_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_9254_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9254_,
                                        0,
                                        v___x_9092_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9254_,
                                        1,
                                        v_k_8597_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9254_,
                                        2,
                                        v_v_8598_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9254_,
                                        3,
                                        v_l_8599_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_9254_,
                                        4,
                                        v_l_8599_,
                                    );
                                    v___x_9253_ = v_reuseFailAlloc_9254_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_8620_;
            }
            3 => {
                v_size_8625_ = crate::leanh::lean_ctor_get(v_l_8612_, 0);
                v_k_8626_ = crate::leanh::lean_ctor_get(v_l_8612_, 1);
                v_v_8627_ = crate::leanh::lean_ctor_get(v_l_8612_, 2);
                v_l_8628_ = crate::leanh::lean_ctor_get(v_l_8612_, 3);
                v_r_8629_ = crate::leanh::lean_ctor_get(v_l_8612_, 4);
                v_size_8630_ = crate::leanh::lean_ctor_get(v_r_8613_, 0);
                v___x_8631_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_8632_ = lean_nat_mul(v___x_8631_, v_size_8630_);
                v___x_8633_ = lean_nat_dec_lt(v_size_8625_, v___x_8632_);
                crate::leanh::lean_dec(v___x_8632_);
                if v___x_8633_ == 0 {
                    crate::leanh::lean_inc(v_r_8629_);
                    crate::leanh::lean_inc(v_l_8628_);
                    crate::leanh::lean_inc(v_v_8627_);
                    crate::leanh::lean_inc(v_k_8626_);
                    v_isSharedCheck_8661_ = (!crate::leanh::lean_is_exclusive(v_l_8612_)) as u8;
                    if v_isSharedCheck_8661_ == 0 {
                        v_unused_8662_ = crate::leanh::lean_ctor_get(v_l_8612_, 4);
                        crate::leanh::lean_dec(v_unused_8662_);
                        v_unused_8663_ = crate::leanh::lean_ctor_get(v_l_8612_, 3);
                        crate::leanh::lean_dec(v_unused_8663_);
                        v_unused_8664_ = crate::leanh::lean_ctor_get(v_l_8612_, 2);
                        crate::leanh::lean_dec(v_unused_8664_);
                        v_unused_8665_ = crate::leanh::lean_ctor_get(v_l_8612_, 1);
                        crate::leanh::lean_dec(v_unused_8665_);
                        v_unused_8666_ = crate::leanh::lean_ctor_get(v_l_8612_, 0);
                        crate::leanh::lean_dec(v_unused_8666_);
                        v___x_8635_ = v_l_8612_;
                        v_isShared_8636_ = v_isSharedCheck_8661_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_8612_);
                        v___x_8635_ = crate::leanh::lean_box(0);
                        v_isShared_8636_ = v_isSharedCheck_8661_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8602_);
                    v___x_8667_ = lean_nat_add(v___x_8607_, v_size_8608_);
                    crate::leanh::lean_dec(v_size_8608_);
                    v___x_8668_ = lean_nat_add(v___x_8667_, v_size_8609_);
                    crate::leanh::lean_dec(v_size_8609_);
                    v___x_8669_ = lean_nat_add(v___x_8667_, v_size_8625_);
                    crate::leanh::lean_dec(v___x_8667_);
                    crate::leanh::lean_inc_ref(v_impl_8606_);
                    if v_isShared_8624_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8623_, 4, v_l_8612_);
                        crate::leanh::lean_ctor_set(v___x_8623_, 3, v_impl_8606_);
                        crate::leanh::lean_ctor_set(v___x_8623_, 2, v_v_8598_);
                        crate::leanh::lean_ctor_set(v___x_8623_, 1, v_k_8597_);
                        crate::leanh::lean_ctor_set(v___x_8623_, 0, v___x_8669_);
                        v___x_8671_ = v___x_8623_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_8684_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8684_, 0, v___x_8669_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8684_, 1, v_k_8597_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8684_, 2, v_v_8598_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8684_, 3, v_impl_8606_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8684_, 4, v_l_8612_);
                        v___x_8671_ = v_reuseFailAlloc_8684_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_8637_ = lean_nat_add(v___x_8607_, v_size_8608_);
                crate::leanh::lean_dec(v_size_8608_);
                v___x_8638_ = lean_nat_add(v___x_8637_, v_size_8609_);
                crate::leanh::lean_dec(v_size_8609_);
                if crate::leanh::lean_obj_tag(v_l_8628_) == 0 {
                    v_size_8659_ = crate::leanh::lean_ctor_get(v_l_8628_, 0);
                    crate::leanh::lean_inc(v_size_8659_);
                    v___y_8651_ = v_size_8659_;
                    state = 8;
                    continue;
                } else {
                    v___x_8660_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8651_ = v___x_8660_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_8643_ = lean_nat_add(v___y_8641_, v___y_8642_);
                crate::leanh::lean_dec(v___y_8642_);
                crate::leanh::lean_dec(v___y_8641_);
                if v_isShared_8636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8635_, 4, v_r_8613_);
                    crate::leanh::lean_ctor_set(v___x_8635_, 3, v_r_8629_);
                    crate::leanh::lean_ctor_set(v___x_8635_, 2, v_v_8611_);
                    crate::leanh::lean_ctor_set(v___x_8635_, 1, v_k_8610_);
                    crate::leanh::lean_ctor_set(v___x_8635_, 0, v___x_8643_);
                    v___x_8645_ = v___x_8635_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8649_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8649_, 0, v___x_8643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8649_, 1, v_k_8610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8649_, 2, v_v_8611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8649_, 3, v_r_8629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8649_, 4, v_r_8613_);
                    v___x_8645_ = v_reuseFailAlloc_8649_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_8624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8623_, 4, v___x_8645_);
                    crate::leanh::lean_ctor_set(v___x_8623_, 3, v___y_8640_);
                    crate::leanh::lean_ctor_set(v___x_8623_, 2, v_v_8627_);
                    crate::leanh::lean_ctor_set(v___x_8623_, 1, v_k_8626_);
                    crate::leanh::lean_ctor_set(v___x_8623_, 0, v___x_8638_);
                    v___x_8647_ = v___x_8623_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8648_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8648_, 0, v___x_8638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8648_, 1, v_k_8626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8648_, 2, v_v_8627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8648_, 3, v___y_8640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8648_, 4, v___x_8645_);
                    v___x_8647_ = v_reuseFailAlloc_8648_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8647_;
            }
            8 => {
                v___x_8652_ = lean_nat_add(v___x_8637_, v___y_8651_);
                crate::leanh::lean_dec(v___y_8651_);
                crate::leanh::lean_dec(v___x_8637_);
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v_l_8628_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v_impl_8606_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8652_);
                    v___x_8654_ = v___x_8602_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8658_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8658_, 0, v___x_8652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8658_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8658_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8658_, 3, v_impl_8606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8658_, 4, v_l_8628_);
                    v___x_8654_ = v_reuseFailAlloc_8658_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_8655_ = lean_nat_add(v___x_8607_, v_size_8630_);
                if crate::leanh::lean_obj_tag(v_r_8629_) == 0 {
                    v_size_8656_ = crate::leanh::lean_ctor_get(v_r_8629_, 0);
                    crate::leanh::lean_inc(v_size_8656_);
                    v___y_8640_ = v___x_8654_;
                    v___y_8641_ = v___x_8655_;
                    v___y_8642_ = v_size_8656_;
                    state = 5;
                    continue;
                } else {
                    v___x_8657_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8640_ = v___x_8654_;
                    v___y_8641_ = v___x_8655_;
                    v___y_8642_ = v___x_8657_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_8678_ = (!crate::leanh::lean_is_exclusive(v_impl_8606_)) as u8;
                if v_isSharedCheck_8678_ == 0 {
                    v_unused_8679_ = crate::leanh::lean_ctor_get(v_impl_8606_, 4);
                    crate::leanh::lean_dec(v_unused_8679_);
                    v_unused_8680_ = crate::leanh::lean_ctor_get(v_impl_8606_, 3);
                    crate::leanh::lean_dec(v_unused_8680_);
                    v_unused_8681_ = crate::leanh::lean_ctor_get(v_impl_8606_, 2);
                    crate::leanh::lean_dec(v_unused_8681_);
                    v_unused_8682_ = crate::leanh::lean_ctor_get(v_impl_8606_, 1);
                    crate::leanh::lean_dec(v_unused_8682_);
                    v_unused_8683_ = crate::leanh::lean_ctor_get(v_impl_8606_, 0);
                    crate::leanh::lean_dec(v_unused_8683_);
                    v___x_8673_ = v_impl_8606_;
                    v_isShared_8674_ = v_isSharedCheck_8678_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_8606_);
                    v___x_8673_ = crate::leanh::lean_box(0);
                    v_isShared_8674_ = v_isSharedCheck_8678_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_8674_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8673_, 4, v_r_8613_);
                    crate::leanh::lean_ctor_set(v___x_8673_, 3, v___x_8671_);
                    crate::leanh::lean_ctor_set(v___x_8673_, 2, v_v_8611_);
                    crate::leanh::lean_ctor_set(v___x_8673_, 1, v_k_8610_);
                    crate::leanh::lean_ctor_set(v___x_8673_, 0, v___x_8668_);
                    v___x_8676_ = v___x_8673_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8677_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8677_, 0, v___x_8668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8677_, 1, v_k_8610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8677_, 2, v_v_8611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8677_, 3, v___x_8671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8677_, 4, v_r_8613_);
                    v___x_8676_ = v_reuseFailAlloc_8677_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8676_;
            }
            13 => {
                return v___x_8694_;
            }
            14 => {
                v_size_8704_ = crate::leanh::lean_ctor_get(v_l_8696_, 0);
                v___x_8705_ = lean_nat_add(v___x_8607_, v_size_8698_);
                crate::leanh::lean_dec(v_size_8698_);
                v___x_8706_ = lean_nat_add(v___x_8607_, v_size_8704_);
                if v_isShared_8703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8702_, 4, v_l_8696_);
                    crate::leanh::lean_ctor_set(v___x_8702_, 3, v_impl_8606_);
                    crate::leanh::lean_ctor_set(v___x_8702_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v___x_8702_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v___x_8702_, 0, v___x_8706_);
                    v___x_8708_ = v___x_8702_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8712_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8712_, 0, v___x_8706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8712_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8712_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8712_, 3, v_impl_8606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8712_, 4, v_l_8696_);
                    v___x_8708_ = v_reuseFailAlloc_8712_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v_r_8697_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v___x_8708_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 2, v_v_8700_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 1, v_k_8699_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8705_);
                    v___x_8710_ = v___x_8602_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_8711_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8711_, 0, v___x_8705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8711_, 1, v_k_8699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8711_, 2, v_v_8700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8711_, 3, v___x_8708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8711_, 4, v_r_8697_);
                    v___x_8710_ = v_reuseFailAlloc_8711_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_8710_;
            }
            17 => {
                v_k_8721_ = crate::leanh::lean_ctor_get(v_l_8696_, 1);
                v_v_8722_ = crate::leanh::lean_ctor_get(v_l_8696_, 2);
                v_isSharedCheck_8736_ = (!crate::leanh::lean_is_exclusive(v_l_8696_)) as u8;
                if v_isSharedCheck_8736_ == 0 {
                    v_unused_8737_ = crate::leanh::lean_ctor_get(v_l_8696_, 4);
                    crate::leanh::lean_dec(v_unused_8737_);
                    v_unused_8738_ = crate::leanh::lean_ctor_get(v_l_8696_, 3);
                    crate::leanh::lean_dec(v_unused_8738_);
                    v_unused_8739_ = crate::leanh::lean_ctor_get(v_l_8696_, 0);
                    crate::leanh::lean_dec(v_unused_8739_);
                    v___x_8724_ = v_l_8696_;
                    v_isShared_8725_ = v_isSharedCheck_8736_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_8722_);
                    crate::leanh::lean_inc(v_k_8721_);
                    crate::leanh::lean_dec(v_l_8696_);
                    v___x_8724_ = crate::leanh::lean_box(0);
                    v_isShared_8725_ = v_isSharedCheck_8736_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_8726_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_8725_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8724_, 4, v_r_8697_);
                    crate::leanh::lean_ctor_set(v___x_8724_, 3, v_r_8697_);
                    crate::leanh::lean_ctor_set(v___x_8724_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v___x_8724_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v___x_8724_, 0, v___x_8607_);
                    v___x_8728_ = v___x_8724_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_8735_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8735_, 0, v___x_8607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8735_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8735_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8735_, 3, v_r_8697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8735_, 4, v_r_8697_);
                    v___x_8728_ = v_reuseFailAlloc_8735_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_8720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8719_, 3, v_r_8697_);
                    crate::leanh::lean_ctor_set(v___x_8719_, 0, v___x_8607_);
                    v___x_8730_ = v___x_8719_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_8734_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 0, v___x_8607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 1, v_k_8716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 2, v_v_8717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 3, v_r_8697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 4, v_r_8697_);
                    v___x_8730_ = v_reuseFailAlloc_8734_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v___x_8730_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v___x_8728_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 2, v_v_8722_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 1, v_k_8721_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8726_);
                    v___x_8732_ = v___x_8602_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_8733_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8733_, 0, v___x_8726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8733_, 1, v_k_8721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8733_, 2, v_v_8722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8733_, 3, v___x_8728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8733_, 4, v___x_8730_);
                    v___x_8732_ = v_reuseFailAlloc_8733_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_8732_;
            }
            22 => {
                v___x_8750_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_8749_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8748_, 4, v_l_8696_);
                    crate::leanh::lean_ctor_set(v___x_8748_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v___x_8748_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v___x_8748_, 0, v___x_8607_);
                    v___x_8752_ = v___x_8748_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_8756_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8756_, 0, v___x_8607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8756_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8756_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8756_, 3, v_l_8696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8756_, 4, v_l_8696_);
                    v___x_8752_ = v_reuseFailAlloc_8756_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v_r_8744_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v___x_8752_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 2, v_v_8746_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 1, v_k_8745_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8750_);
                    v___x_8754_ = v___x_8602_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_8755_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8755_, 0, v___x_8750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8755_, 1, v_k_8745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8755_, 2, v_v_8746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8755_, 3, v___x_8752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8755_, 4, v_r_8744_);
                    v___x_8754_ = v_reuseFailAlloc_8755_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_8754_;
            }
            25 => {
                if v_isShared_8766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8765_, 3, v_r_8744_);
                    v___x_8768_ = v___x_8765_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_8773_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 0, v_size_8761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 1, v_k_8762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 2, v_v_8763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 3, v_r_8744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 4, v_r_8744_);
                    v___x_8768_ = v_reuseFailAlloc_8773_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_8769_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v___x_8768_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v_r_8744_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_8769_);
                    v___x_8771_ = v___x_8602_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_8772_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8772_, 0, v___x_8769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8772_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8772_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8772_, 3, v_r_8744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8772_, 4, v___x_8768_);
                    v___x_8771_ = v_reuseFailAlloc_8772_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_8771_;
            }
            28 => {
                return v___x_8778_;
            }
            29 => {
                v___x_8795_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_8781_, v_v_8782_, v_l_8783_, v_r_8784_,
                );
                v_tree_8796_ = crate::leanh::lean_ctor_get(v___x_8795_, 2);
                crate::leanh::lean_inc(v_tree_8796_);
                if crate::leanh::lean_obj_tag(v_tree_8796_) == 0 {
                    v_k_8797_ = crate::leanh::lean_ctor_get(v___x_8795_, 0);
                    crate::leanh::lean_inc(v_k_8797_);
                    v_v_8798_ = crate::leanh::lean_ctor_get(v___x_8795_, 1);
                    crate::leanh::lean_inc(v_v_8798_);
                    crate::leanh::lean_dec_ref(v___x_8795_);
                    v_size_8799_ = crate::leanh::lean_ctor_get(v_tree_8796_, 0);
                    v___x_8800_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_8801_ = lean_nat_mul(v___x_8800_, v_size_8799_);
                    v___x_8802_ = lean_nat_dec_lt(v___x_8801_, v_size_8785_);
                    crate::leanh::lean_dec(v___x_8801_);
                    if v___x_8802_ == 0 {
                        crate::leanh::lean_dec(v_l_8788_);
                        v___x_8803_ = lean_nat_add(v___x_8790_, v_size_8799_);
                        v___x_8804_ = lean_nat_add(v___x_8803_, v_size_8785_);
                        crate::leanh::lean_dec(v___x_8803_);
                        if v_isShared_8794_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8793_, 4, v_r_8600_);
                            crate::leanh::lean_ctor_set(v___x_8793_, 3, v_tree_8796_);
                            crate::leanh::lean_ctor_set(v___x_8793_, 2, v_v_8798_);
                            crate::leanh::lean_ctor_set(v___x_8793_, 1, v_k_8797_);
                            crate::leanh::lean_ctor_set(v___x_8793_, 0, v___x_8804_);
                            v___x_8806_ = v___x_8793_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_8807_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8807_, 0, v___x_8804_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8807_, 1, v_k_8797_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8807_, 2, v_v_8798_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8807_, 3, v_tree_8796_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8807_, 4, v_r_8600_);
                            v___x_8806_ = v_reuseFailAlloc_8807_;
                            state = 30;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_8789_);
                        crate::leanh::lean_inc(v_v_8787_);
                        crate::leanh::lean_inc(v_k_8786_);
                        crate::leanh::lean_inc(v_size_8785_);
                        v_isSharedCheck_8862_ = (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                        if v_isSharedCheck_8862_ == 0 {
                            v_unused_8863_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                            crate::leanh::lean_dec(v_unused_8863_);
                            v_unused_8864_ = crate::leanh::lean_ctor_get(v_r_8600_, 3);
                            crate::leanh::lean_dec(v_unused_8864_);
                            v_unused_8865_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                            crate::leanh::lean_dec(v_unused_8865_);
                            v_unused_8866_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                            crate::leanh::lean_dec(v_unused_8866_);
                            v_unused_8867_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                            crate::leanh::lean_dec(v_unused_8867_);
                            v___x_8809_ = v_r_8600_;
                            v_isShared_8810_ = v_isSharedCheck_8862_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_8600_);
                            v___x_8809_ = crate::leanh::lean_box(0);
                            v_isShared_8810_ = v_isSharedCheck_8862_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_8789_);
                    crate::leanh::lean_inc(v_v_8787_);
                    crate::leanh::lean_inc(v_k_8786_);
                    crate::leanh::lean_inc(v_size_8785_);
                    v_isSharedCheck_8921_ = (!crate::leanh::lean_is_exclusive(v_r_8600_)) as u8;
                    if v_isSharedCheck_8921_ == 0 {
                        v_unused_8922_ = crate::leanh::lean_ctor_get(v_r_8600_, 4);
                        crate::leanh::lean_dec(v_unused_8922_);
                        v_unused_8923_ = crate::leanh::lean_ctor_get(v_r_8600_, 3);
                        crate::leanh::lean_dec(v_unused_8923_);
                        v_unused_8924_ = crate::leanh::lean_ctor_get(v_r_8600_, 2);
                        crate::leanh::lean_dec(v_unused_8924_);
                        v_unused_8925_ = crate::leanh::lean_ctor_get(v_r_8600_, 1);
                        crate::leanh::lean_dec(v_unused_8925_);
                        v_unused_8926_ = crate::leanh::lean_ctor_get(v_r_8600_, 0);
                        crate::leanh::lean_dec(v_unused_8926_);
                        v___x_8869_ = v_r_8600_;
                        v_isShared_8870_ = v_isSharedCheck_8921_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_8600_);
                        v___x_8869_ = crate::leanh::lean_box(0);
                        v_isShared_8870_ = v_isSharedCheck_8921_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_8806_;
            }
            31 => {
                v_size_8811_ = crate::leanh::lean_ctor_get(v_l_8788_, 0);
                v_k_8812_ = crate::leanh::lean_ctor_get(v_l_8788_, 1);
                v_v_8813_ = crate::leanh::lean_ctor_get(v_l_8788_, 2);
                v_l_8814_ = crate::leanh::lean_ctor_get(v_l_8788_, 3);
                v_r_8815_ = crate::leanh::lean_ctor_get(v_l_8788_, 4);
                v_size_8816_ = crate::leanh::lean_ctor_get(v_r_8789_, 0);
                v___x_8817_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_8818_ = lean_nat_mul(v___x_8817_, v_size_8816_);
                v___x_8819_ = lean_nat_dec_lt(v_size_8811_, v___x_8818_);
                crate::leanh::lean_dec(v___x_8818_);
                if v___x_8819_ == 0 {
                    crate::leanh::lean_inc(v_r_8815_);
                    crate::leanh::lean_inc(v_l_8814_);
                    crate::leanh::lean_inc(v_v_8813_);
                    crate::leanh::lean_inc(v_k_8812_);
                    v_isSharedCheck_8847_ = (!crate::leanh::lean_is_exclusive(v_l_8788_)) as u8;
                    if v_isSharedCheck_8847_ == 0 {
                        v_unused_8848_ = crate::leanh::lean_ctor_get(v_l_8788_, 4);
                        crate::leanh::lean_dec(v_unused_8848_);
                        v_unused_8849_ = crate::leanh::lean_ctor_get(v_l_8788_, 3);
                        crate::leanh::lean_dec(v_unused_8849_);
                        v_unused_8850_ = crate::leanh::lean_ctor_get(v_l_8788_, 2);
                        crate::leanh::lean_dec(v_unused_8850_);
                        v_unused_8851_ = crate::leanh::lean_ctor_get(v_l_8788_, 1);
                        crate::leanh::lean_dec(v_unused_8851_);
                        v_unused_8852_ = crate::leanh::lean_ctor_get(v_l_8788_, 0);
                        crate::leanh::lean_dec(v_unused_8852_);
                        v___x_8821_ = v_l_8788_;
                        v_isShared_8822_ = v_isSharedCheck_8847_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_8788_);
                        v___x_8821_ = crate::leanh::lean_box(0);
                        v_isShared_8822_ = v_isSharedCheck_8847_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_8853_ = lean_nat_add(v___x_8790_, v_size_8799_);
                    v___x_8854_ = lean_nat_add(v___x_8853_, v_size_8785_);
                    crate::leanh::lean_dec(v_size_8785_);
                    v___x_8855_ = lean_nat_add(v___x_8853_, v_size_8811_);
                    crate::leanh::lean_dec(v___x_8853_);
                    if v_isShared_8810_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8809_, 4, v_l_8788_);
                        crate::leanh::lean_ctor_set(v___x_8809_, 3, v_tree_8796_);
                        crate::leanh::lean_ctor_set(v___x_8809_, 2, v_v_8798_);
                        crate::leanh::lean_ctor_set(v___x_8809_, 1, v_k_8797_);
                        crate::leanh::lean_ctor_set(v___x_8809_, 0, v___x_8855_);
                        v___x_8857_ = v___x_8809_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_8861_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8861_, 0, v___x_8855_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8861_, 1, v_k_8797_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8861_, 2, v_v_8798_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8861_, 3, v_tree_8796_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8861_, 4, v_l_8788_);
                        v___x_8857_ = v_reuseFailAlloc_8861_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_8823_ = lean_nat_add(v___x_8790_, v_size_8799_);
                v___x_8824_ = lean_nat_add(v___x_8823_, v_size_8785_);
                crate::leanh::lean_dec(v_size_8785_);
                if crate::leanh::lean_obj_tag(v_l_8814_) == 0 {
                    v_size_8845_ = crate::leanh::lean_ctor_get(v_l_8814_, 0);
                    crate::leanh::lean_inc(v_size_8845_);
                    v___y_8837_ = v_size_8845_;
                    state = 36;
                    continue;
                } else {
                    v___x_8846_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8837_ = v___x_8846_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_8829_ = lean_nat_add(v___y_8827_, v___y_8828_);
                crate::leanh::lean_dec(v___y_8828_);
                crate::leanh::lean_dec(v___y_8827_);
                if v_isShared_8822_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8821_, 4, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8821_, 3, v_r_8815_);
                    crate::leanh::lean_ctor_set(v___x_8821_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v___x_8821_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v___x_8821_, 0, v___x_8829_);
                    v___x_8831_ = v___x_8821_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_8835_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8835_, 0, v___x_8829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8835_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8835_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8835_, 3, v_r_8815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8835_, 4, v_r_8789_);
                    v___x_8831_ = v_reuseFailAlloc_8835_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_8810_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8809_, 4, v___x_8831_);
                    crate::leanh::lean_ctor_set(v___x_8809_, 3, v___y_8826_);
                    crate::leanh::lean_ctor_set(v___x_8809_, 2, v_v_8813_);
                    crate::leanh::lean_ctor_set(v___x_8809_, 1, v_k_8812_);
                    crate::leanh::lean_ctor_set(v___x_8809_, 0, v___x_8824_);
                    v___x_8833_ = v___x_8809_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_8834_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8834_, 0, v___x_8824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8834_, 1, v_k_8812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8834_, 2, v_v_8813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8834_, 3, v___y_8826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8834_, 4, v___x_8831_);
                    v___x_8833_ = v_reuseFailAlloc_8834_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_8833_;
            }
            36 => {
                v___x_8838_ = lean_nat_add(v___x_8823_, v___y_8837_);
                crate::leanh::lean_dec(v___y_8837_);
                crate::leanh::lean_dec(v___x_8823_);
                if v_isShared_8794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8793_, 4, v_l_8814_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 3, v_tree_8796_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 2, v_v_8798_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 1, v_k_8797_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 0, v___x_8838_);
                    v___x_8840_ = v___x_8793_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_8844_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8844_, 0, v___x_8838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8844_, 1, v_k_8797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8844_, 2, v_v_8798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8844_, 3, v_tree_8796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8844_, 4, v_l_8814_);
                    v___x_8840_ = v_reuseFailAlloc_8844_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_8841_ = lean_nat_add(v___x_8790_, v_size_8816_);
                if crate::leanh::lean_obj_tag(v_r_8815_) == 0 {
                    v_size_8842_ = crate::leanh::lean_ctor_get(v_r_8815_, 0);
                    crate::leanh::lean_inc(v_size_8842_);
                    v___y_8826_ = v___x_8840_;
                    v___y_8827_ = v___x_8841_;
                    v___y_8828_ = v_size_8842_;
                    state = 33;
                    continue;
                } else {
                    v___x_8843_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8826_ = v___x_8840_;
                    v___y_8827_ = v___x_8841_;
                    v___y_8828_ = v___x_8843_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_8794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8793_, 4, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 3, v___x_8857_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 0, v___x_8854_);
                    v___x_8859_ = v___x_8793_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_8860_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8860_, 0, v___x_8854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8860_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8860_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8860_, 3, v___x_8857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8860_, 4, v_r_8789_);
                    v___x_8859_ = v_reuseFailAlloc_8860_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_8859_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v_l_8788_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_8789_) == 0 {
                        v_k_8871_ = crate::leanh::lean_ctor_get(v___x_8795_, 0);
                        crate::leanh::lean_inc(v_k_8871_);
                        v_v_8872_ = crate::leanh::lean_ctor_get(v___x_8795_, 1);
                        crate::leanh::lean_inc(v_v_8872_);
                        crate::leanh::lean_dec_ref(v___x_8795_);
                        v_size_8873_ = crate::leanh::lean_ctor_get(v_l_8788_, 0);
                        v___x_8874_ = lean_nat_add(v___x_8790_, v_size_8785_);
                        crate::leanh::lean_dec(v_size_8785_);
                        v___x_8875_ = lean_nat_add(v___x_8790_, v_size_8873_);
                        if v_isShared_8870_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8869_, 4, v_l_8788_);
                            crate::leanh::lean_ctor_set(v___x_8869_, 3, v_tree_8796_);
                            crate::leanh::lean_ctor_set(v___x_8869_, 2, v_v_8872_);
                            crate::leanh::lean_ctor_set(v___x_8869_, 1, v_k_8871_);
                            crate::leanh::lean_ctor_set(v___x_8869_, 0, v___x_8875_);
                            v___x_8877_ = v___x_8869_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_8881_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8881_, 0, v___x_8875_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8881_, 1, v_k_8871_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8881_, 2, v_v_8872_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8881_, 3, v_tree_8796_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8881_, 4, v_l_8788_);
                            v___x_8877_ = v_reuseFailAlloc_8881_;
                            state = 41;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_8785_);
                        v_k_8882_ = crate::leanh::lean_ctor_get(v___x_8795_, 0);
                        crate::leanh::lean_inc(v_k_8882_);
                        v_v_8883_ = crate::leanh::lean_ctor_get(v___x_8795_, 1);
                        crate::leanh::lean_inc(v_v_8883_);
                        crate::leanh::lean_dec_ref(v___x_8795_);
                        v_k_8884_ = crate::leanh::lean_ctor_get(v_l_8788_, 1);
                        v_v_8885_ = crate::leanh::lean_ctor_get(v_l_8788_, 2);
                        v_isSharedCheck_8899_ = (!crate::leanh::lean_is_exclusive(v_l_8788_)) as u8;
                        if v_isSharedCheck_8899_ == 0 {
                            v_unused_8900_ = crate::leanh::lean_ctor_get(v_l_8788_, 4);
                            crate::leanh::lean_dec(v_unused_8900_);
                            v_unused_8901_ = crate::leanh::lean_ctor_get(v_l_8788_, 3);
                            crate::leanh::lean_dec(v_unused_8901_);
                            v_unused_8902_ = crate::leanh::lean_ctor_get(v_l_8788_, 0);
                            crate::leanh::lean_dec(v_unused_8902_);
                            v___x_8887_ = v_l_8788_;
                            v_isShared_8888_ = v_isSharedCheck_8899_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_8885_);
                            crate::leanh::lean_inc(v_k_8884_);
                            crate::leanh::lean_dec(v_l_8788_);
                            v___x_8887_ = crate::leanh::lean_box(0);
                            v_isShared_8888_ = v_isSharedCheck_8899_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_8789_) == 0 {
                        crate::leanh::lean_dec(v_size_8785_);
                        v_k_8903_ = crate::leanh::lean_ctor_get(v___x_8795_, 0);
                        crate::leanh::lean_inc(v_k_8903_);
                        v_v_8904_ = crate::leanh::lean_ctor_get(v___x_8795_, 1);
                        crate::leanh::lean_inc(v_v_8904_);
                        crate::leanh::lean_dec_ref(v___x_8795_);
                        v___x_8905_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_8870_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8869_, 4, v_l_8788_);
                            crate::leanh::lean_ctor_set(v___x_8869_, 2, v_v_8904_);
                            crate::leanh::lean_ctor_set(v___x_8869_, 1, v_k_8903_);
                            crate::leanh::lean_ctor_set(v___x_8869_, 0, v___x_8790_);
                            v___x_8907_ = v___x_8869_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_8911_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8911_, 0, v___x_8790_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8911_, 1, v_k_8903_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8911_, 2, v_v_8904_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8911_, 3, v_l_8788_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8911_, 4, v_l_8788_);
                            v___x_8907_ = v_reuseFailAlloc_8911_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_8912_ = crate::leanh::lean_ctor_get(v___x_8795_, 0);
                        crate::leanh::lean_inc(v_k_8912_);
                        v_v_8913_ = crate::leanh::lean_ctor_get(v___x_8795_, 1);
                        crate::leanh::lean_inc(v_v_8913_);
                        crate::leanh::lean_dec_ref(v___x_8795_);
                        if v_isShared_8870_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8869_, 3, v_r_8789_);
                            v___x_8915_ = v___x_8869_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_8920_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8920_, 0, v_size_8785_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8920_, 1, v_k_8786_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8920_, 2, v_v_8787_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8920_, 3, v_r_8789_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8920_, 4, v_r_8789_);
                            v___x_8915_ = v_reuseFailAlloc_8920_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_8794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8793_, 4, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 3, v___x_8877_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 0, v___x_8874_);
                    v___x_8879_ = v___x_8793_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_8880_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8880_, 0, v___x_8874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8880_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8880_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8880_, 3, v___x_8877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8880_, 4, v_r_8789_);
                    v___x_8879_ = v_reuseFailAlloc_8880_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_8879_;
            }
            43 => {
                v___x_8889_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_8888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8887_, 4, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8887_, 3, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8887_, 2, v_v_8883_);
                    crate::leanh::lean_ctor_set(v___x_8887_, 1, v_k_8882_);
                    crate::leanh::lean_ctor_set(v___x_8887_, 0, v___x_8790_);
                    v___x_8891_ = v___x_8887_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_8898_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8898_, 0, v___x_8790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8898_, 1, v_k_8882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8898_, 2, v_v_8883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8898_, 3, v_r_8789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8898_, 4, v_r_8789_);
                    v___x_8891_ = v_reuseFailAlloc_8898_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_8870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8869_, 3, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8869_, 0, v___x_8790_);
                    v___x_8893_ = v___x_8869_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_8897_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8897_, 0, v___x_8790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8897_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8897_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8897_, 3, v_r_8789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8897_, 4, v_r_8789_);
                    v___x_8893_ = v_reuseFailAlloc_8897_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_8794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8793_, 4, v___x_8893_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 3, v___x_8891_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 2, v_v_8885_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 1, v_k_8884_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 0, v___x_8889_);
                    v___x_8895_ = v___x_8793_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_8896_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8896_, 0, v___x_8889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8896_, 1, v_k_8884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8896_, 2, v_v_8885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8896_, 3, v___x_8891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8896_, 4, v___x_8893_);
                    v___x_8895_ = v_reuseFailAlloc_8896_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_8895_;
            }
            47 => {
                if v_isShared_8794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8793_, 4, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 3, v___x_8907_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 0, v___x_8905_);
                    v___x_8909_ = v___x_8793_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_8910_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8910_, 0, v___x_8905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8910_, 1, v_k_8786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8910_, 2, v_v_8787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8910_, 3, v___x_8907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8910_, 4, v_r_8789_);
                    v___x_8909_ = v_reuseFailAlloc_8910_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_8909_;
            }
            49 => {
                v___x_8916_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_8794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8793_, 4, v___x_8915_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 3, v_r_8789_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 2, v_v_8913_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 1, v_k_8912_);
                    crate::leanh::lean_ctor_set(v___x_8793_, 0, v___x_8916_);
                    v___x_8918_ = v___x_8793_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_8919_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8919_, 0, v___x_8916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8919_, 1, v_k_8912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8919_, 2, v_v_8913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8919_, 3, v_r_8789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8919_, 4, v___x_8915_);
                    v___x_8918_ = v_reuseFailAlloc_8919_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_8918_;
            }
            51 => {
                v___x_8936_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_8786_, v_v_8787_, v_l_8788_, v_r_8789_,
                );
                v_tree_8937_ = crate::leanh::lean_ctor_get(v___x_8936_, 2);
                crate::leanh::lean_inc(v_tree_8937_);
                if crate::leanh::lean_obj_tag(v_tree_8937_) == 0 {
                    v_k_8938_ = crate::leanh::lean_ctor_get(v___x_8936_, 0);
                    crate::leanh::lean_inc(v_k_8938_);
                    v_v_8939_ = crate::leanh::lean_ctor_get(v___x_8936_, 1);
                    crate::leanh::lean_inc(v_v_8939_);
                    crate::leanh::lean_dec_ref(v___x_8936_);
                    v_size_8940_ = crate::leanh::lean_ctor_get(v_tree_8937_, 0);
                    v___x_8941_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_8942_ = lean_nat_mul(v___x_8941_, v_size_8940_);
                    v___x_8943_ = lean_nat_dec_lt(v___x_8942_, v_size_8780_);
                    crate::leanh::lean_dec(v___x_8942_);
                    if v___x_8943_ == 0 {
                        crate::leanh::lean_dec(v_r_8784_);
                        v___x_8944_ = lean_nat_add(v___x_8790_, v_size_8780_);
                        v___x_8945_ = lean_nat_add(v___x_8944_, v_size_8940_);
                        crate::leanh::lean_dec(v___x_8944_);
                        if v_isShared_8935_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8934_, 4, v_tree_8937_);
                            crate::leanh::lean_ctor_set(v___x_8934_, 3, v_l_8599_);
                            crate::leanh::lean_ctor_set(v___x_8934_, 2, v_v_8939_);
                            crate::leanh::lean_ctor_set(v___x_8934_, 1, v_k_8938_);
                            crate::leanh::lean_ctor_set(v___x_8934_, 0, v___x_8945_);
                            v___x_8947_ = v___x_8934_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_8948_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8948_, 0, v___x_8945_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8948_, 1, v_k_8938_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8948_, 2, v_v_8939_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8948_, 3, v_l_8599_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8948_, 4, v_tree_8937_);
                            v___x_8947_ = v_reuseFailAlloc_8948_;
                            state = 52;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_8783_);
                        crate::leanh::lean_inc(v_v_8782_);
                        crate::leanh::lean_inc(v_k_8781_);
                        crate::leanh::lean_inc(v_size_8780_);
                        v_isSharedCheck_9014_ = (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                        if v_isSharedCheck_9014_ == 0 {
                            v_unused_9015_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                            crate::leanh::lean_dec(v_unused_9015_);
                            v_unused_9016_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                            crate::leanh::lean_dec(v_unused_9016_);
                            v_unused_9017_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                            crate::leanh::lean_dec(v_unused_9017_);
                            v_unused_9018_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                            crate::leanh::lean_dec(v_unused_9018_);
                            v_unused_9019_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                            crate::leanh::lean_dec(v_unused_9019_);
                            v___x_8950_ = v_l_8599_;
                            v_isShared_8951_ = v_isSharedCheck_9014_;
                            state = 53;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_8599_);
                            v___x_8950_ = crate::leanh::lean_box(0);
                            v_isShared_8951_ = v_isSharedCheck_9014_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_8783_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_8783_);
                        crate::leanh::lean_inc(v_v_8782_);
                        crate::leanh::lean_inc(v_k_8781_);
                        crate::leanh::lean_inc(v_size_8780_);
                        v_isSharedCheck_9043_ = (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                        if v_isSharedCheck_9043_ == 0 {
                            v_unused_9044_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                            crate::leanh::lean_dec(v_unused_9044_);
                            v_unused_9045_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                            crate::leanh::lean_dec(v_unused_9045_);
                            v_unused_9046_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                            crate::leanh::lean_dec(v_unused_9046_);
                            v_unused_9047_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                            crate::leanh::lean_dec(v_unused_9047_);
                            v_unused_9048_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                            crate::leanh::lean_dec(v_unused_9048_);
                            v___x_9021_ = v_l_8599_;
                            v_isShared_9022_ = v_isSharedCheck_9043_;
                            state = 63;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_8599_);
                            v___x_9021_ = crate::leanh::lean_box(0);
                            v_isShared_9022_ = v_isSharedCheck_9043_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_8784_) == 0 {
                            crate::leanh::lean_inc(v_l_8783_);
                            crate::leanh::lean_inc(v_v_8782_);
                            crate::leanh::lean_inc(v_k_8781_);
                            v_isSharedCheck_9073_ =
                                (!crate::leanh::lean_is_exclusive(v_l_8599_)) as u8;
                            if v_isSharedCheck_9073_ == 0 {
                                v_unused_9074_ = crate::leanh::lean_ctor_get(v_l_8599_, 4);
                                crate::leanh::lean_dec(v_unused_9074_);
                                v_unused_9075_ = crate::leanh::lean_ctor_get(v_l_8599_, 3);
                                crate::leanh::lean_dec(v_unused_9075_);
                                v_unused_9076_ = crate::leanh::lean_ctor_get(v_l_8599_, 2);
                                crate::leanh::lean_dec(v_unused_9076_);
                                v_unused_9077_ = crate::leanh::lean_ctor_get(v_l_8599_, 1);
                                crate::leanh::lean_dec(v_unused_9077_);
                                v_unused_9078_ = crate::leanh::lean_ctor_get(v_l_8599_, 0);
                                crate::leanh::lean_dec(v_unused_9078_);
                                v___x_9050_ = v_l_8599_;
                                v_isShared_9051_ = v_isSharedCheck_9073_;
                                state = 68;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_8599_);
                                v___x_9050_ = crate::leanh::lean_box(0);
                                v_isShared_9051_ = v_isSharedCheck_9073_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_9079_ = crate::leanh::lean_ctor_get(v___x_8936_, 0);
                            crate::leanh::lean_inc(v_k_9079_);
                            v_v_9080_ = crate::leanh::lean_ctor_get(v___x_8936_, 1);
                            crate::leanh::lean_inc(v_v_9080_);
                            crate::leanh::lean_dec_ref(v___x_8936_);
                            v___x_9081_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_8935_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_8934_, 4, v_r_8784_);
                                crate::leanh::lean_ctor_set(v___x_8934_, 3, v_l_8599_);
                                crate::leanh::lean_ctor_set(v___x_8934_, 2, v_v_9080_);
                                crate::leanh::lean_ctor_set(v___x_8934_, 1, v_k_9079_);
                                crate::leanh::lean_ctor_set(v___x_8934_, 0, v___x_9081_);
                                v___x_9083_ = v___x_8934_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_9084_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_9084_, 0, v___x_9081_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_9084_, 1, v_k_9079_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_9084_, 2, v_v_9080_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_9084_, 3, v_l_8599_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_9084_, 4, v_r_8784_);
                                v___x_9083_ = v_reuseFailAlloc_9084_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_8947_;
            }
            53 => {
                v_size_8952_ = crate::leanh::lean_ctor_get(v_l_8783_, 0);
                v_size_8953_ = crate::leanh::lean_ctor_get(v_r_8784_, 0);
                v_k_8954_ = crate::leanh::lean_ctor_get(v_r_8784_, 1);
                v_v_8955_ = crate::leanh::lean_ctor_get(v_r_8784_, 2);
                v_l_8956_ = crate::leanh::lean_ctor_get(v_r_8784_, 3);
                v_r_8957_ = crate::leanh::lean_ctor_get(v_r_8784_, 4);
                v___x_8958_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_8959_ = lean_nat_mul(v___x_8958_, v_size_8952_);
                v___x_8960_ = lean_nat_dec_lt(v_size_8953_, v___x_8959_);
                crate::leanh::lean_dec(v___x_8959_);
                if v___x_8960_ == 0 {
                    crate::leanh::lean_inc(v_r_8957_);
                    crate::leanh::lean_inc(v_l_8956_);
                    crate::leanh::lean_inc(v_v_8955_);
                    crate::leanh::lean_inc(v_k_8954_);
                    crate::leanh::lean_del_object(v___x_8950_);
                    v_isSharedCheck_8998_ = (!crate::leanh::lean_is_exclusive(v_r_8784_)) as u8;
                    if v_isSharedCheck_8998_ == 0 {
                        v_unused_8999_ = crate::leanh::lean_ctor_get(v_r_8784_, 4);
                        crate::leanh::lean_dec(v_unused_8999_);
                        v_unused_9000_ = crate::leanh::lean_ctor_get(v_r_8784_, 3);
                        crate::leanh::lean_dec(v_unused_9000_);
                        v_unused_9001_ = crate::leanh::lean_ctor_get(v_r_8784_, 2);
                        crate::leanh::lean_dec(v_unused_9001_);
                        v_unused_9002_ = crate::leanh::lean_ctor_get(v_r_8784_, 1);
                        crate::leanh::lean_dec(v_unused_9002_);
                        v_unused_9003_ = crate::leanh::lean_ctor_get(v_r_8784_, 0);
                        crate::leanh::lean_dec(v_unused_9003_);
                        v___x_8962_ = v_r_8784_;
                        v_isShared_8963_ = v_isSharedCheck_8998_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_8784_);
                        v___x_8962_ = crate::leanh::lean_box(0);
                        v_isShared_8963_ = v_isSharedCheck_8998_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_9004_ = lean_nat_add(v___x_8790_, v_size_8780_);
                    crate::leanh::lean_dec(v_size_8780_);
                    v___x_9005_ = lean_nat_add(v___x_9004_, v_size_8940_);
                    crate::leanh::lean_dec(v___x_9004_);
                    v___x_9006_ = lean_nat_add(v___x_8790_, v_size_8940_);
                    v___x_9007_ = lean_nat_add(v___x_9006_, v_size_8953_);
                    crate::leanh::lean_dec(v___x_9006_);
                    if v_isShared_8935_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8934_, 4, v_tree_8937_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 3, v_r_8784_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 2, v_v_8939_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 1, v_k_8938_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 0, v___x_9007_);
                        v___x_9009_ = v___x_8934_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_9013_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9013_, 0, v___x_9007_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9013_, 1, v_k_8938_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9013_, 2, v_v_8939_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9013_, 3, v_r_8784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9013_, 4, v_tree_8937_);
                        v___x_9009_ = v_reuseFailAlloc_9013_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_8964_ = lean_nat_add(v___x_8790_, v_size_8780_);
                crate::leanh::lean_dec(v_size_8780_);
                v___x_8965_ = lean_nat_add(v___x_8964_, v_size_8940_);
                crate::leanh::lean_dec(v___x_8964_);
                v___x_8986_ = lean_nat_add(v___x_8790_, v_size_8952_);
                if crate::leanh::lean_obj_tag(v_l_8956_) == 0 {
                    v_size_8996_ = crate::leanh::lean_ctor_get(v_l_8956_, 0);
                    crate::leanh::lean_inc(v_size_8996_);
                    v___y_8988_ = v_size_8996_;
                    state = 59;
                    continue;
                } else {
                    v___x_8997_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8988_ = v___x_8997_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_8970_ = lean_nat_add(v___y_8967_, v___y_8969_);
                crate::leanh::lean_dec(v___y_8969_);
                crate::leanh::lean_dec(v___y_8967_);
                crate::leanh::lean_inc_ref(v_tree_8937_);
                if v_isShared_8963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8962_, 4, v_tree_8937_);
                    crate::leanh::lean_ctor_set(v___x_8962_, 3, v_r_8957_);
                    crate::leanh::lean_ctor_set(v___x_8962_, 2, v_v_8939_);
                    crate::leanh::lean_ctor_set(v___x_8962_, 1, v_k_8938_);
                    crate::leanh::lean_ctor_set(v___x_8962_, 0, v___x_8970_);
                    v___x_8972_ = v___x_8962_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_8985_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8985_, 0, v___x_8970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8985_, 1, v_k_8938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8985_, 2, v_v_8939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8985_, 3, v_r_8957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8985_, 4, v_tree_8937_);
                    v___x_8972_ = v_reuseFailAlloc_8985_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_8979_ = (!crate::leanh::lean_is_exclusive(v_tree_8937_)) as u8;
                if v_isSharedCheck_8979_ == 0 {
                    v_unused_8980_ = crate::leanh::lean_ctor_get(v_tree_8937_, 4);
                    crate::leanh::lean_dec(v_unused_8980_);
                    v_unused_8981_ = crate::leanh::lean_ctor_get(v_tree_8937_, 3);
                    crate::leanh::lean_dec(v_unused_8981_);
                    v_unused_8982_ = crate::leanh::lean_ctor_get(v_tree_8937_, 2);
                    crate::leanh::lean_dec(v_unused_8982_);
                    v_unused_8983_ = crate::leanh::lean_ctor_get(v_tree_8937_, 1);
                    crate::leanh::lean_dec(v_unused_8983_);
                    v_unused_8984_ = crate::leanh::lean_ctor_get(v_tree_8937_, 0);
                    crate::leanh::lean_dec(v_unused_8984_);
                    v___x_8974_ = v_tree_8937_;
                    v_isShared_8975_ = v_isSharedCheck_8979_;
                    state = 57;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_8937_);
                    v___x_8974_ = crate::leanh::lean_box(0);
                    v_isShared_8975_ = v_isSharedCheck_8979_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_8975_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8974_, 4, v___x_8972_);
                    crate::leanh::lean_ctor_set(v___x_8974_, 3, v___y_8968_);
                    crate::leanh::lean_ctor_set(v___x_8974_, 2, v_v_8955_);
                    crate::leanh::lean_ctor_set(v___x_8974_, 1, v_k_8954_);
                    crate::leanh::lean_ctor_set(v___x_8974_, 0, v___x_8965_);
                    v___x_8977_ = v___x_8974_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_8978_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8978_, 0, v___x_8965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8978_, 1, v_k_8954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8978_, 2, v_v_8955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8978_, 3, v___y_8968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8978_, 4, v___x_8972_);
                    v___x_8977_ = v_reuseFailAlloc_8978_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_8977_;
            }
            59 => {
                v___x_8989_ = lean_nat_add(v___x_8986_, v___y_8988_);
                crate::leanh::lean_dec(v___y_8988_);
                crate::leanh::lean_dec(v___x_8986_);
                if v_isShared_8935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8934_, 4, v_l_8956_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 2, v_v_8782_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 1, v_k_8781_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 0, v___x_8989_);
                    v___x_8991_ = v___x_8934_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_8995_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8995_, 0, v___x_8989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8995_, 1, v_k_8781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8995_, 2, v_v_8782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8995_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8995_, 4, v_l_8956_);
                    v___x_8991_ = v_reuseFailAlloc_8995_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_8992_ = lean_nat_add(v___x_8790_, v_size_8940_);
                if crate::leanh::lean_obj_tag(v_r_8957_) == 0 {
                    v_size_8993_ = crate::leanh::lean_ctor_get(v_r_8957_, 0);
                    crate::leanh::lean_inc(v_size_8993_);
                    v___y_8967_ = v___x_8992_;
                    v___y_8968_ = v___x_8991_;
                    v___y_8969_ = v_size_8993_;
                    state = 55;
                    continue;
                } else {
                    v___x_8994_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_8967_ = v___x_8992_;
                    v___y_8968_ = v___x_8991_;
                    v___y_8969_ = v___x_8994_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_8951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8950_, 4, v___x_9009_);
                    crate::leanh::lean_ctor_set(v___x_8950_, 0, v___x_9005_);
                    v___x_9011_ = v___x_8950_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_9012_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9012_, 0, v___x_9005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9012_, 1, v_k_8781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9012_, 2, v_v_8782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9012_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9012_, 4, v___x_9009_);
                    v___x_9011_ = v_reuseFailAlloc_9012_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_9011_;
            }
            63 => {
                if crate::leanh::lean_obj_tag(v_r_8784_) == 0 {
                    v_k_9023_ = crate::leanh::lean_ctor_get(v___x_8936_, 0);
                    crate::leanh::lean_inc(v_k_9023_);
                    v_v_9024_ = crate::leanh::lean_ctor_get(v___x_8936_, 1);
                    crate::leanh::lean_inc(v_v_9024_);
                    crate::leanh::lean_dec_ref(v___x_8936_);
                    v_size_9025_ = crate::leanh::lean_ctor_get(v_r_8784_, 0);
                    v___x_9026_ = lean_nat_add(v___x_8790_, v_size_8780_);
                    crate::leanh::lean_dec(v_size_8780_);
                    v___x_9027_ = lean_nat_add(v___x_8790_, v_size_9025_);
                    if v_isShared_8935_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8934_, 4, v_tree_8937_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 3, v_r_8784_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 2, v_v_9024_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 1, v_k_9023_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 0, v___x_9027_);
                        v___x_9029_ = v___x_8934_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_9033_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9033_, 0, v___x_9027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9033_, 1, v_k_9023_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9033_, 2, v_v_9024_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9033_, 3, v_r_8784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9033_, 4, v_tree_8937_);
                        v___x_9029_ = v_reuseFailAlloc_9033_;
                        state = 64;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_8780_);
                    v_k_9034_ = crate::leanh::lean_ctor_get(v___x_8936_, 0);
                    crate::leanh::lean_inc(v_k_9034_);
                    v_v_9035_ = crate::leanh::lean_ctor_get(v___x_8936_, 1);
                    crate::leanh::lean_inc(v_v_9035_);
                    crate::leanh::lean_dec_ref(v___x_8936_);
                    v___x_9036_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_8935_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8934_, 4, v_r_8784_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 3, v_r_8784_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 2, v_v_9035_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 1, v_k_9034_);
                        crate::leanh::lean_ctor_set(v___x_8934_, 0, v___x_8790_);
                        v___x_9038_ = v___x_8934_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_9042_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9042_, 0, v___x_8790_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9042_, 1, v_k_9034_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9042_, 2, v_v_9035_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9042_, 3, v_r_8784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9042_, 4, v_r_8784_);
                        v___x_9038_ = v_reuseFailAlloc_9042_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_9022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9021_, 4, v___x_9029_);
                    crate::leanh::lean_ctor_set(v___x_9021_, 0, v___x_9026_);
                    v___x_9031_ = v___x_9021_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_9032_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9032_, 0, v___x_9026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9032_, 1, v_k_8781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9032_, 2, v_v_8782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9032_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9032_, 4, v___x_9029_);
                    v___x_9031_ = v_reuseFailAlloc_9032_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_9031_;
            }
            66 => {
                if v_isShared_9022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9021_, 4, v___x_9038_);
                    crate::leanh::lean_ctor_set(v___x_9021_, 0, v___x_9036_);
                    v___x_9040_ = v___x_9021_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_9041_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9041_, 0, v___x_9036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9041_, 1, v_k_8781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9041_, 2, v_v_8782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9041_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9041_, 4, v___x_9038_);
                    v___x_9040_ = v_reuseFailAlloc_9041_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_9040_;
            }
            68 => {
                v_k_9052_ = crate::leanh::lean_ctor_get(v___x_8936_, 0);
                crate::leanh::lean_inc(v_k_9052_);
                v_v_9053_ = crate::leanh::lean_ctor_get(v___x_8936_, 1);
                crate::leanh::lean_inc(v_v_9053_);
                crate::leanh::lean_dec_ref(v___x_8936_);
                v_k_9054_ = crate::leanh::lean_ctor_get(v_r_8784_, 1);
                v_v_9055_ = crate::leanh::lean_ctor_get(v_r_8784_, 2);
                v_isSharedCheck_9069_ = (!crate::leanh::lean_is_exclusive(v_r_8784_)) as u8;
                if v_isSharedCheck_9069_ == 0 {
                    v_unused_9070_ = crate::leanh::lean_ctor_get(v_r_8784_, 4);
                    crate::leanh::lean_dec(v_unused_9070_);
                    v_unused_9071_ = crate::leanh::lean_ctor_get(v_r_8784_, 3);
                    crate::leanh::lean_dec(v_unused_9071_);
                    v_unused_9072_ = crate::leanh::lean_ctor_get(v_r_8784_, 0);
                    crate::leanh::lean_dec(v_unused_9072_);
                    v___x_9057_ = v_r_8784_;
                    v_isShared_9058_ = v_isSharedCheck_9069_;
                    state = 69;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_9055_);
                    crate::leanh::lean_inc(v_k_9054_);
                    crate::leanh::lean_dec(v_r_8784_);
                    v___x_9057_ = crate::leanh::lean_box(0);
                    v_isShared_9058_ = v_isSharedCheck_9069_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_9059_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_9058_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9057_, 4, v_l_8783_);
                    crate::leanh::lean_ctor_set(v___x_9057_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v___x_9057_, 2, v_v_8782_);
                    crate::leanh::lean_ctor_set(v___x_9057_, 1, v_k_8781_);
                    crate::leanh::lean_ctor_set(v___x_9057_, 0, v___x_8790_);
                    v___x_9061_ = v___x_9057_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_9068_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9068_, 0, v___x_8790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9068_, 1, v_k_8781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9068_, 2, v_v_8782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9068_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9068_, 4, v_l_8783_);
                    v___x_9061_ = v_reuseFailAlloc_9068_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_8935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8934_, 4, v_l_8783_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 2, v_v_9053_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 1, v_k_9052_);
                    crate::leanh::lean_ctor_set(v___x_8934_, 0, v___x_8790_);
                    v___x_9063_ = v___x_8934_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_9067_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9067_, 0, v___x_8790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9067_, 1, v_k_9052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9067_, 2, v_v_9053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9067_, 3, v_l_8783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9067_, 4, v_l_8783_);
                    v___x_9063_ = v_reuseFailAlloc_9067_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_9051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9050_, 4, v___x_9063_);
                    crate::leanh::lean_ctor_set(v___x_9050_, 3, v___x_9061_);
                    crate::leanh::lean_ctor_set(v___x_9050_, 2, v_v_9055_);
                    crate::leanh::lean_ctor_set(v___x_9050_, 1, v_k_9054_);
                    crate::leanh::lean_ctor_set(v___x_9050_, 0, v___x_9059_);
                    v___x_9065_ = v___x_9050_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_9066_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9066_, 0, v___x_9059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9066_, 1, v_k_9054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9066_, 2, v_v_9055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9066_, 3, v___x_9061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9066_, 4, v___x_9063_);
                    v___x_9065_ = v_reuseFailAlloc_9066_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_9065_;
            }
            73 => {
                return v___x_9083_;
            }
            74 => {
                return v___x_9105_;
            }
            75 => {
                v_size_9110_ = crate::leanh::lean_ctor_get(v_l_9097_, 0);
                v_size_9111_ = crate::leanh::lean_ctor_get(v_r_9098_, 0);
                v_k_9112_ = crate::leanh::lean_ctor_get(v_r_9098_, 1);
                v_v_9113_ = crate::leanh::lean_ctor_get(v_r_9098_, 2);
                v_l_9114_ = crate::leanh::lean_ctor_get(v_r_9098_, 3);
                v_r_9115_ = crate::leanh::lean_ctor_get(v_r_9098_, 4);
                v___x_9116_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_9117_ = lean_nat_mul(v___x_9116_, v_size_9110_);
                v___x_9118_ = lean_nat_dec_lt(v_size_9111_, v___x_9117_);
                crate::leanh::lean_dec(v___x_9117_);
                if v___x_9118_ == 0 {
                    crate::leanh::lean_inc(v_r_9115_);
                    crate::leanh::lean_inc(v_l_9114_);
                    crate::leanh::lean_inc(v_v_9113_);
                    crate::leanh::lean_inc(v_k_9112_);
                    v_isSharedCheck_9147_ = (!crate::leanh::lean_is_exclusive(v_r_9098_)) as u8;
                    if v_isSharedCheck_9147_ == 0 {
                        v_unused_9148_ = crate::leanh::lean_ctor_get(v_r_9098_, 4);
                        crate::leanh::lean_dec(v_unused_9148_);
                        v_unused_9149_ = crate::leanh::lean_ctor_get(v_r_9098_, 3);
                        crate::leanh::lean_dec(v_unused_9149_);
                        v_unused_9150_ = crate::leanh::lean_ctor_get(v_r_9098_, 2);
                        crate::leanh::lean_dec(v_unused_9150_);
                        v_unused_9151_ = crate::leanh::lean_ctor_get(v_r_9098_, 1);
                        crate::leanh::lean_dec(v_unused_9151_);
                        v_unused_9152_ = crate::leanh::lean_ctor_get(v_r_9098_, 0);
                        crate::leanh::lean_dec(v_unused_9152_);
                        v___x_9120_ = v_r_9098_;
                        v_isShared_9121_ = v_isSharedCheck_9147_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_9098_);
                        v___x_9120_ = crate::leanh::lean_box(0);
                        v_isShared_9121_ = v_isSharedCheck_9147_;
                        state = 76;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8602_);
                    v___x_9153_ = lean_nat_add(v___x_9092_, v_size_9094_);
                    crate::leanh::lean_dec(v_size_9094_);
                    v___x_9154_ = lean_nat_add(v___x_9153_, v_size_9093_);
                    crate::leanh::lean_dec(v___x_9153_);
                    v___x_9155_ = lean_nat_add(v___x_9092_, v_size_9093_);
                    crate::leanh::lean_dec(v_size_9093_);
                    v___x_9156_ = lean_nat_add(v___x_9155_, v_size_9111_);
                    crate::leanh::lean_dec(v___x_9155_);
                    crate::leanh::lean_inc_ref(v_impl_9091_);
                    if v_isShared_9109_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_9108_, 4, v_impl_9091_);
                        crate::leanh::lean_ctor_set(v___x_9108_, 3, v_r_9098_);
                        crate::leanh::lean_ctor_set(v___x_9108_, 2, v_v_8598_);
                        crate::leanh::lean_ctor_set(v___x_9108_, 1, v_k_8597_);
                        crate::leanh::lean_ctor_set(v___x_9108_, 0, v___x_9156_);
                        v___x_9158_ = v___x_9108_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_9171_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9171_, 0, v___x_9156_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9171_, 1, v_k_8597_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9171_, 2, v_v_8598_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9171_, 3, v_r_9098_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9171_, 4, v_impl_9091_);
                        v___x_9158_ = v_reuseFailAlloc_9171_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_9122_ = lean_nat_add(v___x_9092_, v_size_9094_);
                crate::leanh::lean_dec(v_size_9094_);
                v___x_9123_ = lean_nat_add(v___x_9122_, v_size_9093_);
                crate::leanh::lean_dec(v___x_9122_);
                v___x_9135_ = lean_nat_add(v___x_9092_, v_size_9110_);
                if crate::leanh::lean_obj_tag(v_l_9114_) == 0 {
                    v_size_9145_ = crate::leanh::lean_ctor_get(v_l_9114_, 0);
                    crate::leanh::lean_inc(v_size_9145_);
                    v___y_9137_ = v_size_9145_;
                    state = 80;
                    continue;
                } else {
                    v___x_9146_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_9137_ = v___x_9146_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_9128_ = lean_nat_add(v___y_9125_, v___y_9127_);
                crate::leanh::lean_dec(v___y_9127_);
                crate::leanh::lean_dec(v___y_9125_);
                if v_isShared_9121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9120_, 4, v_impl_9091_);
                    crate::leanh::lean_ctor_set(v___x_9120_, 3, v_r_9115_);
                    crate::leanh::lean_ctor_set(v___x_9120_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v___x_9120_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v___x_9120_, 0, v___x_9128_);
                    v___x_9130_ = v___x_9120_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_9134_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9134_, 0, v___x_9128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9134_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9134_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9134_, 3, v_r_9115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9134_, 4, v_impl_9091_);
                    v___x_9130_ = v_reuseFailAlloc_9134_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_9109_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9108_, 4, v___x_9130_);
                    crate::leanh::lean_ctor_set(v___x_9108_, 3, v___y_9126_);
                    crate::leanh::lean_ctor_set(v___x_9108_, 2, v_v_9113_);
                    crate::leanh::lean_ctor_set(v___x_9108_, 1, v_k_9112_);
                    crate::leanh::lean_ctor_set(v___x_9108_, 0, v___x_9123_);
                    v___x_9132_ = v___x_9108_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_9133_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9133_, 0, v___x_9123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9133_, 1, v_k_9112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9133_, 2, v_v_9113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9133_, 3, v___y_9126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9133_, 4, v___x_9130_);
                    v___x_9132_ = v_reuseFailAlloc_9133_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_9132_;
            }
            80 => {
                v___x_9138_ = lean_nat_add(v___x_9135_, v___y_9137_);
                crate::leanh::lean_dec(v___y_9137_);
                crate::leanh::lean_dec(v___x_9135_);
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v_l_9114_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v_l_9097_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 2, v_v_9096_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 1, v_k_9095_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_9138_);
                    v___x_9140_ = v___x_8602_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_9144_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9144_, 0, v___x_9138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9144_, 1, v_k_9095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9144_, 2, v_v_9096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9144_, 3, v_l_9097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9144_, 4, v_l_9114_);
                    v___x_9140_ = v_reuseFailAlloc_9144_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_9141_ = lean_nat_add(v___x_9092_, v_size_9093_);
                crate::leanh::lean_dec(v_size_9093_);
                if crate::leanh::lean_obj_tag(v_r_9115_) == 0 {
                    v_size_9142_ = crate::leanh::lean_ctor_get(v_r_9115_, 0);
                    crate::leanh::lean_inc(v_size_9142_);
                    v___y_9125_ = v___x_9141_;
                    v___y_9126_ = v___x_9140_;
                    v___y_9127_ = v_size_9142_;
                    state = 77;
                    continue;
                } else {
                    v___x_9143_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_9125_ = v___x_9141_;
                    v___y_9126_ = v___x_9140_;
                    v___y_9127_ = v___x_9143_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_9165_ = (!crate::leanh::lean_is_exclusive(v_impl_9091_)) as u8;
                if v_isSharedCheck_9165_ == 0 {
                    v_unused_9166_ = crate::leanh::lean_ctor_get(v_impl_9091_, 4);
                    crate::leanh::lean_dec(v_unused_9166_);
                    v_unused_9167_ = crate::leanh::lean_ctor_get(v_impl_9091_, 3);
                    crate::leanh::lean_dec(v_unused_9167_);
                    v_unused_9168_ = crate::leanh::lean_ctor_get(v_impl_9091_, 2);
                    crate::leanh::lean_dec(v_unused_9168_);
                    v_unused_9169_ = crate::leanh::lean_ctor_get(v_impl_9091_, 1);
                    crate::leanh::lean_dec(v_unused_9169_);
                    v_unused_9170_ = crate::leanh::lean_ctor_get(v_impl_9091_, 0);
                    crate::leanh::lean_dec(v_unused_9170_);
                    v___x_9160_ = v_impl_9091_;
                    v_isShared_9161_ = v_isSharedCheck_9165_;
                    state = 83;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_9091_);
                    v___x_9160_ = crate::leanh::lean_box(0);
                    v_isShared_9161_ = v_isSharedCheck_9165_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_9161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9160_, 4, v___x_9158_);
                    crate::leanh::lean_ctor_set(v___x_9160_, 3, v_l_9097_);
                    crate::leanh::lean_ctor_set(v___x_9160_, 2, v_v_9096_);
                    crate::leanh::lean_ctor_set(v___x_9160_, 1, v_k_9095_);
                    crate::leanh::lean_ctor_set(v___x_9160_, 0, v___x_9154_);
                    v___x_9163_ = v___x_9160_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_9164_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9164_, 0, v___x_9154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9164_, 1, v_k_9095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9164_, 2, v_v_9096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9164_, 3, v_l_9097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9164_, 4, v___x_9158_);
                    v___x_9163_ = v_reuseFailAlloc_9164_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_9163_;
            }
            85 => {
                return v___x_9181_;
            }
            86 => {
                v_size_9191_ = crate::leanh::lean_ctor_get(v_r_9184_, 0);
                v___x_9192_ = lean_nat_add(v___x_9092_, v_size_9185_);
                crate::leanh::lean_dec(v_size_9185_);
                v___x_9193_ = lean_nat_add(v___x_9092_, v_size_9191_);
                if v_isShared_9190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9189_, 4, v_impl_9091_);
                    crate::leanh::lean_ctor_set(v___x_9189_, 3, v_r_9184_);
                    crate::leanh::lean_ctor_set(v___x_9189_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v___x_9189_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v___x_9189_, 0, v___x_9193_);
                    v___x_9195_ = v___x_9189_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_9199_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9199_, 0, v___x_9193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9199_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9199_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9199_, 3, v_r_9184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9199_, 4, v_impl_9091_);
                    v___x_9195_ = v_reuseFailAlloc_9199_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v___x_9195_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v_l_9183_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 2, v_v_9187_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 1, v_k_9186_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_9192_);
                    v___x_9197_ = v___x_8602_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_9198_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9198_, 0, v___x_9192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9198_, 1, v_k_9186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9198_, 2, v_v_9187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9198_, 3, v_l_9183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9198_, 4, v___x_9195_);
                    v___x_9197_ = v_reuseFailAlloc_9198_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_9197_;
            }
            89 => {
                v___x_9208_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_9207_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9206_, 3, v_r_9184_);
                    crate::leanh::lean_ctor_set(v___x_9206_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v___x_9206_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v___x_9206_, 0, v___x_9092_);
                    v___x_9210_ = v___x_9206_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_9214_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9214_, 0, v___x_9092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9214_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9214_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9214_, 3, v_r_9184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9214_, 4, v_r_9184_);
                    v___x_9210_ = v_reuseFailAlloc_9214_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v___x_9210_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v_l_9183_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 2, v_v_9204_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 1, v_k_9203_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_9208_);
                    v___x_9212_ = v___x_8602_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_9213_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9213_, 0, v___x_9208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9213_, 1, v_k_9203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9213_, 2, v_v_9204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9213_, 3, v_l_9183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9213_, 4, v___x_9210_);
                    v___x_9212_ = v_reuseFailAlloc_9213_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_9212_;
            }
            92 => {
                v_k_9225_ = crate::leanh::lean_ctor_get(v_r_9219_, 1);
                v_v_9226_ = crate::leanh::lean_ctor_get(v_r_9219_, 2);
                v_isSharedCheck_9240_ = (!crate::leanh::lean_is_exclusive(v_r_9219_)) as u8;
                if v_isSharedCheck_9240_ == 0 {
                    v_unused_9241_ = crate::leanh::lean_ctor_get(v_r_9219_, 4);
                    crate::leanh::lean_dec(v_unused_9241_);
                    v_unused_9242_ = crate::leanh::lean_ctor_get(v_r_9219_, 3);
                    crate::leanh::lean_dec(v_unused_9242_);
                    v_unused_9243_ = crate::leanh::lean_ctor_get(v_r_9219_, 0);
                    crate::leanh::lean_dec(v_unused_9243_);
                    v___x_9228_ = v_r_9219_;
                    v_isShared_9229_ = v_isSharedCheck_9240_;
                    state = 93;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_9226_);
                    crate::leanh::lean_inc(v_k_9225_);
                    crate::leanh::lean_dec(v_r_9219_);
                    v___x_9228_ = crate::leanh::lean_box(0);
                    v_isShared_9229_ = v_isSharedCheck_9240_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_9230_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_9229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9228_, 4, v_l_9183_);
                    crate::leanh::lean_ctor_set(v___x_9228_, 3, v_l_9183_);
                    crate::leanh::lean_ctor_set(v___x_9228_, 2, v_v_9221_);
                    crate::leanh::lean_ctor_set(v___x_9228_, 1, v_k_9220_);
                    crate::leanh::lean_ctor_set(v___x_9228_, 0, v___x_9092_);
                    v___x_9232_ = v___x_9228_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_9239_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9239_, 0, v___x_9092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9239_, 1, v_k_9220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9239_, 2, v_v_9221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9239_, 3, v_l_9183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9239_, 4, v_l_9183_);
                    v___x_9232_ = v_reuseFailAlloc_9239_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_9224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9223_, 4, v_l_9183_);
                    crate::leanh::lean_ctor_set(v___x_9223_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v___x_9223_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v___x_9223_, 0, v___x_9092_);
                    v___x_9234_ = v___x_9223_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_9238_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9238_, 0, v___x_9092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9238_, 1, v_k_8597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9238_, 2, v_v_8598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9238_, 3, v_l_9183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9238_, 4, v_l_9183_);
                    v___x_9234_ = v_reuseFailAlloc_9238_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_8603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8602_, 4, v___x_9234_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 3, v___x_9232_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 2, v_v_9226_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 1, v_k_9225_);
                    crate::leanh::lean_ctor_set(v___x_8602_, 0, v___x_9230_);
                    v___x_9236_ = v___x_8602_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_9237_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9237_, 0, v___x_9230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9237_, 1, v_k_9225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9237_, 2, v_v_9226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9237_, 3, v___x_9232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9237_, 4, v___x_9234_);
                    v___x_9236_ = v_reuseFailAlloc_9237_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_9236_;
            }
            97 => {
                return v___x_9250_;
            }
            98 => {
                return v___x_9253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(
    mut v_cmp_9257_: *mut crate::leanh::LeanObject,
    mut v_init_9258_: *mut crate::leanh::LeanObject,
    mut v_x_9259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_9260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_9261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_9262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_9265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_9259_) == 0 {
                    v_k_9260_ = crate::leanh::lean_ctor_get(v_x_9259_, 1);
                    crate::leanh::lean_inc(v_k_9260_);
                    v_l_9261_ = crate::leanh::lean_ctor_get(v_x_9259_, 3);
                    crate::leanh::lean_inc(v_l_9261_);
                    v_r_9262_ = crate::leanh::lean_ctor_get(v_x_9259_, 4);
                    crate::leanh::lean_inc(v_r_9262_);
                    crate::leanh::lean_dec_ref_known(v_x_9259_, 5);
                    crate::leanh::lean_inc_ref_n(v_cmp_9257_, 2);
                    v___x_9263_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_9257_, v_init_9258_, v_l_9261_);
                    v_a_9264_ = crate::leanh::lean_ctor_get(v___x_9263_, 0);
                    crate::leanh::lean_inc(v_a_9264_);
                    crate::leanh::lean_dec_ref(v___x_9263_);
                    v_r_9265_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_9257_, v_k_9260_, v_a_9264_);
                    v_init_9258_ = v_r_9265_;
                    v_x_9259_ = v_r_9262_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_9257_);
                    v___x_9267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_9267_, 0, v_init_9258_);
                    return v___x_9267_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(
    mut v_cmp_9268_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_9269_: *mut crate::leanh::LeanObject,
    mut v_t_9270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_9270_) == 0 {
        let mut v_k_9271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_9272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_9273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_9274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9275_: u8 = 0;
        v_k_9271_ = crate::leanh::lean_ctor_get(v_t_9270_, 1);
        crate::leanh::lean_inc_n(v_k_9271_, 2);
        v_v_9272_ = crate::leanh::lean_ctor_get(v_t_9270_, 2);
        crate::leanh::lean_inc(v_v_9272_);
        v_l_9273_ = crate::leanh::lean_ctor_get(v_t_9270_, 3);
        crate::leanh::lean_inc(v_l_9273_);
        v_r_9274_ = crate::leanh::lean_ctor_get(v_t_9270_, 4);
        crate::leanh::lean_inc(v_r_9274_);
        crate::leanh::lean_dec_ref_known(v_t_9270_, 5);
        crate::leanh::lean_inc(v_t_u2082_9269_);
        crate::leanh::lean_inc_ref(v_cmp_9268_);
        v___x_9275_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0_spec__0___redArg(v_cmp_9268_, v_k_9271_, v_t_u2082_9269_);
        if v___x_9275_ == 0 {
            let mut v_impl_9276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_impl_9277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_t_u2082_9269_);
            crate::leanh::lean_inc_ref(v_cmp_9268_);
            v_impl_9276_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_9268_, v_t_u2082_9269_, v_l_9273_);
            v_impl_9277_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_9268_, v_t_u2082_9269_, v_r_9274_);
            v___x_9278_ = l_Std_DTreeMap_Internal_Impl_link___redArg(
                v_k_9271_,
                v_v_9272_,
                v_impl_9276_,
                v_impl_9277_,
            );
            return v___x_9278_;
        } else {
            let mut v_impl_9279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_impl_9280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_v_9272_);
            crate::leanh::lean_dec(v_k_9271_);
            crate::leanh::lean_inc(v_t_u2082_9269_);
            crate::leanh::lean_inc_ref(v_cmp_9268_);
            v_impl_9279_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_9268_, v_t_u2082_9269_, v_l_9273_);
            v_impl_9280_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_9268_, v_t_u2082_9269_, v_r_9274_);
            v___x_9281_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_9279_, v_impl_9280_);
            return v___x_9281_;
        }
    } else {
        crate::leanh::lean_dec(v_t_u2082_9269_);
        crate::leanh::lean_dec_ref(v_cmp_9268_);
        return v_t_9270_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
    mut v_cmp_9282_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_9283_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_9284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_9286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9288_: u8 = 0;
    let mut v___x_9289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_9296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_u2081_9283_) == 0 {
                    v_size_9296_ = crate::leanh::lean_ctor_get(v_t_u2081_9283_, 0);
                    crate::leanh::lean_inc(v_size_9296_);
                    v___y_9293_ = v_size_9296_;
                    state = 2;
                    continue;
                } else {
                    v___x_9297_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_9293_ = v___x_9297_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_9288_ = lean_nat_dec_le(v___y_9286_, v___y_9287_);
                crate::leanh::lean_dec(v___y_9287_);
                crate::leanh::lean_dec(v___y_9286_);
                if v___x_9288_ == 0 {
                    v___x_9289_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_9282_, v_t_u2081_9283_, v_t_u2082_9284_);
                    v_a_9290_ = crate::leanh::lean_ctor_get(v___x_9289_, 0);
                    crate::leanh::lean_inc(v_a_9290_);
                    crate::leanh::lean_dec_ref(v___x_9289_);
                    return v_a_9290_;
                } else {
                    v___x_9291_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_9282_, v_t_u2082_9284_, v_t_u2081_9283_);
                    return v___x_9291_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_t_u2082_9284_) == 0 {
                    v_size_9294_ = crate::leanh::lean_ctor_get(v_t_u2082_9284_, 0);
                    crate::leanh::lean_inc(v_size_9294_);
                    v___y_9286_ = v___y_9293_;
                    v___y_9287_ = v_size_9294_;
                    state = 1;
                    continue;
                } else {
                    v___x_9295_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_9286_ = v___y_9293_;
                    v___y_9287_ = v___x_9295_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_diff___redArg(
    mut v_cmp_9298_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_9299_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_9300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9301_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_9298_,
        v_t_u2081_9299_,
        v_t_u2082_9300_,
    );
    return v___x_9301_;
}
pub unsafe fn l_Std_DTreeMap_diff(
    mut v_00_u03b1_9302_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9303_: *mut crate::leanh::LeanObject,
    mut v_cmp_9304_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_9305_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_9306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9307_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_9304_,
        v_t_u2081_9305_,
        v_t_u2082_9306_,
    );
    return v___x_9307_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0(
    mut v_00_u03b1_9308_: *mut crate::leanh::LeanObject,
    mut v_cmp_9309_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9310_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_9311_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_9312_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_9313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9314_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_9309_,
        v_t_u2081_9311_,
        v_t_u2082_9312_,
    );
    return v___x_9314_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0(
    mut v_00_u03b1_9315_: *mut crate::leanh::LeanObject,
    mut v_cmp_9316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9317_: *mut crate::leanh::LeanObject,
    mut v_k_9318_: *mut crate::leanh::LeanObject,
    mut v_t_9319_: *mut crate::leanh::LeanObject,
    mut v_h_9320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9321_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__0___redArg(v_cmp_9316_, v_k_9318_, v_t_9319_);
    return v___x_9321_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1(
    mut v_00_u03b1_9322_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9323_: *mut crate::leanh::LeanObject,
    mut v_cmp_9324_: *mut crate::leanh::LeanObject,
    mut v_init_9325_: *mut crate::leanh::LeanObject,
    mut v_x_9326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9327_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__1___redArg(v_cmp_9324_, v_init_9325_, v_x_9326_);
    return v___x_9327_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2(
    mut v_00_u03b1_9328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9329_: *mut crate::leanh::LeanObject,
    mut v_cmp_9330_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_9331_: *mut crate::leanh::LeanObject,
    mut v_t_9332_: *mut crate::leanh::LeanObject,
    mut v_hl_9333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9334_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0_spec__2___redArg(v_cmp_9330_, v_t_u2082_9331_, v_t_9332_);
    return v___x_9334_;
}
pub unsafe fn l_Std_DTreeMap_instSDiff___redArg(
    mut v_cmp_9335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9336_ =
        crate::leanh::lean_alloc_closure(l_Std_DTreeMap_diff as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_9336_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9336_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9336_, 2, v_cmp_9335_);
    return v___x_9336_;
}
pub unsafe fn l_Std_DTreeMap_instSDiff(
    mut v_00_u03b1_9337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9338_: *mut crate::leanh::LeanObject,
    mut v_cmp_9339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9340_ =
        crate::leanh::lean_alloc_closure(l_Std_DTreeMap_diff as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_9340_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9340_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9340_, 2, v_cmp_9339_);
    return v___x_9340_;
}
pub unsafe fn l_Std_DTreeMap_eraseMany___redArg___lam__0(
    mut v_cmp_9341_: *mut crate::leanh::LeanObject,
    mut v_a_9342_: *mut crate::leanh::LeanObject,
    mut v_____s_9343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_9344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_9344_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_9341_, v_a_9342_, v_____s_9343_);
    v___x_9345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9345_, 0, v_r_9344_);
    return v___x_9345_;
}
pub unsafe fn l_Std_DTreeMap_eraseMany___redArg(
    mut v_cmp_9346_: *mut crate::leanh::LeanObject,
    mut v_inst_9347_: *mut crate::leanh::LeanObject,
    mut v_t_9348_: *mut crate::leanh::LeanObject,
    mut v_l_9349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_9350_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_9350_, 0, v_cmp_9346_);
    v___x_9351_ = crate::leanh::lean_apply_4(
        v_inst_9347_,
        crate::leanh::lean_box(0),
        v_l_9349_,
        v_t_9348_,
        v___f_9350_,
    );
    return v___x_9351_;
}
pub unsafe fn l_Std_DTreeMap_eraseMany(
    mut v_00_u03b1_9352_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9353_: *mut crate::leanh::LeanObject,
    mut v_cmp_9354_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_9355_: *mut crate::leanh::LeanObject,
    mut v_inst_9356_: *mut crate::leanh::LeanObject,
    mut v_t_9357_: *mut crate::leanh::LeanObject,
    mut v_l_9358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_9359_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_9359_, 0, v_cmp_9354_);
    v___x_9360_ = crate::leanh::lean_apply_4(
        v_inst_9356_,
        crate::leanh::lean_box(0),
        v_l_9358_,
        v_t_9357_,
        v___f_9359_,
    );
    return v___x_9360_;
}
pub unsafe fn l_Std_DTreeMap_Const_insertMany___redArg___lam__0(
    mut v_cmp_9361_: *mut crate::leanh::LeanObject,
    mut v_x_9362_: *mut crate::leanh::LeanObject,
    mut v_____s_9363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_9364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_9365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_9366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_9364_ = crate::leanh::lean_ctor_get(v_x_9362_, 0);
    crate::leanh::lean_inc(v_fst_9364_);
    v_snd_9365_ = crate::leanh::lean_ctor_get(v_x_9362_, 1);
    crate::leanh::lean_inc(v_snd_9365_);
    crate::leanh::lean_dec_ref(v_x_9362_);
    v_r_9366_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_9361_,
        v_fst_9364_,
        v_snd_9365_,
        v_____s_9363_,
    );
    v___x_9367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9367_, 0, v_r_9366_);
    return v___x_9367_;
}
pub unsafe fn l_Std_DTreeMap_Const_insertMany___redArg(
    mut v_cmp_9368_: *mut crate::leanh::LeanObject,
    mut v_inst_9369_: *mut crate::leanh::LeanObject,
    mut v_t_9370_: *mut crate::leanh::LeanObject,
    mut v_l_9371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_9372_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_9372_, 0, v_cmp_9368_);
    v___x_9373_ = crate::leanh::lean_apply_4(
        v_inst_9369_,
        crate::leanh::lean_box(0),
        v_l_9371_,
        v_t_9370_,
        v___f_9372_,
    );
    return v___x_9373_;
}
pub unsafe fn l_Std_DTreeMap_Const_insertMany(
    mut v_00_u03b1_9374_: *mut crate::leanh::LeanObject,
    mut v_cmp_9375_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9376_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_9377_: *mut crate::leanh::LeanObject,
    mut v_inst_9378_: *mut crate::leanh::LeanObject,
    mut v_t_9379_: *mut crate::leanh::LeanObject,
    mut v_l_9380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_9381_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_9381_, 0, v_cmp_9375_);
    v___x_9382_ = crate::leanh::lean_apply_4(
        v_inst_9378_,
        crate::leanh::lean_box(0),
        v_l_9380_,
        v_t_9379_,
        v___f_9381_,
    );
    return v___x_9382_;
}
pub unsafe fn l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0(
    mut v_cmp_9383_: *mut crate::leanh::LeanObject,
    mut v_a_9384_: *mut crate::leanh::LeanObject,
    mut v_____s_9385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9386_: u8 = 0;
    crate::leanh::lean_inc(v_____s_9385_);
    crate::leanh::lean_inc(v_a_9384_);
    crate::leanh::lean_inc_ref(v_cmp_9383_);
    v___x_9386_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_9383_, v_a_9384_, v_____s_9385_);
    if v___x_9386_ == 0 {
        let mut v___x_9387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_9387_ = crate::leanh::lean_box(0);
        v___x_9388_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_9383_,
            v_a_9384_,
            v___x_9387_,
            v_____s_9385_,
        );
        v___x_9389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_9389_, 0, v___x_9388_);
        return v___x_9389_;
    } else {
        let mut v___x_9390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_9384_);
        crate::leanh::lean_dec_ref(v_cmp_9383_);
        v___x_9390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_9390_, 0, v_____s_9385_);
        return v___x_9390_;
    }
}
pub unsafe fn l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg(
    mut v_cmp_9391_: *mut crate::leanh::LeanObject,
    mut v_inst_9392_: *mut crate::leanh::LeanObject,
    mut v_t_9393_: *mut crate::leanh::LeanObject,
    mut v_l_9394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_9395_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_9395_, 0, v_cmp_9391_);
    v___x_9396_ = crate::leanh::lean_apply_4(
        v_inst_9392_,
        crate::leanh::lean_box(0),
        v_l_9394_,
        v_t_9393_,
        v___f_9395_,
    );
    return v___x_9396_;
}
pub unsafe fn l_Std_DTreeMap_Const_insertManyIfNewUnit(
    mut v_00_u03b1_9397_: *mut crate::leanh::LeanObject,
    mut v_cmp_9398_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_9399_: *mut crate::leanh::LeanObject,
    mut v_inst_9400_: *mut crate::leanh::LeanObject,
    mut v_t_9401_: *mut crate::leanh::LeanObject,
    mut v_l_9402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_9403_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Const_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_9403_, 0, v_cmp_9398_);
    v___x_9404_ = crate::leanh::lean_apply_4(
        v_inst_9400_,
        crate::leanh::lean_box(0),
        v_l_9402_,
        v_t_9401_,
        v___f_9403_,
    );
    return v___x_9404_;
}
pub unsafe fn l_Std_DTreeMap_instRepr___redArg___lam__1(
    mut v___f_9408_: *mut crate::leanh::LeanObject,
    mut v___x_9409_: *mut crate::leanh::LeanObject,
    mut v_m_9410_: *mut crate::leanh::LeanObject,
    mut v_prec_9411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9412_ = l_Std_DTreeMap_instRepr___redArg___lam__1___closed__1;
    v___x_9413_ = crate::leanh::lean_box(0);
    v___x_9414_ = l_Std_DTreeMap_foldr___redArg___closed__9;
    v___x_9415_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_9414_,
        v___f_9408_,
        v___x_9413_,
        v_m_9410_,
    );
    v___x_9416_ = l_List_repr___redArg(v___x_9409_, v___x_9415_);
    v___x_9417_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9417_, 0, v___x_9412_);
    crate::leanh::lean_ctor_set(v___x_9417_, 1, v___x_9416_);
    v___x_9418_ = l_Repr_addAppParen(v___x_9417_, v_prec_9411_);
    return v___x_9418_;
}
pub unsafe fn l_Std_DTreeMap_instRepr___redArg___lam__1___boxed(
    mut v___f_9419_: *mut crate::leanh::LeanObject,
    mut v___x_9420_: *mut crate::leanh::LeanObject,
    mut v_m_9421_: *mut crate::leanh::LeanObject,
    mut v_prec_9422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9423_ = l_Std_DTreeMap_instRepr___redArg___lam__1(
        v___f_9419_,
        v___x_9420_,
        v_m_9421_,
        v_prec_9422_,
    );
    crate::leanh::lean_dec(v_prec_9422_);
    return v_res_9423_;
}
pub unsafe fn l_Std_DTreeMap_instRepr___redArg(
    mut v_inst_9424_: *mut crate::leanh::LeanObject,
    mut v_inst_9425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_9426_ = l_Std_DTreeMap_toList___redArg___closed__0;
    v___x_9427_ =
        crate::leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_9427_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9427_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9427_, 2, v_inst_9424_);
    crate::leanh::lean_closure_set(v___x_9427_, 3, v_inst_9425_);
    v___f_9428_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_instRepr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_9428_, 0, v___f_9426_);
    crate::leanh::lean_closure_set(v___f_9428_, 1, v___x_9427_);
    return v___f_9428_;
}
pub unsafe fn l_Std_DTreeMap_instRepr(
    mut v_00_u03b1_9429_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9430_: *mut crate::leanh::LeanObject,
    mut v_cmp_9431_: *mut crate::leanh::LeanObject,
    mut v_inst_9432_: *mut crate::leanh::LeanObject,
    mut v_inst_9433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9434_ = l_Std_DTreeMap_instRepr___redArg(v_inst_9432_, v_inst_9433_);
    return v___x_9434_;
}
pub unsafe fn l_Std_DTreeMap_instRepr___boxed(
    mut v_00_u03b1_9435_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9436_: *mut crate::leanh::LeanObject,
    mut v_cmp_9437_: *mut crate::leanh::LeanObject,
    mut v_inst_9438_: *mut crate::leanh::LeanObject,
    mut v_inst_9439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9440_ = l_Std_DTreeMap_instRepr(
        v_00_u03b1_9435_,
        v_00_u03b2_9436_,
        v_cmp_9437_,
        v_inst_9438_,
        v_inst_9439_,
    );
    crate::leanh::lean_dec_ref(v_cmp_9437_);
    return v_res_9440_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_DTreeMap___auto__1 = _init_l_Std_DTreeMap___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap___auto__1);
    l_Std_DTreeMap_ofList___auto__1 = _init_l_Std_DTreeMap_ofList___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap_ofList___auto__1);
    l_Std_DTreeMap_ofArray___auto__1 = _init_l_Std_DTreeMap_ofArray___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap_ofArray___auto__1);
    l_Std_DTreeMap_Const_ofList___auto__1 = _init_l_Std_DTreeMap_Const_ofList___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap_Const_ofList___auto__1);
    l_Std_DTreeMap_Const_ofArray___auto__1 = _init_l_Std_DTreeMap_Const_ofArray___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap_Const_ofArray___auto__1);
    l_Std_DTreeMap_Const_unitOfList___auto__1 = _init_l_Std_DTreeMap_Const_unitOfList___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap_Const_unitOfList___auto__1);
    l_Std_DTreeMap_Const_unitOfArray___auto__1 = _init_l_Std_DTreeMap_Const_unitOfArray___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_DTreeMap_Const_unitOfArray___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_WF_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Basic(builtin);
}
