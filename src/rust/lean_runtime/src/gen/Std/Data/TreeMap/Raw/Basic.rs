// Lean compiler output
// Module: Std.Data.TreeMap.Raw.Basic
// Imports: Std.Data.DTreeMap.Raw.Basic
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
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_mkAtom, l_Lean_replaceRef, l_String_toRawSubstring_x27,
    l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_beq___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_modify___redArg,
    l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg,
    l_Std_DTreeMap_Internal_Impl_erase_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_filter_x21___redArg, l_Std_DTreeMap_Internal_Impl_insert___redArg,
    l_Std_DTreeMap_Internal_Impl_insert_x21___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
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
    l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg,
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
    initialize_Std_Data_DTreeMap_Raw_Basic,
    l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg,
    runtime_initialize_Std_Data_DTreeMap_Raw_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_string_utf8_byte_size,
};
pub static l_Std_TreeMap_Raw___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeMap_Raw___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeMap_Raw___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeMap_Raw___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeMap_Raw___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_Raw___auto__1___closed__14_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_TreeMap_Raw___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeMap_Raw___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_Raw___auto__1___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16710690322389477741 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeMap_Raw___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_Raw___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeMap_Raw___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [84, 114, 101, 101, 77, 97, 112, 0],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [82, 97, 119, 0],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__3_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            16988956666274133190 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            9119362187006284029 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            7003394003125887999 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__9_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_term___x7em___00__closed__13_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_term___x7em___00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeMap_Raw_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,16988956666274133190 as *mut crate::leanh::LeanObject] };
static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw_term___x7em___00__closed__2_value) as *mut crate::leanh::LeanObject,9119362187006284029 as *mut crate::leanh::LeanObject] };
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,6810441436034836926 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0_value:
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
static mut l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1_value:
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
static mut l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2_value:
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
static mut l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_foldr___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeMap_Raw_foldr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_foldr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_partition___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_TreeMap_Raw_partition___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_partition___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_any___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_TreeMap_Raw_any___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_any___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_keys___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_Raw_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_Raw_keys___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_keys___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_keysArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeMap_Raw_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeMap_Raw_keysArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_keysArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_values___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_Raw_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_Raw_values___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_values___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_TreeMap_Raw_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeMap_Raw_valuesArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_valuesArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_Raw_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeMap_Raw_ofList___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeMap_Raw_unitOfList___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_Raw_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeMap_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeMap_Raw_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeMap_Raw_ofArray___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeMap_Raw_unitOfArray___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        83, 116, 100, 46, 84, 114, 101, 101, 77, 97, 112, 46, 82, 97, 119, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_Std_TreeMap_Raw___auto__1___closed__10;
    v___x_2514_ = l_Lean_mkAtom(v___x_2513_);
    return v___x_2514_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__12_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__12,
    );
    v___x_2516_ = l_Std_TreeMap_Raw___auto__1___closed__5;
    v___x_2517_ = lean_array_push(v___x_2516_, v___x_2515_);
    return v___x_2517_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Std_TreeMap_Raw___auto__1___closed__14;
    v___x_2520_ = lean_string_utf8_byte_size(v___x_2519_);
    return v___x_2520_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__15_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__15,
    );
    v___x_2522_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2523_ = l_Std_TreeMap_Raw___auto__1___closed__14;
    v___x_2524_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2524_, 0, v___x_2523_);
    crate::leanh::lean_ctor_set(v___x_2524_, 1, v___x_2522_);
    crate::leanh::lean_ctor_set(v___x_2524_, 2, v___x_2521_);
    return v___x_2524_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = crate::leanh::lean_box(0);
    v___x_2528_ = l_Std_TreeMap_Raw___auto__1___closed__17;
    v___x_2529_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__16_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__16,
    );
    v___x_2530_ = crate::leanh::lean_box(2);
    v___x_2531_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2531_, 0, v___x_2530_);
    crate::leanh::lean_ctor_set(v___x_2531_, 1, v___x_2529_);
    crate::leanh::lean_ctor_set(v___x_2531_, 2, v___x_2528_);
    crate::leanh::lean_ctor_set(v___x_2531_, 3, v___x_2527_);
    return v___x_2531_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__18_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__18,
    );
    v___x_2533_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__13_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__13,
    );
    v___x_2534_ = lean_array_push(v___x_2533_, v___x_2532_);
    return v___x_2534_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__19_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__19,
    );
    v___x_2536_ = l_Std_TreeMap_Raw___auto__1___closed__11;
    v___x_2537_ = crate::leanh::lean_box(2);
    v___x_2538_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2538_, 0, v___x_2537_);
    crate::leanh::lean_ctor_set(v___x_2538_, 1, v___x_2536_);
    crate::leanh::lean_ctor_set(v___x_2538_, 2, v___x_2535_);
    return v___x_2538_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__20_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__20,
    );
    v___x_2540_ = l_Std_TreeMap_Raw___auto__1___closed__5;
    v___x_2541_ = lean_array_push(v___x_2540_, v___x_2539_);
    return v___x_2541_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__21_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__21,
    );
    v___x_2543_ = l_Std_TreeMap_Raw___auto__1___closed__9;
    v___x_2544_ = crate::leanh::lean_box(2);
    v___x_2545_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    crate::leanh::lean_ctor_set(v___x_2545_, 1, v___x_2543_);
    crate::leanh::lean_ctor_set(v___x_2545_, 2, v___x_2542_);
    return v___x_2545_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__22_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__22,
    );
    v___x_2547_ = l_Std_TreeMap_Raw___auto__1___closed__5;
    v___x_2548_ = lean_array_push(v___x_2547_, v___x_2546_);
    return v___x_2548_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2549_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__23_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__23,
    );
    v___x_2550_ = l_Std_TreeMap_Raw___auto__1___closed__7;
    v___x_2551_ = crate::leanh::lean_box(2);
    v___x_2552_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2551_);
    crate::leanh::lean_ctor_set(v___x_2552_, 1, v___x_2550_);
    crate::leanh::lean_ctor_set(v___x_2552_, 2, v___x_2549_);
    return v___x_2552_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__24_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__24,
    );
    v___x_2554_ = l_Std_TreeMap_Raw___auto__1___closed__5;
    v___x_2555_ = lean_array_push(v___x_2554_, v___x_2553_);
    return v___x_2555_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2556_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__25_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__25,
    );
    v___x_2557_ = l_Std_TreeMap_Raw___auto__1___closed__4;
    v___x_2558_ = crate::leanh::lean_box(2);
    v___x_2559_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2559_, 0, v___x_2558_);
    crate::leanh::lean_ctor_set(v___x_2559_, 1, v___x_2557_);
    crate::leanh::lean_ctor_set(v___x_2559_, 2, v___x_2556_);
    return v___x_2559_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2560_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__26,
    );
    return v___x_2560_;
}
pub unsafe fn l_Std_TreeMap_Raw_instCoeWFWFInner(
    mut v_00_u03b1_2561_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2562_: *mut crate::leanh::LeanObject,
    mut v_cmp_2563_: *mut crate::leanh::LeanObject,
    mut v_t_2564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2565_ = crate::leanh::lean_box(0);
    return v___x_2565_;
}
pub unsafe fn l_Std_TreeMap_Raw_instCoeWFWFInner___boxed(
    mut v_00_u03b1_2566_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2567_: *mut crate::leanh::LeanObject,
    mut v_cmp_2568_: *mut crate::leanh::LeanObject,
    mut v_t_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Std_TreeMap_Raw_instCoeWFWFInner(
        v_00_u03b1_2566_,
        v_00_u03b2_2567_,
        v_cmp_2568_,
        v_t_2569_,
    );
    crate::leanh::lean_dec(v_t_2569_);
    crate::leanh::lean_dec_ref(v_cmp_2568_);
    return v_res_2570_;
}
pub unsafe fn l_Std_TreeMap_Raw_empty(
    mut v_00_u03b1_2571_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2572_: *mut crate::leanh::LeanObject,
    mut v_cmp_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2574_ = crate::leanh::lean_box(1);
    return v___x_2574_;
}
pub unsafe fn l_Std_TreeMap_Raw_empty___boxed(
    mut v_00_u03b1_2575_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2576_: *mut crate::leanh::LeanObject,
    mut v_cmp_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2578_ = l_Std_TreeMap_Raw_empty(v_00_u03b1_2575_, v_00_u03b2_2576_, v_cmp_2577_);
    crate::leanh::lean_dec_ref(v_cmp_2577_);
    return v_res_2578_;
}
pub unsafe fn l_Std_TreeMap_Raw_instEmptyCollection(
    mut v_00_u03b1_2579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2580_: *mut crate::leanh::LeanObject,
    mut v_cmp_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ = crate::leanh::lean_box(1);
    return v___x_2582_;
}
pub unsafe fn l_Std_TreeMap_Raw_instEmptyCollection___boxed(
    mut v_00_u03b1_2583_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2584_: *mut crate::leanh::LeanObject,
    mut v_cmp_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2586_ =
        l_Std_TreeMap_Raw_instEmptyCollection(v_00_u03b1_2583_, v_00_u03b2_2584_, v_cmp_2585_);
    crate::leanh::lean_dec_ref(v_cmp_2585_);
    return v_res_2586_;
}
pub unsafe fn l_Std_TreeMap_Raw_instInhabited(
    mut v_00_u03b1_2587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2588_: *mut crate::leanh::LeanObject,
    mut v_cmp_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = crate::leanh::lean_box(1);
    return v___x_2590_;
}
pub unsafe fn l_Std_TreeMap_Raw_instInhabited___boxed(
    mut v_00_u03b1_2591_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2592_: *mut crate::leanh::LeanObject,
    mut v_cmp_2593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2594_ = l_Std_TreeMap_Raw_instInhabited(v_00_u03b1_2591_, v_00_u03b2_2592_, v_cmp_2593_);
    crate::leanh::lean_dec_ref(v_cmp_2593_);
    return v_res_2594_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2634_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__3;
    v___x_2635_ = l_String_toRawSubstring_x27(v___x_2634_);
    return v___x_2635_;
}
pub unsafe fn l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(
    mut v_x_2654_: *mut crate::leanh::LeanObject,
    mut v_a_2655_: *mut crate::leanh::LeanObject,
    mut v_a_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: u8 = 0;
    v___x_2657_ = l_Std_TreeMap_Raw_term___x7em___00__closed__4;
    crate::leanh::lean_inc(v_x_2654_);
    v___x_2658_ = l_Lean_Syntax_isOfKind(v_x_2654_, v___x_2657_);
    if v___x_2658_ == 0 {
        let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2654_);
        v___x_2659_ = crate::leanh::lean_box(1);
        v___x_2660_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2660_, 0, v___x_2659_);
        crate::leanh::lean_ctor_set(v___x_2660_, 1, v_a_2656_);
        return v___x_2660_;
    } else {
        let mut v_quotContext_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2668_: u8 = 0;
        let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2661_ = crate::leanh::lean_ctor_get(v_a_2655_, 1);
        v_currMacroScope_2662_ = crate::leanh::lean_ctor_get(v_a_2655_, 2);
        v_ref_2663_ = crate::leanh::lean_ctor_get(v_a_2655_, 5);
        v___x_2664_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2665_ = l_Lean_Syntax_getArg(v_x_2654_, v___x_2664_);
        v___x_2666_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2667_ = l_Lean_Syntax_getArg(v_x_2654_, v___x_2666_);
        crate::leanh::lean_dec(v_x_2654_);
        v___x_2668_ = 0;
        v___x_2669_ = l_Lean_SourceInfo_fromRef(v_ref_2663_, v___x_2668_);
        v___x_2670_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2;
        v___x_2671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4), core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4_once), _init_l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__4);
        v___x_2672_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__5;
        crate::leanh::lean_inc(v_currMacroScope_2662_);
        crate::leanh::lean_inc(v_quotContext_2661_);
        v___x_2673_ =
            l_Lean_addMacroScope(v_quotContext_2661_, v___x_2672_, v_currMacroScope_2662_);
        v___x_2674_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__10;
        crate::leanh::lean_inc_n(v___x_2669_, 2);
        v___x_2675_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2675_, 0, v___x_2669_);
        crate::leanh::lean_ctor_set(v___x_2675_, 1, v___x_2671_);
        crate::leanh::lean_ctor_set(v___x_2675_, 2, v___x_2673_);
        crate::leanh::lean_ctor_set(v___x_2675_, 3, v___x_2674_);
        v___x_2676_ = l_Std_TreeMap_Raw___auto__1___closed__9;
        v___x_2677_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2676_, v___x_2665_, v___x_2667_);
        v___x_2678_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2670_, v___x_2675_, v___x_2677_);
        v___x_2679_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2679_, 0, v___x_2678_);
        crate::leanh::lean_ctor_set(v___x_2679_, 1, v_a_2656_);
        return v___x_2679_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___boxed(
    mut v_x_2680_: *mut crate::leanh::LeanObject,
    mut v_a_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2683_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1(v_x_2680_, v_a_2681_, v_a_2682_);
    crate::leanh::lean_dec_ref(v_a_2681_);
    return v_res_2683_;
}
pub unsafe fn l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(
    mut v_x_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    v___x_2690_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______macroRules__Std__TreeMap__Raw__term___x7em____1___closed__2;
    crate::leanh::lean_inc(v_x_2687_);
    v___x_2691_ = l_Lean_Syntax_isOfKind(v_x_2687_, v___x_2690_);
    if v___x_2691_ == 0 {
        let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2687_);
        v___x_2692_ = crate::leanh::lean_box(0);
        v___x_2693_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2693_, 0, v___x_2692_);
        crate::leanh::lean_ctor_set(v___x_2693_, 1, v_a_2689_);
        return v___x_2693_;
    } else {
        let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2697_: u8 = 0;
        v___x_2694_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2695_ = l_Lean_Syntax_getArg(v_x_2687_, v___x_2694_);
        v___x_2696_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_2695_);
        v___x_2697_ = l_Lean_Syntax_isOfKind(v___x_2695_, v___x_2696_);
        if v___x_2697_ == 0 {
            let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2695_);
            crate::leanh::lean_dec(v_x_2687_);
            v___x_2698_ = crate::leanh::lean_box(0);
            v___x_2699_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2699_, 0, v___x_2698_);
            crate::leanh::lean_ctor_set(v___x_2699_, 1, v_a_2689_);
            return v___x_2699_;
        } else {
            let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2703_: u8 = 0;
            v___x_2700_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2701_ = l_Lean_Syntax_getArg(v_x_2687_, v___x_2700_);
            crate::leanh::lean_dec(v_x_2687_);
            v___x_2702_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_2701_);
            v___x_2703_ = l_Lean_Syntax_matchesNull(v___x_2701_, v___x_2702_);
            if v___x_2703_ == 0 {
                let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2701_);
                crate::leanh::lean_dec(v___x_2695_);
                v___x_2704_ = crate::leanh::lean_box(0);
                v___x_2705_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2705_, 0, v___x_2704_);
                crate::leanh::lean_ctor_set(v___x_2705_, 1, v_a_2689_);
                return v___x_2705_;
            } else {
                let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2709_: u8 = 0;
                let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2706_ = l_Lean_Syntax_getArg(v___x_2701_, v___x_2694_);
                v___x_2707_ = l_Lean_Syntax_getArg(v___x_2701_, v___x_2700_);
                crate::leanh::lean_dec(v___x_2701_);
                v_ref_2708_ = l_Lean_replaceRef(v___x_2695_, v_a_2688_);
                crate::leanh::lean_dec(v___x_2695_);
                v___x_2709_ = 0;
                v___x_2710_ = l_Lean_SourceInfo_fromRef(v_ref_2708_, v___x_2709_);
                crate::leanh::lean_dec(v_ref_2708_);
                v___x_2711_ = l_Std_TreeMap_Raw_term___x7em___00__closed__4;
                v___x_2712_ = l_Std_TreeMap_Raw_term___x7em___00__closed__7;
                crate::leanh::lean_inc(v___x_2710_);
                v___x_2713_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2713_, 0, v___x_2710_);
                crate::leanh::lean_ctor_set(v___x_2713_, 1, v___x_2712_);
                v___x_2714_ = l_Lean_Syntax_node3(
                    v___x_2710_,
                    v___x_2711_,
                    v___x_2706_,
                    v___x_2713_,
                    v___x_2707_,
                );
                v___x_2715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2715_, 0, v___x_2714_);
                crate::leanh::lean_ctor_set(v___x_2715_, 1, v_a_2689_);
                return v___x_2715_;
            }
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1___boxed(
    mut v_x_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Std_TreeMap_Raw___aux__Std__Data__TreeMap__Raw__Basic______unexpand__Std__TreeMap__Raw__Equiv__1(v_x_2716_, v_a_2717_, v_a_2718_);
    crate::leanh::lean_dec(v_a_2717_);
    return v_res_2719_;
}
pub unsafe fn l_Std_TreeMap_Raw_insert___redArg(
    mut v_cmp_2720_: *mut crate::leanh::LeanObject,
    mut v_l_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_b_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2724_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
        v_cmp_2720_,
        v_a_2722_,
        v_b_2723_,
        v_l_2721_,
    );
    return v___x_2724_;
}
pub unsafe fn l_Std_TreeMap_Raw_insert(
    mut v_00_u03b1_2725_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2726_: *mut crate::leanh::LeanObject,
    mut v_cmp_2727_: *mut crate::leanh::LeanObject,
    mut v_l_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_b_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2731_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
        v_cmp_2727_,
        v_a_2729_,
        v_b_2730_,
        v_l_2728_,
    );
    return v___x_2731_;
}
pub unsafe fn l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0(
    mut v_cmp_2732_: *mut crate::leanh::LeanObject,
    mut v_e_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2734_ = crate::leanh::lean_ctor_get(v_e_2733_, 0);
    crate::leanh::lean_inc(v_fst_2734_);
    v_snd_2735_ = crate::leanh::lean_ctor_get(v_e_2733_, 1);
    crate::leanh::lean_inc(v_snd_2735_);
    crate::leanh::lean_dec_ref(v_e_2733_);
    v___x_2736_ = crate::leanh::lean_box(1);
    v___x_2737_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
        v_cmp_2732_,
        v_fst_2734_,
        v_snd_2735_,
        v___x_2736_,
    );
    return v___x_2737_;
}
pub unsafe fn l_Std_TreeMap_Raw_instSingletonProd___redArg(
    mut v_cmp_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2739_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2739_, 0, v_cmp_2738_);
    return v___f_2739_;
}
pub unsafe fn l_Std_TreeMap_Raw_instSingletonProd(
    mut v_00_u03b1_2740_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2741_: *mut crate::leanh::LeanObject,
    mut v_cmp_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2743_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instSingletonProd___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2743_, 0, v_cmp_2742_);
    return v___f_2743_;
}
pub unsafe fn l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0(
    mut v_cmp_2744_: *mut crate::leanh::LeanObject,
    mut v_e_2745_: *mut crate::leanh::LeanObject,
    mut v_s_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2747_ = crate::leanh::lean_ctor_get(v_e_2745_, 0);
    crate::leanh::lean_inc(v_fst_2747_);
    v_snd_2748_ = crate::leanh::lean_ctor_get(v_e_2745_, 1);
    crate::leanh::lean_inc(v_snd_2748_);
    crate::leanh::lean_dec_ref(v_e_2745_);
    v___x_2749_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
        v_cmp_2744_,
        v_fst_2747_,
        v_snd_2748_,
        v_s_2746_,
    );
    return v___x_2749_;
}
pub unsafe fn l_Std_TreeMap_Raw_instInsertProd___redArg(
    mut v_cmp_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2751_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2751_, 0, v_cmp_2750_);
    return v___f_2751_;
}
pub unsafe fn l_Std_TreeMap_Raw_instInsertProd(
    mut v_00_u03b1_2752_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2753_: *mut crate::leanh::LeanObject,
    mut v_cmp_2754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2755_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instInsertProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2755_, 0, v_cmp_2754_);
    return v___f_2755_;
}
pub unsafe fn l_Std_TreeMap_Raw_insertIfNew___redArg(
    mut v_cmp_2756_: *mut crate::leanh::LeanObject,
    mut v_t_2757_: *mut crate::leanh::LeanObject,
    mut v_a_2758_: *mut crate::leanh::LeanObject,
    mut v_b_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2760_: u8 = 0;
    crate::leanh::lean_inc(v_t_2757_);
    crate::leanh::lean_inc(v_a_2758_);
    crate::leanh::lean_inc_ref(v_cmp_2756_);
    v___x_2760_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2756_, v_a_2758_, v_t_2757_);
    if v___x_2760_ == 0 {
        let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2761_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_2756_,
            v_a_2758_,
            v_b_2759_,
            v_t_2757_,
        );
        return v___x_2761_;
    } else {
        crate::leanh::lean_dec(v_b_2759_);
        crate::leanh::lean_dec(v_a_2758_);
        crate::leanh::lean_dec_ref(v_cmp_2756_);
        return v_t_2757_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_insertIfNew(
    mut v_00_u03b1_2762_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2763_: *mut crate::leanh::LeanObject,
    mut v_cmp_2764_: *mut crate::leanh::LeanObject,
    mut v_t_2765_: *mut crate::leanh::LeanObject,
    mut v_a_2766_: *mut crate::leanh::LeanObject,
    mut v_b_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2768_: u8 = 0;
    crate::leanh::lean_inc(v_t_2765_);
    crate::leanh::lean_inc(v_a_2766_);
    crate::leanh::lean_inc_ref(v_cmp_2764_);
    v___x_2768_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2764_, v_a_2766_, v_t_2765_);
    if v___x_2768_ == 0 {
        let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2769_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_2764_,
            v_a_2766_,
            v_b_2767_,
            v_t_2765_,
        );
        return v___x_2769_;
    } else {
        crate::leanh::lean_dec(v_b_2767_);
        crate::leanh::lean_dec(v_a_2766_);
        crate::leanh::lean_dec_ref(v_cmp_2764_);
        return v_t_2765_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_containsThenInsert___redArg(
    mut v_cmp_2770_: *mut crate::leanh::LeanObject,
    mut v_t_2771_: *mut crate::leanh::LeanObject,
    mut v_a_2772_: *mut crate::leanh::LeanObject,
    mut v_b_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2774_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_2771_);
                v_m_2775_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                    v_cmp_2770_,
                    v_a_2772_,
                    v_b_2773_,
                    v_t_2771_,
                );
                if crate::leanh::lean_obj_tag(v_m_2775_) == 0 {
                    v_size_2781_ = crate::leanh::lean_ctor_get(v_m_2775_, 0);
                    crate::leanh::lean_inc(v_size_2781_);
                    v___y_2777_ = v_size_2781_;
                    state = 1;
                    continue;
                } else {
                    v___x_2782_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2777_ = v___x_2782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2778_ = lean_nat_dec_eq(v_sz_2774_, v___y_2777_);
                crate::leanh::lean_dec(v___y_2777_);
                crate::leanh::lean_dec(v_sz_2774_);
                v___x_2779_ = crate::leanh::lean_box((v___x_2778_) as usize);
                v___x_2780_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2780_, 0, v___x_2779_);
                crate::leanh::lean_ctor_set(v___x_2780_, 1, v_m_2775_);
                return v___x_2780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_containsThenInsert(
    mut v_00_u03b1_2783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2784_: *mut crate::leanh::LeanObject,
    mut v_cmp_2785_: *mut crate::leanh::LeanObject,
    mut v_t_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_b_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: u8 = 0;
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2789_ =
                    l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_2786_);
                v_m_2790_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                    v_cmp_2785_,
                    v_a_2787_,
                    v_b_2788_,
                    v_t_2786_,
                );
                if crate::leanh::lean_obj_tag(v_m_2790_) == 0 {
                    v_size_2796_ = crate::leanh::lean_ctor_get(v_m_2790_, 0);
                    crate::leanh::lean_inc(v_size_2796_);
                    v___y_2792_ = v_size_2796_;
                    state = 1;
                    continue;
                } else {
                    v___x_2797_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2792_ = v___x_2797_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2793_ = lean_nat_dec_eq(v_sz_2789_, v___y_2792_);
                crate::leanh::lean_dec(v___y_2792_);
                crate::leanh::lean_dec(v_sz_2789_);
                v___x_2794_ = crate::leanh::lean_box((v___x_2793_) as usize);
                v___x_2795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2795_, 0, v___x_2794_);
                crate::leanh::lean_ctor_set(v___x_2795_, 1, v_m_2790_);
                return v___x_2795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_containsThenInsertIfNew___redArg(
    mut v_cmp_2798_: *mut crate::leanh::LeanObject,
    mut v_t_2799_: *mut crate::leanh::LeanObject,
    mut v_a_2800_: *mut crate::leanh::LeanObject,
    mut v_b_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2802_: u8 = 0;
    crate::leanh::lean_inc(v_t_2799_);
    crate::leanh::lean_inc(v_a_2800_);
    crate::leanh::lean_inc_ref(v_cmp_2798_);
    v___x_2802_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2798_, v_a_2800_, v_t_2799_);
    if v___x_2802_ == 0 {
        let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2803_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_2798_,
            v_a_2800_,
            v_b_2801_,
            v_t_2799_,
        );
        v___x_2804_ = crate::leanh::lean_box((v___x_2802_) as usize);
        v___x_2805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2804_);
        crate::leanh::lean_ctor_set(v___x_2805_, 1, v___x_2803_);
        return v___x_2805_;
    } else {
        let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_2801_);
        crate::leanh::lean_dec(v_a_2800_);
        crate::leanh::lean_dec_ref(v_cmp_2798_);
        v___x_2806_ = crate::leanh::lean_box((v___x_2802_) as usize);
        v___x_2807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2807_, 0, v___x_2806_);
        crate::leanh::lean_ctor_set(v___x_2807_, 1, v_t_2799_);
        return v___x_2807_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_containsThenInsertIfNew(
    mut v_00_u03b1_2808_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2809_: *mut crate::leanh::LeanObject,
    mut v_cmp_2810_: *mut crate::leanh::LeanObject,
    mut v_t_2811_: *mut crate::leanh::LeanObject,
    mut v_a_2812_: *mut crate::leanh::LeanObject,
    mut v_b_2813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2814_: u8 = 0;
    crate::leanh::lean_inc(v_t_2811_);
    crate::leanh::lean_inc(v_a_2812_);
    crate::leanh::lean_inc_ref(v_cmp_2810_);
    v___x_2814_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2810_, v_a_2812_, v_t_2811_);
    if v___x_2814_ == 0 {
        let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2815_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_2810_,
            v_a_2812_,
            v_b_2813_,
            v_t_2811_,
        );
        v___x_2816_ = crate::leanh::lean_box((v___x_2814_) as usize);
        v___x_2817_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2817_, 0, v___x_2816_);
        crate::leanh::lean_ctor_set(v___x_2817_, 1, v___x_2815_);
        return v___x_2817_;
    } else {
        let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_2813_);
        crate::leanh::lean_dec(v_a_2812_);
        crate::leanh::lean_dec_ref(v_cmp_2810_);
        v___x_2818_ = crate::leanh::lean_box((v___x_2814_) as usize);
        v___x_2819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2819_, 0, v___x_2818_);
        crate::leanh::lean_ctor_set(v___x_2819_, 1, v_t_2811_);
        return v___x_2819_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getThenInsertIfNew_x3f___redArg(
    mut v_cmp_2820_: *mut crate::leanh::LeanObject,
    mut v_t_2821_: *mut crate::leanh::LeanObject,
    mut v_a_2822_: *mut crate::leanh::LeanObject,
    mut v_b_2823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2822_);
    crate::leanh::lean_inc(v_t_2821_);
    crate::leanh::lean_inc_ref(v_cmp_2820_);
    v___x_2824_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2820_, v_t_2821_, v_a_2822_);
    if crate::leanh::lean_obj_tag(v___x_2824_) == 0 {
        let mut v___x_2825_: u8 = 0;
        crate::leanh::lean_inc(v_t_2821_);
        crate::leanh::lean_inc(v_a_2822_);
        crate::leanh::lean_inc_ref(v_cmp_2820_);
        v___x_2825_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2820_, v_a_2822_, v_t_2821_);
        if v___x_2825_ == 0 {
            let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2826_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                v_cmp_2820_,
                v_a_2822_,
                v_b_2823_,
                v_t_2821_,
            );
            v___x_2827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2827_, 0, v___x_2824_);
            crate::leanh::lean_ctor_set(v___x_2827_, 1, v___x_2826_);
            return v___x_2827_;
        } else {
            let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_2823_);
            crate::leanh::lean_dec(v_a_2822_);
            crate::leanh::lean_dec_ref(v_cmp_2820_);
            v___x_2828_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2828_, 0, v___x_2824_);
            crate::leanh::lean_ctor_set(v___x_2828_, 1, v_t_2821_);
            return v___x_2828_;
        }
    } else {
        let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_2823_);
        crate::leanh::lean_dec(v_a_2822_);
        crate::leanh::lean_dec_ref(v_cmp_2820_);
        v___x_2829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2829_, 0, v___x_2824_);
        crate::leanh::lean_ctor_set(v___x_2829_, 1, v_t_2821_);
        return v___x_2829_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2830_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2831_: *mut crate::leanh::LeanObject,
    mut v_cmp_2832_: *mut crate::leanh::LeanObject,
    mut v_t_2833_: *mut crate::leanh::LeanObject,
    mut v_a_2834_: *mut crate::leanh::LeanObject,
    mut v_b_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2834_);
    crate::leanh::lean_inc(v_t_2833_);
    crate::leanh::lean_inc_ref(v_cmp_2832_);
    v___x_2836_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2832_, v_t_2833_, v_a_2834_);
    if crate::leanh::lean_obj_tag(v___x_2836_) == 0 {
        let mut v___x_2837_: u8 = 0;
        crate::leanh::lean_inc(v_t_2833_);
        crate::leanh::lean_inc(v_a_2834_);
        crate::leanh::lean_inc_ref(v_cmp_2832_);
        v___x_2837_ =
            l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2832_, v_a_2834_, v_t_2833_);
        if v___x_2837_ == 0 {
            let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2838_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                v_cmp_2832_,
                v_a_2834_,
                v_b_2835_,
                v_t_2833_,
            );
            v___x_2839_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2839_, 0, v___x_2836_);
            crate::leanh::lean_ctor_set(v___x_2839_, 1, v___x_2838_);
            return v___x_2839_;
        } else {
            let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_2835_);
            crate::leanh::lean_dec(v_a_2834_);
            crate::leanh::lean_dec_ref(v_cmp_2832_);
            v___x_2840_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2840_, 0, v___x_2836_);
            crate::leanh::lean_ctor_set(v___x_2840_, 1, v_t_2833_);
            return v___x_2840_;
        }
    } else {
        let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_2835_);
        crate::leanh::lean_dec(v_a_2834_);
        crate::leanh::lean_dec_ref(v_cmp_2832_);
        v___x_2841_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2841_, 0, v___x_2836_);
        crate::leanh::lean_ctor_set(v___x_2841_, 1, v_t_2833_);
        return v___x_2841_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_contains___redArg(
    mut v_cmp_2842_: *mut crate::leanh::LeanObject,
    mut v_l_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2845_: u8 = 0;
    v___x_2845_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2842_, v_a_2844_, v_l_2843_);
    return v___x_2845_;
}
pub unsafe fn l_Std_TreeMap_Raw_contains___redArg___boxed(
    mut v_cmp_2846_: *mut crate::leanh::LeanObject,
    mut v_l_2847_: *mut crate::leanh::LeanObject,
    mut v_a_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2849_: u8 = 0;
    let mut v_r_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Std_TreeMap_Raw_contains___redArg(v_cmp_2846_, v_l_2847_, v_a_2848_);
    v_r_2850_ = crate::leanh::lean_box((v_res_2849_) as usize);
    return v_r_2850_;
}
pub unsafe fn l_Std_TreeMap_Raw_contains(
    mut v_00_u03b1_2851_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2852_: *mut crate::leanh::LeanObject,
    mut v_cmp_2853_: *mut crate::leanh::LeanObject,
    mut v_l_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2856_: u8 = 0;
    v___x_2856_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2853_, v_a_2855_, v_l_2854_);
    return v___x_2856_;
}
pub unsafe fn l_Std_TreeMap_Raw_contains___boxed(
    mut v_00_u03b1_2857_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2858_: *mut crate::leanh::LeanObject,
    mut v_cmp_2859_: *mut crate::leanh::LeanObject,
    mut v_l_2860_: *mut crate::leanh::LeanObject,
    mut v_a_2861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2862_: u8 = 0;
    let mut v_r_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_Std_TreeMap_Raw_contains(
        v_00_u03b1_2857_,
        v_00_u03b2_2858_,
        v_cmp_2859_,
        v_l_2860_,
        v_a_2861_,
    );
    v_r_2863_ = crate::leanh::lean_box((v_res_2862_) as usize);
    return v_r_2863_;
}
pub unsafe fn l_Std_TreeMap_Raw_instMembership(
    mut v_00_u03b1_2864_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2865_: *mut crate::leanh::LeanObject,
    mut v_cmp_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = crate::leanh::lean_box(0);
    return v___x_2867_;
}
pub unsafe fn l_Std_TreeMap_Raw_instMembership___boxed(
    mut v_00_u03b1_2868_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2869_: *mut crate::leanh::LeanObject,
    mut v_cmp_2870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2871_ = l_Std_TreeMap_Raw_instMembership(v_00_u03b1_2868_, v_00_u03b2_2869_, v_cmp_2870_);
    crate::leanh::lean_dec_ref(v_cmp_2870_);
    return v_res_2871_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableMem___redArg(
    mut v_cmp_2872_: *mut crate::leanh::LeanObject,
    mut v_t_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2875_: u8 = 0;
    v___x_2875_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2872_, v_a_2874_, v_t_2873_);
    return v___x_2875_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableMem___redArg___boxed(
    mut v_cmp_2876_: *mut crate::leanh::LeanObject,
    mut v_t_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2879_: u8 = 0;
    let mut v_r_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2879_ = l_Std_TreeMap_Raw_instDecidableMem___redArg(v_cmp_2876_, v_t_2877_, v_a_2878_);
    v_r_2880_ = crate::leanh::lean_box((v_res_2879_) as usize);
    return v_r_2880_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableMem(
    mut v_00_u03b1_2881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2882_: *mut crate::leanh::LeanObject,
    mut v_cmp_2883_: *mut crate::leanh::LeanObject,
    mut v_t_2884_: *mut crate::leanh::LeanObject,
    mut v_a_2885_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2886_: u8 = 0;
    v___x_2886_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2883_, v_a_2885_, v_t_2884_);
    return v___x_2886_;
}
pub unsafe fn l_Std_TreeMap_Raw_instDecidableMem___boxed(
    mut v_00_u03b1_2887_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2888_: *mut crate::leanh::LeanObject,
    mut v_cmp_2889_: *mut crate::leanh::LeanObject,
    mut v_t_2890_: *mut crate::leanh::LeanObject,
    mut v_a_2891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2892_: u8 = 0;
    let mut v_r_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2892_ = l_Std_TreeMap_Raw_instDecidableMem(
        v_00_u03b1_2887_,
        v_00_u03b2_2888_,
        v_cmp_2889_,
        v_t_2890_,
        v_a_2891_,
    );
    v_r_2893_ = crate::leanh::lean_box((v_res_2892_) as usize);
    return v_r_2893_;
}
pub unsafe fn l_Std_TreeMap_Raw_size___redArg(
    mut v_t_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2894_) == 0 {
        let mut v_size_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_2895_ = crate::leanh::lean_ctor_get(v_t_2894_, 0);
        crate::leanh::lean_inc(v_size_2895_);
        return v_size_2895_;
    } else {
        let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2896_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2896_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_size___redArg___boxed(
    mut v_t_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2898_ = l_Std_TreeMap_Raw_size___redArg(v_t_2897_);
    crate::leanh::lean_dec(v_t_2897_);
    return v_res_2898_;
}
pub unsafe fn l_Std_TreeMap_Raw_size(
    mut v_00_u03b1_2899_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2900_: *mut crate::leanh::LeanObject,
    mut v_cmp_2901_: *mut crate::leanh::LeanObject,
    mut v_t_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2902_) == 0 {
        let mut v_size_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_2903_ = crate::leanh::lean_ctor_get(v_t_2902_, 0);
        crate::leanh::lean_inc(v_size_2903_);
        return v_size_2903_;
    } else {
        let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2904_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2904_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_size___boxed(
    mut v_00_u03b1_2905_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2906_: *mut crate::leanh::LeanObject,
    mut v_cmp_2907_: *mut crate::leanh::LeanObject,
    mut v_t_2908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2909_ =
        l_Std_TreeMap_Raw_size(v_00_u03b1_2905_, v_00_u03b2_2906_, v_cmp_2907_, v_t_2908_);
    crate::leanh::lean_dec(v_t_2908_);
    crate::leanh::lean_dec_ref(v_cmp_2907_);
    return v_res_2909_;
}
pub unsafe fn l_Std_TreeMap_Raw_isEmpty___redArg(
    mut v_t_2910_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_2910_) == 0 {
        let mut v___x_2911_: u8 = 0;
        v___x_2911_ = 0;
        return v___x_2911_;
    } else {
        let mut v___x_2912_: u8 = 0;
        v___x_2912_ = 1;
        return v___x_2912_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_isEmpty___redArg___boxed(
    mut v_t_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2914_: u8 = 0;
    let mut v_r_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2914_ = l_Std_TreeMap_Raw_isEmpty___redArg(v_t_2913_);
    crate::leanh::lean_dec(v_t_2913_);
    v_r_2915_ = crate::leanh::lean_box((v_res_2914_) as usize);
    return v_r_2915_;
}
pub unsafe fn l_Std_TreeMap_Raw_isEmpty(
    mut v_00_u03b1_2916_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2917_: *mut crate::leanh::LeanObject,
    mut v_cmp_2918_: *mut crate::leanh::LeanObject,
    mut v_t_2919_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_2919_) == 0 {
        let mut v___x_2920_: u8 = 0;
        v___x_2920_ = 0;
        return v___x_2920_;
    } else {
        let mut v___x_2921_: u8 = 0;
        v___x_2921_ = 1;
        return v___x_2921_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_isEmpty___boxed(
    mut v_00_u03b1_2922_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2923_: *mut crate::leanh::LeanObject,
    mut v_cmp_2924_: *mut crate::leanh::LeanObject,
    mut v_t_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2926_: u8 = 0;
    let mut v_r_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ =
        l_Std_TreeMap_Raw_isEmpty(v_00_u03b1_2922_, v_00_u03b2_2923_, v_cmp_2924_, v_t_2925_);
    crate::leanh::lean_dec(v_t_2925_);
    crate::leanh::lean_dec_ref(v_cmp_2924_);
    v_r_2927_ = crate::leanh::lean_box((v_res_2926_) as usize);
    return v_r_2927_;
}
pub unsafe fn l_Std_TreeMap_Raw_erase___redArg(
    mut v_cmp_2928_: *mut crate::leanh::LeanObject,
    mut v_t_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2931_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2928_, v_a_2930_, v_t_2929_);
    return v___x_2931_;
}
pub unsafe fn l_Std_TreeMap_Raw_erase(
    mut v_00_u03b1_2932_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2933_: *mut crate::leanh::LeanObject,
    mut v_cmp_2934_: *mut crate::leanh::LeanObject,
    mut v_t_2935_: *mut crate::leanh::LeanObject,
    mut v_a_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2937_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2934_, v_a_2936_, v_t_2935_);
    return v___x_2937_;
}
pub unsafe fn l_Std_TreeMap_Raw_get_x3f___redArg(
    mut v_cmp_2938_: *mut crate::leanh::LeanObject,
    mut v_t_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2938_, v_t_2939_, v_a_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Std_TreeMap_Raw_get_x3f(
    mut v_00_u03b1_2942_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2943_: *mut crate::leanh::LeanObject,
    mut v_cmp_2944_: *mut crate::leanh::LeanObject,
    mut v_t_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_2944_, v_t_2945_, v_a_2946_);
    return v___x_2947_;
}
pub unsafe fn l_Std_TreeMap_Raw_get___redArg(
    mut v_cmp_2948_: *mut crate::leanh::LeanObject,
    mut v_t_2949_: *mut crate::leanh::LeanObject,
    mut v_a_2950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_2948_, v_t_2949_, v_a_2950_);
    return v___x_2951_;
}
pub unsafe fn l_Std_TreeMap_Raw_get(
    mut v_00_u03b1_2952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2953_: *mut crate::leanh::LeanObject,
    mut v_cmp_2954_: *mut crate::leanh::LeanObject,
    mut v_t_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_h_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_2954_, v_t_2955_, v_a_2956_);
    return v___x_2958_;
}
pub unsafe fn l_Std_TreeMap_Raw_get_x21___redArg(
    mut v_cmp_2959_: *mut crate::leanh::LeanObject,
    mut v_inst_2960_: *mut crate::leanh::LeanObject,
    mut v_t_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2963_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_2959_,
        v_inst_2960_,
        v_t_2961_,
        v_a_2962_,
    );
    return v___x_2963_;
}
pub unsafe fn l_Std_TreeMap_Raw_get_x21___redArg___boxed(
    mut v_cmp_2964_: *mut crate::leanh::LeanObject,
    mut v_inst_2965_: *mut crate::leanh::LeanObject,
    mut v_t_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ =
        l_Std_TreeMap_Raw_get_x21___redArg(v_cmp_2964_, v_inst_2965_, v_t_2966_, v_a_2967_);
    crate::leanh::lean_dec(v_inst_2965_);
    return v_res_2968_;
}
pub unsafe fn l_Std_TreeMap_Raw_get_x21(
    mut v_00_u03b1_2969_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2970_: *mut crate::leanh::LeanObject,
    mut v_cmp_2971_: *mut crate::leanh::LeanObject,
    mut v_inst_2972_: *mut crate::leanh::LeanObject,
    mut v_t_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_2971_,
        v_inst_2972_,
        v_t_2973_,
        v_a_2974_,
    );
    return v___x_2975_;
}
pub unsafe fn l_Std_TreeMap_Raw_get_x21___boxed(
    mut v_00_u03b1_2976_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2977_: *mut crate::leanh::LeanObject,
    mut v_cmp_2978_: *mut crate::leanh::LeanObject,
    mut v_inst_2979_: *mut crate::leanh::LeanObject,
    mut v_t_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Std_TreeMap_Raw_get_x21(
        v_00_u03b1_2976_,
        v_00_u03b2_2977_,
        v_cmp_2978_,
        v_inst_2979_,
        v_t_2980_,
        v_a_2981_,
    );
    crate::leanh::lean_dec(v_inst_2979_);
    return v_res_2982_;
}
pub unsafe fn l_Std_TreeMap_Raw_getD___redArg(
    mut v_cmp_2983_: *mut crate::leanh::LeanObject,
    mut v_t_2984_: *mut crate::leanh::LeanObject,
    mut v_a_2985_: *mut crate::leanh::LeanObject,
    mut v_fallback_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_2983_,
        v_t_2984_,
        v_a_2985_,
        v_fallback_2986_,
    );
    return v___x_2987_;
}
pub unsafe fn l_Std_TreeMap_Raw_getD___redArg___boxed(
    mut v_cmp_2988_: *mut crate::leanh::LeanObject,
    mut v_t_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
    mut v_fallback_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2992_ =
        l_Std_TreeMap_Raw_getD___redArg(v_cmp_2988_, v_t_2989_, v_a_2990_, v_fallback_2991_);
    crate::leanh::lean_dec(v_fallback_2991_);
    return v_res_2992_;
}
pub unsafe fn l_Std_TreeMap_Raw_getD(
    mut v_00_u03b1_2993_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2994_: *mut crate::leanh::LeanObject,
    mut v_cmp_2995_: *mut crate::leanh::LeanObject,
    mut v_t_2996_: *mut crate::leanh::LeanObject,
    mut v_a_2997_: *mut crate::leanh::LeanObject,
    mut v_fallback_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2999_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_cmp_2995_,
        v_t_2996_,
        v_a_2997_,
        v_fallback_2998_,
    );
    return v___x_2999_;
}
pub unsafe fn l_Std_TreeMap_Raw_getD___boxed(
    mut v_00_u03b1_3000_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3001_: *mut crate::leanh::LeanObject,
    mut v_cmp_3002_: *mut crate::leanh::LeanObject,
    mut v_t_3003_: *mut crate::leanh::LeanObject,
    mut v_a_3004_: *mut crate::leanh::LeanObject,
    mut v_fallback_3005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_Std_TreeMap_Raw_getD(
        v_00_u03b1_3000_,
        v_00_u03b2_3001_,
        v_cmp_3002_,
        v_t_3003_,
        v_a_3004_,
        v_fallback_3005_,
    );
    crate::leanh::lean_dec(v_fallback_3005_);
    return v_res_3006_;
}
pub unsafe fn l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0(
    mut v_cmp_3007_: *mut crate::leanh::LeanObject,
    mut v_m_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
    mut v_h_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3011_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_3007_, v_m_3008_, v_a_3009_);
    return v___x_3011_;
}
pub unsafe fn l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1(
    mut v_cmp_3012_: *mut crate::leanh::LeanObject,
    mut v_m_3013_: *mut crate::leanh::LeanObject,
    mut v_a_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3015_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_3012_, v_m_3013_, v_a_3014_);
    return v___x_3015_;
}
pub unsafe fn l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(
    mut v_cmp_3016_: *mut crate::leanh::LeanObject,
    mut v_inst_3017_: *mut crate::leanh::LeanObject,
    mut v_m_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3020_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_cmp_3016_,
        v_inst_3017_,
        v_m_3018_,
        v_a_3019_,
    );
    return v___x_3020_;
}
pub unsafe fn l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(
    mut v_cmp_3021_: *mut crate::leanh::LeanObject,
    mut v_inst_3022_: *mut crate::leanh::LeanObject,
    mut v_m_3023_: *mut crate::leanh::LeanObject,
    mut v_a_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3025_ = l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2(
        v_cmp_3021_,
        v_inst_3022_,
        v_m_3023_,
        v_a_3024_,
    );
    crate::leanh::lean_dec(v_inst_3022_);
    return v_res_3025_;
}
pub unsafe fn l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(
    mut v_cmp_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_cmp_3026_, 2);
    v___f_3027_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3027_, 0, v_cmp_3026_);
    v___f_3028_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3028_, 0, v_cmp_3026_);
    v___f_3029_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3029_, 0, v_cmp_3026_);
    v___x_3030_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3030_, 0, v___f_3027_);
    crate::leanh::lean_ctor_set(v___x_3030_, 1, v___f_3028_);
    crate::leanh::lean_ctor_set(v___x_3030_, 2, v___f_3029_);
    return v___x_3030_;
}
pub unsafe fn l_Std_TreeMap_Raw_instGetElem_x3fMem(
    mut v_00_u03b1_3031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3032_: *mut crate::leanh::LeanObject,
    mut v_cmp_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3034_ = l_Std_TreeMap_Raw_instGetElem_x3fMem___redArg(v_cmp_3033_);
    return v___x_3034_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey_x3f___redArg(
    mut v_cmp_3035_: *mut crate::leanh::LeanObject,
    mut v_t_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_3035_, v_t_3036_, v_a_3037_);
    return v___x_3038_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey_x3f(
    mut v_00_u03b1_3039_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3040_: *mut crate::leanh::LeanObject,
    mut v_cmp_3041_: *mut crate::leanh::LeanObject,
    mut v_t_3042_: *mut crate::leanh::LeanObject,
    mut v_a_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3044_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_3041_, v_t_3042_, v_a_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey___redArg(
    mut v_cmp_3045_: *mut crate::leanh::LeanObject,
    mut v_t_3046_: *mut crate::leanh::LeanObject,
    mut v_a_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_3045_, v_t_3046_, v_a_3047_);
    return v___x_3048_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey(
    mut v_00_u03b1_3049_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3050_: *mut crate::leanh::LeanObject,
    mut v_cmp_3051_: *mut crate::leanh::LeanObject,
    mut v_t_3052_: *mut crate::leanh::LeanObject,
    mut v_a_3053_: *mut crate::leanh::LeanObject,
    mut v_h_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3055_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_3051_, v_t_3052_, v_a_3053_);
    return v___x_3055_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey_x21___redArg(
    mut v_cmp_3056_: *mut crate::leanh::LeanObject,
    mut v_inst_3057_: *mut crate::leanh::LeanObject,
    mut v_t_3058_: *mut crate::leanh::LeanObject,
    mut v_a_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_3056_,
        v_t_3058_,
        v_a_3059_,
        v_inst_3057_,
    );
    return v___x_3060_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey_x21___redArg___boxed(
    mut v_cmp_3061_: *mut crate::leanh::LeanObject,
    mut v_inst_3062_: *mut crate::leanh::LeanObject,
    mut v_t_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3065_ =
        l_Std_TreeMap_Raw_getKey_x21___redArg(v_cmp_3061_, v_inst_3062_, v_t_3063_, v_a_3064_);
    crate::leanh::lean_dec(v_inst_3062_);
    return v_res_3065_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey_x21(
    mut v_00_u03b1_3066_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3067_: *mut crate::leanh::LeanObject,
    mut v_cmp_3068_: *mut crate::leanh::LeanObject,
    mut v_inst_3069_: *mut crate::leanh::LeanObject,
    mut v_t_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_3068_,
        v_t_3070_,
        v_a_3071_,
        v_inst_3069_,
    );
    return v___x_3072_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKey_x21___boxed(
    mut v_00_u03b1_3073_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3074_: *mut crate::leanh::LeanObject,
    mut v_cmp_3075_: *mut crate::leanh::LeanObject,
    mut v_inst_3076_: *mut crate::leanh::LeanObject,
    mut v_t_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3079_ = l_Std_TreeMap_Raw_getKey_x21(
        v_00_u03b1_3073_,
        v_00_u03b2_3074_,
        v_cmp_3075_,
        v_inst_3076_,
        v_t_3077_,
        v_a_3078_,
    );
    crate::leanh::lean_dec(v_inst_3076_);
    return v_res_3079_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyD___redArg(
    mut v_cmp_3080_: *mut crate::leanh::LeanObject,
    mut v_t_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_fallback_3083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3084_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_3080_,
        v_t_3081_,
        v_a_3082_,
        v_fallback_3083_,
    );
    return v___x_3084_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyD___redArg___boxed(
    mut v_cmp_3085_: *mut crate::leanh::LeanObject,
    mut v_t_3086_: *mut crate::leanh::LeanObject,
    mut v_a_3087_: *mut crate::leanh::LeanObject,
    mut v_fallback_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3089_ =
        l_Std_TreeMap_Raw_getKeyD___redArg(v_cmp_3085_, v_t_3086_, v_a_3087_, v_fallback_3088_);
    crate::leanh::lean_dec(v_fallback_3088_);
    return v_res_3089_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyD(
    mut v_00_u03b1_3090_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3091_: *mut crate::leanh::LeanObject,
    mut v_cmp_3092_: *mut crate::leanh::LeanObject,
    mut v_t_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
    mut v_fallback_3095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3096_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_3092_,
        v_t_3093_,
        v_a_3094_,
        v_fallback_3095_,
    );
    return v___x_3096_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyD___boxed(
    mut v_00_u03b1_3097_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3098_: *mut crate::leanh::LeanObject,
    mut v_cmp_3099_: *mut crate::leanh::LeanObject,
    mut v_t_3100_: *mut crate::leanh::LeanObject,
    mut v_a_3101_: *mut crate::leanh::LeanObject,
    mut v_fallback_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3103_ = l_Std_TreeMap_Raw_getKeyD(
        v_00_u03b1_3097_,
        v_00_u03b2_3098_,
        v_cmp_3099_,
        v_t_3100_,
        v_a_3101_,
        v_fallback_3102_,
    );
    crate::leanh::lean_dec(v_fallback_3102_);
    return v_res_3103_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x3f___redArg(
    mut v_t_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_3104_);
    return v___x_3105_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x3f___redArg___boxed(
    mut v_t_3106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3107_ = l_Std_TreeMap_Raw_minEntry_x3f___redArg(v_t_3106_);
    crate::leanh::lean_dec(v_t_3106_);
    return v_res_3107_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x3f(
    mut v_00_u03b1_3108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3109_: *mut crate::leanh::LeanObject,
    mut v_cmp_3110_: *mut crate::leanh::LeanObject,
    mut v_t_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3112_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_3111_);
    return v___x_3112_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x3f___boxed(
    mut v_00_u03b1_3113_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3114_: *mut crate::leanh::LeanObject,
    mut v_cmp_3115_: *mut crate::leanh::LeanObject,
    mut v_t_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3117_ =
        l_Std_TreeMap_Raw_minEntry_x3f(v_00_u03b1_3113_, v_00_u03b2_3114_, v_cmp_3115_, v_t_3116_);
    crate::leanh::lean_dec(v_t_3116_);
    crate::leanh::lean_dec_ref(v_cmp_3115_);
    return v_res_3117_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x21___redArg(
    mut v_inst_3118_: *mut crate::leanh::LeanObject,
    mut v_t_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3120_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3118_, v_t_3119_);
    return v___x_3120_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x21___redArg___boxed(
    mut v_inst_3121_: *mut crate::leanh::LeanObject,
    mut v_t_3122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3123_ = l_Std_TreeMap_Raw_minEntry_x21___redArg(v_inst_3121_, v_t_3122_);
    crate::leanh::lean_dec(v_t_3122_);
    crate::leanh::lean_dec_ref(v_inst_3121_);
    return v_res_3123_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x21(
    mut v_00_u03b1_3124_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3125_: *mut crate::leanh::LeanObject,
    mut v_cmp_3126_: *mut crate::leanh::LeanObject,
    mut v_inst_3127_: *mut crate::leanh::LeanObject,
    mut v_t_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3127_, v_t_3128_);
    return v___x_3129_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntry_x21___boxed(
    mut v_00_u03b1_3130_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3131_: *mut crate::leanh::LeanObject,
    mut v_cmp_3132_: *mut crate::leanh::LeanObject,
    mut v_inst_3133_: *mut crate::leanh::LeanObject,
    mut v_t_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l_Std_TreeMap_Raw_minEntry_x21(
        v_00_u03b1_3130_,
        v_00_u03b2_3131_,
        v_cmp_3132_,
        v_inst_3133_,
        v_t_3134_,
    );
    crate::leanh::lean_dec(v_t_3134_);
    crate::leanh::lean_dec_ref(v_inst_3133_);
    crate::leanh::lean_dec_ref(v_cmp_3132_);
    return v_res_3135_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntryD___redArg(
    mut v_t_3136_: *mut crate::leanh::LeanObject,
    mut v_fallback_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_3136_, v_fallback_3137_);
    return v___x_3138_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntryD___redArg___boxed(
    mut v_t_3139_: *mut crate::leanh::LeanObject,
    mut v_fallback_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Std_TreeMap_Raw_minEntryD___redArg(v_t_3139_, v_fallback_3140_);
    crate::leanh::lean_dec_ref(v_fallback_3140_);
    crate::leanh::lean_dec(v_t_3139_);
    return v_res_3141_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntryD(
    mut v_00_u03b1_3142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3143_: *mut crate::leanh::LeanObject,
    mut v_cmp_3144_: *mut crate::leanh::LeanObject,
    mut v_t_3145_: *mut crate::leanh::LeanObject,
    mut v_fallback_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ =
        l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_3145_, v_fallback_3146_);
    return v___x_3147_;
}
pub unsafe fn l_Std_TreeMap_Raw_minEntryD___boxed(
    mut v_00_u03b1_3148_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3149_: *mut crate::leanh::LeanObject,
    mut v_cmp_3150_: *mut crate::leanh::LeanObject,
    mut v_t_3151_: *mut crate::leanh::LeanObject,
    mut v_fallback_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3153_ = l_Std_TreeMap_Raw_minEntryD(
        v_00_u03b1_3148_,
        v_00_u03b2_3149_,
        v_cmp_3150_,
        v_t_3151_,
        v_fallback_3152_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3152_);
    crate::leanh::lean_dec(v_t_3151_);
    crate::leanh::lean_dec_ref(v_cmp_3150_);
    return v_res_3153_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x3f___redArg(
    mut v_t_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_3154_);
    return v___x_3155_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x3f___redArg___boxed(
    mut v_t_3156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_Std_TreeMap_Raw_maxEntry_x3f___redArg(v_t_3156_);
    crate::leanh::lean_dec(v_t_3156_);
    return v_res_3157_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x3f(
    mut v_00_u03b1_3158_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3159_: *mut crate::leanh::LeanObject,
    mut v_cmp_3160_: *mut crate::leanh::LeanObject,
    mut v_t_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3162_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_3161_);
    return v___x_3162_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x3f___boxed(
    mut v_00_u03b1_3163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3164_: *mut crate::leanh::LeanObject,
    mut v_cmp_3165_: *mut crate::leanh::LeanObject,
    mut v_t_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3167_ =
        l_Std_TreeMap_Raw_maxEntry_x3f(v_00_u03b1_3163_, v_00_u03b2_3164_, v_cmp_3165_, v_t_3166_);
    crate::leanh::lean_dec(v_t_3166_);
    crate::leanh::lean_dec_ref(v_cmp_3165_);
    return v_res_3167_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x21___redArg(
    mut v_inst_3168_: *mut crate::leanh::LeanObject,
    mut v_t_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3170_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3168_, v_t_3169_);
    return v___x_3170_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x21___redArg___boxed(
    mut v_inst_3171_: *mut crate::leanh::LeanObject,
    mut v_t_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3173_ = l_Std_TreeMap_Raw_maxEntry_x21___redArg(v_inst_3171_, v_t_3172_);
    crate::leanh::lean_dec(v_t_3172_);
    crate::leanh::lean_dec_ref(v_inst_3171_);
    return v_res_3173_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x21(
    mut v_00_u03b1_3174_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3175_: *mut crate::leanh::LeanObject,
    mut v_cmp_3176_: *mut crate::leanh::LeanObject,
    mut v_inst_3177_: *mut crate::leanh::LeanObject,
    mut v_t_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3177_, v_t_3178_);
    return v___x_3179_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntry_x21___boxed(
    mut v_00_u03b1_3180_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3181_: *mut crate::leanh::LeanObject,
    mut v_cmp_3182_: *mut crate::leanh::LeanObject,
    mut v_inst_3183_: *mut crate::leanh::LeanObject,
    mut v_t_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3185_ = l_Std_TreeMap_Raw_maxEntry_x21(
        v_00_u03b1_3180_,
        v_00_u03b2_3181_,
        v_cmp_3182_,
        v_inst_3183_,
        v_t_3184_,
    );
    crate::leanh::lean_dec(v_t_3184_);
    crate::leanh::lean_dec_ref(v_inst_3183_);
    crate::leanh::lean_dec_ref(v_cmp_3182_);
    return v_res_3185_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntryD___redArg(
    mut v_t_3186_: *mut crate::leanh::LeanObject,
    mut v_fallback_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3188_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_3186_, v_fallback_3187_);
    return v___x_3188_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntryD___redArg___boxed(
    mut v_t_3189_: *mut crate::leanh::LeanObject,
    mut v_fallback_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3191_ = l_Std_TreeMap_Raw_maxEntryD___redArg(v_t_3189_, v_fallback_3190_);
    crate::leanh::lean_dec_ref(v_fallback_3190_);
    crate::leanh::lean_dec(v_t_3189_);
    return v_res_3191_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntryD(
    mut v_00_u03b1_3192_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3193_: *mut crate::leanh::LeanObject,
    mut v_cmp_3194_: *mut crate::leanh::LeanObject,
    mut v_t_3195_: *mut crate::leanh::LeanObject,
    mut v_fallback_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3197_ =
        l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_3195_, v_fallback_3196_);
    return v___x_3197_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxEntryD___boxed(
    mut v_00_u03b1_3198_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3199_: *mut crate::leanh::LeanObject,
    mut v_cmp_3200_: *mut crate::leanh::LeanObject,
    mut v_t_3201_: *mut crate::leanh::LeanObject,
    mut v_fallback_3202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3203_ = l_Std_TreeMap_Raw_maxEntryD(
        v_00_u03b1_3198_,
        v_00_u03b2_3199_,
        v_cmp_3200_,
        v_t_3201_,
        v_fallback_3202_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3202_);
    crate::leanh::lean_dec(v_t_3201_);
    crate::leanh::lean_dec_ref(v_cmp_3200_);
    return v_res_3203_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x3f___redArg(
    mut v_t_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_3204_);
    return v___x_3205_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x3f___redArg___boxed(
    mut v_t_3206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3207_ = l_Std_TreeMap_Raw_minKey_x3f___redArg(v_t_3206_);
    crate::leanh::lean_dec(v_t_3206_);
    return v_res_3207_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x3f(
    mut v_00_u03b1_3208_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3209_: *mut crate::leanh::LeanObject,
    mut v_cmp_3210_: *mut crate::leanh::LeanObject,
    mut v_t_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3212_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_3211_);
    return v___x_3212_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x3f___boxed(
    mut v_00_u03b1_3213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3214_: *mut crate::leanh::LeanObject,
    mut v_cmp_3215_: *mut crate::leanh::LeanObject,
    mut v_t_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ =
        l_Std_TreeMap_Raw_minKey_x3f(v_00_u03b1_3213_, v_00_u03b2_3214_, v_cmp_3215_, v_t_3216_);
    crate::leanh::lean_dec(v_t_3216_);
    crate::leanh::lean_dec_ref(v_cmp_3215_);
    return v_res_3217_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x21___redArg(
    mut v_inst_3218_: *mut crate::leanh::LeanObject,
    mut v_t_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_3218_, v_t_3219_);
    return v___x_3220_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x21___redArg___boxed(
    mut v_inst_3221_: *mut crate::leanh::LeanObject,
    mut v_t_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Std_TreeMap_Raw_minKey_x21___redArg(v_inst_3221_, v_t_3222_);
    crate::leanh::lean_dec(v_t_3222_);
    crate::leanh::lean_dec(v_inst_3221_);
    return v_res_3223_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x21(
    mut v_00_u03b1_3224_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3225_: *mut crate::leanh::LeanObject,
    mut v_cmp_3226_: *mut crate::leanh::LeanObject,
    mut v_inst_3227_: *mut crate::leanh::LeanObject,
    mut v_t_3228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3229_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_3227_, v_t_3228_);
    return v___x_3229_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKey_x21___boxed(
    mut v_00_u03b1_3230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3231_: *mut crate::leanh::LeanObject,
    mut v_cmp_3232_: *mut crate::leanh::LeanObject,
    mut v_inst_3233_: *mut crate::leanh::LeanObject,
    mut v_t_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3235_ = l_Std_TreeMap_Raw_minKey_x21(
        v_00_u03b1_3230_,
        v_00_u03b2_3231_,
        v_cmp_3232_,
        v_inst_3233_,
        v_t_3234_,
    );
    crate::leanh::lean_dec(v_t_3234_);
    crate::leanh::lean_dec(v_inst_3233_);
    crate::leanh::lean_dec_ref(v_cmp_3232_);
    return v_res_3235_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKeyD___redArg(
    mut v_t_3236_: *mut crate::leanh::LeanObject,
    mut v_fallback_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3238_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_3236_, v_fallback_3237_);
    return v___x_3238_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKeyD___redArg___boxed(
    mut v_t_3239_: *mut crate::leanh::LeanObject,
    mut v_fallback_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Std_TreeMap_Raw_minKeyD___redArg(v_t_3239_, v_fallback_3240_);
    crate::leanh::lean_dec(v_fallback_3240_);
    crate::leanh::lean_dec(v_t_3239_);
    return v_res_3241_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKeyD(
    mut v_00_u03b1_3242_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3243_: *mut crate::leanh::LeanObject,
    mut v_cmp_3244_: *mut crate::leanh::LeanObject,
    mut v_t_3245_: *mut crate::leanh::LeanObject,
    mut v_fallback_3246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3247_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_3245_, v_fallback_3246_);
    return v___x_3247_;
}
pub unsafe fn l_Std_TreeMap_Raw_minKeyD___boxed(
    mut v_00_u03b1_3248_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3249_: *mut crate::leanh::LeanObject,
    mut v_cmp_3250_: *mut crate::leanh::LeanObject,
    mut v_t_3251_: *mut crate::leanh::LeanObject,
    mut v_fallback_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3253_ = l_Std_TreeMap_Raw_minKeyD(
        v_00_u03b1_3248_,
        v_00_u03b2_3249_,
        v_cmp_3250_,
        v_t_3251_,
        v_fallback_3252_,
    );
    crate::leanh::lean_dec(v_fallback_3252_);
    crate::leanh::lean_dec(v_t_3251_);
    crate::leanh::lean_dec_ref(v_cmp_3250_);
    return v_res_3253_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x3f___redArg(
    mut v_t_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3255_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_3254_);
    return v___x_3255_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x3f___redArg___boxed(
    mut v_t_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3257_ = l_Std_TreeMap_Raw_maxKey_x3f___redArg(v_t_3256_);
    crate::leanh::lean_dec(v_t_3256_);
    return v_res_3257_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x3f(
    mut v_00_u03b1_3258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3259_: *mut crate::leanh::LeanObject,
    mut v_cmp_3260_: *mut crate::leanh::LeanObject,
    mut v_t_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3262_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_3261_);
    return v___x_3262_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x3f___boxed(
    mut v_00_u03b1_3263_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3264_: *mut crate::leanh::LeanObject,
    mut v_cmp_3265_: *mut crate::leanh::LeanObject,
    mut v_t_3266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3267_ =
        l_Std_TreeMap_Raw_maxKey_x3f(v_00_u03b1_3263_, v_00_u03b2_3264_, v_cmp_3265_, v_t_3266_);
    crate::leanh::lean_dec(v_t_3266_);
    crate::leanh::lean_dec_ref(v_cmp_3265_);
    return v_res_3267_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x21___redArg(
    mut v_inst_3268_: *mut crate::leanh::LeanObject,
    mut v_t_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3270_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_3268_, v_t_3269_);
    return v___x_3270_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x21___redArg___boxed(
    mut v_inst_3271_: *mut crate::leanh::LeanObject,
    mut v_t_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3273_ = l_Std_TreeMap_Raw_maxKey_x21___redArg(v_inst_3271_, v_t_3272_);
    crate::leanh::lean_dec(v_t_3272_);
    crate::leanh::lean_dec(v_inst_3271_);
    return v_res_3273_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x21(
    mut v_00_u03b1_3274_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3275_: *mut crate::leanh::LeanObject,
    mut v_cmp_3276_: *mut crate::leanh::LeanObject,
    mut v_inst_3277_: *mut crate::leanh::LeanObject,
    mut v_t_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3279_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_3277_, v_t_3278_);
    return v___x_3279_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKey_x21___boxed(
    mut v_00_u03b1_3280_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3281_: *mut crate::leanh::LeanObject,
    mut v_cmp_3282_: *mut crate::leanh::LeanObject,
    mut v_inst_3283_: *mut crate::leanh::LeanObject,
    mut v_t_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3285_ = l_Std_TreeMap_Raw_maxKey_x21(
        v_00_u03b1_3280_,
        v_00_u03b2_3281_,
        v_cmp_3282_,
        v_inst_3283_,
        v_t_3284_,
    );
    crate::leanh::lean_dec(v_t_3284_);
    crate::leanh::lean_dec(v_inst_3283_);
    crate::leanh::lean_dec_ref(v_cmp_3282_);
    return v_res_3285_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKeyD___redArg(
    mut v_t_3286_: *mut crate::leanh::LeanObject,
    mut v_fallback_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3288_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_3286_, v_fallback_3287_);
    return v___x_3288_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKeyD___redArg___boxed(
    mut v_t_3289_: *mut crate::leanh::LeanObject,
    mut v_fallback_3290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3291_ = l_Std_TreeMap_Raw_maxKeyD___redArg(v_t_3289_, v_fallback_3290_);
    crate::leanh::lean_dec(v_fallback_3290_);
    crate::leanh::lean_dec(v_t_3289_);
    return v_res_3291_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKeyD(
    mut v_00_u03b1_3292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3293_: *mut crate::leanh::LeanObject,
    mut v_cmp_3294_: *mut crate::leanh::LeanObject,
    mut v_t_3295_: *mut crate::leanh::LeanObject,
    mut v_fallback_3296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3297_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_3295_, v_fallback_3296_);
    return v___x_3297_;
}
pub unsafe fn l_Std_TreeMap_Raw_maxKeyD___boxed(
    mut v_00_u03b1_3298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3299_: *mut crate::leanh::LeanObject,
    mut v_cmp_3300_: *mut crate::leanh::LeanObject,
    mut v_t_3301_: *mut crate::leanh::LeanObject,
    mut v_fallback_3302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3303_ = l_Std_TreeMap_Raw_maxKeyD(
        v_00_u03b1_3298_,
        v_00_u03b2_3299_,
        v_cmp_3300_,
        v_t_3301_,
        v_fallback_3302_,
    );
    crate::leanh::lean_dec(v_fallback_3302_);
    crate::leanh::lean_dec(v_t_3301_);
    crate::leanh::lean_dec_ref(v_cmp_3300_);
    return v_res_3303_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(
    mut v_t_3304_: *mut crate::leanh::LeanObject,
    mut v_n_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3306_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_3304_, v_n_3305_);
    return v___x_3306_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg___boxed(
    mut v_t_3307_: *mut crate::leanh::LeanObject,
    mut v_n_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3309_ = l_Std_TreeMap_Raw_entryAtIdx_x3f___redArg(v_t_3307_, v_n_3308_);
    crate::leanh::lean_dec(v_t_3307_);
    return v_res_3309_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x3f(
    mut v_00_u03b1_3310_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3311_: *mut crate::leanh::LeanObject,
    mut v_cmp_3312_: *mut crate::leanh::LeanObject,
    mut v_t_3313_: *mut crate::leanh::LeanObject,
    mut v_n_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3315_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_3313_, v_n_3314_);
    return v___x_3315_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_3316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3317_: *mut crate::leanh::LeanObject,
    mut v_cmp_3318_: *mut crate::leanh::LeanObject,
    mut v_t_3319_: *mut crate::leanh::LeanObject,
    mut v_n_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l_Std_TreeMap_Raw_entryAtIdx_x3f(
        v_00_u03b1_3316_,
        v_00_u03b2_3317_,
        v_cmp_3318_,
        v_t_3319_,
        v_n_3320_,
    );
    crate::leanh::lean_dec(v_t_3319_);
    crate::leanh::lean_dec_ref(v_cmp_3318_);
    return v_res_3321_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(
    mut v_inst_3322_: *mut crate::leanh::LeanObject,
    mut v_t_3323_: *mut crate::leanh::LeanObject,
    mut v_n_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3325_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_3322_,
        v_t_3323_,
        v_n_3324_,
    );
    return v___x_3325_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x21___redArg___boxed(
    mut v_inst_3326_: *mut crate::leanh::LeanObject,
    mut v_t_3327_: *mut crate::leanh::LeanObject,
    mut v_n_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Std_TreeMap_Raw_entryAtIdx_x21___redArg(v_inst_3326_, v_t_3327_, v_n_3328_);
    crate::leanh::lean_dec(v_t_3327_);
    crate::leanh::lean_dec_ref(v_inst_3326_);
    return v_res_3329_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x21(
    mut v_00_u03b1_3330_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3331_: *mut crate::leanh::LeanObject,
    mut v_cmp_3332_: *mut crate::leanh::LeanObject,
    mut v_inst_3333_: *mut crate::leanh::LeanObject,
    mut v_t_3334_: *mut crate::leanh::LeanObject,
    mut v_n_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3336_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_3333_,
        v_t_3334_,
        v_n_3335_,
    );
    return v___x_3336_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdx_x21___boxed(
    mut v_00_u03b1_3337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3338_: *mut crate::leanh::LeanObject,
    mut v_cmp_3339_: *mut crate::leanh::LeanObject,
    mut v_inst_3340_: *mut crate::leanh::LeanObject,
    mut v_t_3341_: *mut crate::leanh::LeanObject,
    mut v_n_3342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3343_ = l_Std_TreeMap_Raw_entryAtIdx_x21(
        v_00_u03b1_3337_,
        v_00_u03b2_3338_,
        v_cmp_3339_,
        v_inst_3340_,
        v_t_3341_,
        v_n_3342_,
    );
    crate::leanh::lean_dec(v_t_3341_);
    crate::leanh::lean_dec_ref(v_inst_3340_);
    crate::leanh::lean_dec_ref(v_cmp_3339_);
    return v_res_3343_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdxD___redArg(
    mut v_t_3344_: *mut crate::leanh::LeanObject,
    mut v_n_3345_: *mut crate::leanh::LeanObject,
    mut v_fallback_3346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3347_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_3344_,
        v_n_3345_,
        v_fallback_3346_,
    );
    return v___x_3347_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdxD___redArg___boxed(
    mut v_t_3348_: *mut crate::leanh::LeanObject,
    mut v_n_3349_: *mut crate::leanh::LeanObject,
    mut v_fallback_3350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3351_ = l_Std_TreeMap_Raw_entryAtIdxD___redArg(v_t_3348_, v_n_3349_, v_fallback_3350_);
    crate::leanh::lean_dec_ref(v_fallback_3350_);
    crate::leanh::lean_dec(v_t_3348_);
    return v_res_3351_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdxD(
    mut v_00_u03b1_3352_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3353_: *mut crate::leanh::LeanObject,
    mut v_cmp_3354_: *mut crate::leanh::LeanObject,
    mut v_t_3355_: *mut crate::leanh::LeanObject,
    mut v_n_3356_: *mut crate::leanh::LeanObject,
    mut v_fallback_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
        v_t_3355_,
        v_n_3356_,
        v_fallback_3357_,
    );
    return v___x_3358_;
}
pub unsafe fn l_Std_TreeMap_Raw_entryAtIdxD___boxed(
    mut v_00_u03b1_3359_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3360_: *mut crate::leanh::LeanObject,
    mut v_cmp_3361_: *mut crate::leanh::LeanObject,
    mut v_t_3362_: *mut crate::leanh::LeanObject,
    mut v_n_3363_: *mut crate::leanh::LeanObject,
    mut v_fallback_3364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3365_ = l_Std_TreeMap_Raw_entryAtIdxD(
        v_00_u03b1_3359_,
        v_00_u03b2_3360_,
        v_cmp_3361_,
        v_t_3362_,
        v_n_3363_,
        v_fallback_3364_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3364_);
    crate::leanh::lean_dec(v_t_3362_);
    crate::leanh::lean_dec_ref(v_cmp_3361_);
    return v_res_3365_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(
    mut v_t_3366_: *mut crate::leanh::LeanObject,
    mut v_n_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3368_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_3366_, v_n_3367_);
    return v___x_3368_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg___boxed(
    mut v_t_3369_: *mut crate::leanh::LeanObject,
    mut v_n_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3371_ = l_Std_TreeMap_Raw_keyAtIdx_x3f___redArg(v_t_3369_, v_n_3370_);
    crate::leanh::lean_dec(v_t_3369_);
    return v_res_3371_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x3f(
    mut v_00_u03b1_3372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3373_: *mut crate::leanh::LeanObject,
    mut v_cmp_3374_: *mut crate::leanh::LeanObject,
    mut v_t_3375_: *mut crate::leanh::LeanObject,
    mut v_n_3376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3377_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_3375_, v_n_3376_);
    return v___x_3377_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x3f___boxed(
    mut v_00_u03b1_3378_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3379_: *mut crate::leanh::LeanObject,
    mut v_cmp_3380_: *mut crate::leanh::LeanObject,
    mut v_t_3381_: *mut crate::leanh::LeanObject,
    mut v_n_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3383_ = l_Std_TreeMap_Raw_keyAtIdx_x3f(
        v_00_u03b1_3378_,
        v_00_u03b2_3379_,
        v_cmp_3380_,
        v_t_3381_,
        v_n_3382_,
    );
    crate::leanh::lean_dec(v_t_3381_);
    crate::leanh::lean_dec_ref(v_cmp_3380_);
    return v_res_3383_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(
    mut v_inst_3384_: *mut crate::leanh::LeanObject,
    mut v_t_3385_: *mut crate::leanh::LeanObject,
    mut v_n_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3387_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_3384_, v_t_3385_, v_n_3386_);
    return v___x_3387_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x21___redArg___boxed(
    mut v_inst_3388_: *mut crate::leanh::LeanObject,
    mut v_t_3389_: *mut crate::leanh::LeanObject,
    mut v_n_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Std_TreeMap_Raw_keyAtIdx_x21___redArg(v_inst_3388_, v_t_3389_, v_n_3390_);
    crate::leanh::lean_dec(v_t_3389_);
    crate::leanh::lean_dec(v_inst_3388_);
    return v_res_3391_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x21(
    mut v_00_u03b1_3392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3393_: *mut crate::leanh::LeanObject,
    mut v_cmp_3394_: *mut crate::leanh::LeanObject,
    mut v_inst_3395_: *mut crate::leanh::LeanObject,
    mut v_t_3396_: *mut crate::leanh::LeanObject,
    mut v_n_3397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_3395_, v_t_3396_, v_n_3397_);
    return v___x_3398_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdx_x21___boxed(
    mut v_00_u03b1_3399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3400_: *mut crate::leanh::LeanObject,
    mut v_cmp_3401_: *mut crate::leanh::LeanObject,
    mut v_inst_3402_: *mut crate::leanh::LeanObject,
    mut v_t_3403_: *mut crate::leanh::LeanObject,
    mut v_n_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3405_ = l_Std_TreeMap_Raw_keyAtIdx_x21(
        v_00_u03b1_3399_,
        v_00_u03b2_3400_,
        v_cmp_3401_,
        v_inst_3402_,
        v_t_3403_,
        v_n_3404_,
    );
    crate::leanh::lean_dec(v_t_3403_);
    crate::leanh::lean_dec(v_inst_3402_);
    crate::leanh::lean_dec_ref(v_cmp_3401_);
    return v_res_3405_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdxD___redArg(
    mut v_t_3406_: *mut crate::leanh::LeanObject,
    mut v_n_3407_: *mut crate::leanh::LeanObject,
    mut v_fallback_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_3406_, v_n_3407_, v_fallback_3408_);
    return v___x_3409_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdxD___redArg___boxed(
    mut v_t_3410_: *mut crate::leanh::LeanObject,
    mut v_n_3411_: *mut crate::leanh::LeanObject,
    mut v_fallback_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Std_TreeMap_Raw_keyAtIdxD___redArg(v_t_3410_, v_n_3411_, v_fallback_3412_);
    crate::leanh::lean_dec(v_fallback_3412_);
    crate::leanh::lean_dec(v_t_3410_);
    return v_res_3413_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdxD(
    mut v_00_u03b1_3414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3415_: *mut crate::leanh::LeanObject,
    mut v_cmp_3416_: *mut crate::leanh::LeanObject,
    mut v_t_3417_: *mut crate::leanh::LeanObject,
    mut v_n_3418_: *mut crate::leanh::LeanObject,
    mut v_fallback_3419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3420_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_3417_, v_n_3418_, v_fallback_3419_);
    return v___x_3420_;
}
pub unsafe fn l_Std_TreeMap_Raw_keyAtIdxD___boxed(
    mut v_00_u03b1_3421_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3422_: *mut crate::leanh::LeanObject,
    mut v_cmp_3423_: *mut crate::leanh::LeanObject,
    mut v_t_3424_: *mut crate::leanh::LeanObject,
    mut v_n_3425_: *mut crate::leanh::LeanObject,
    mut v_fallback_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Std_TreeMap_Raw_keyAtIdxD(
        v_00_u03b1_3421_,
        v_00_u03b2_3422_,
        v_cmp_3423_,
        v_t_3424_,
        v_n_3425_,
        v_fallback_3426_,
    );
    crate::leanh::lean_dec(v_fallback_3426_);
    crate::leanh::lean_dec(v_t_3424_);
    crate::leanh::lean_dec_ref(v_cmp_3423_);
    return v_res_3427_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGE_x3f___redArg(
    mut v_cmp_3428_: *mut crate::leanh::LeanObject,
    mut v_t_3429_: *mut crate::leanh::LeanObject,
    mut v_k_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3431_ = crate::leanh::lean_box(0);
    v___x_3432_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3428_,
        v_k_3430_,
        v___x_3431_,
        v_t_3429_,
    );
    return v___x_3432_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGE_x3f(
    mut v_00_u03b1_3433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3434_: *mut crate::leanh::LeanObject,
    mut v_cmp_3435_: *mut crate::leanh::LeanObject,
    mut v_t_3436_: *mut crate::leanh::LeanObject,
    mut v_k_3437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3438_ = crate::leanh::lean_box(0);
    v___x_3439_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3435_,
        v_k_3437_,
        v___x_3438_,
        v_t_3436_,
    );
    return v___x_3439_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGT_x3f___redArg(
    mut v_cmp_3440_: *mut crate::leanh::LeanObject,
    mut v_t_3441_: *mut crate::leanh::LeanObject,
    mut v_k_3442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = crate::leanh::lean_box(0);
    v___x_3444_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3440_,
        v_k_3442_,
        v___x_3443_,
        v_t_3441_,
    );
    return v___x_3444_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGT_x3f(
    mut v_00_u03b1_3445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3446_: *mut crate::leanh::LeanObject,
    mut v_cmp_3447_: *mut crate::leanh::LeanObject,
    mut v_t_3448_: *mut crate::leanh::LeanObject,
    mut v_k_3449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = crate::leanh::lean_box(0);
    v___x_3451_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3447_,
        v_k_3449_,
        v___x_3450_,
        v_t_3448_,
    );
    return v___x_3451_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLE_x3f___redArg(
    mut v_cmp_3452_: *mut crate::leanh::LeanObject,
    mut v_t_3453_: *mut crate::leanh::LeanObject,
    mut v_k_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3455_ = crate::leanh::lean_box(0);
    v___x_3456_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3452_,
        v_k_3454_,
        v___x_3455_,
        v_t_3453_,
    );
    return v___x_3456_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLE_x3f(
    mut v_00_u03b1_3457_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3458_: *mut crate::leanh::LeanObject,
    mut v_cmp_3459_: *mut crate::leanh::LeanObject,
    mut v_t_3460_: *mut crate::leanh::LeanObject,
    mut v_k_3461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3462_ = crate::leanh::lean_box(0);
    v___x_3463_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3459_,
        v_k_3461_,
        v___x_3462_,
        v_t_3460_,
    );
    return v___x_3463_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLT_x3f___redArg(
    mut v_cmp_3464_: *mut crate::leanh::LeanObject,
    mut v_t_3465_: *mut crate::leanh::LeanObject,
    mut v_k_3466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = crate::leanh::lean_box(0);
    v___x_3468_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3464_,
        v_k_3466_,
        v___x_3467_,
        v_t_3465_,
    );
    return v___x_3468_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLT_x3f(
    mut v_00_u03b1_3469_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3470_: *mut crate::leanh::LeanObject,
    mut v_cmp_3471_: *mut crate::leanh::LeanObject,
    mut v_t_3472_: *mut crate::leanh::LeanObject,
    mut v_k_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = crate::leanh::lean_box(0);
    v___x_3475_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3471_,
        v_k_3473_,
        v___x_3474_,
        v_t_3472_,
    );
    return v___x_3475_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3479_ = l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__2;
    v___x_3480_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_3481_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_3482_ = l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__1;
    v___x_3483_ = l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__0;
    v___x_3484_ = l_mkPanicMessageWithDecl(
        v___x_3483_,
        v___x_3482_,
        v___x_3481_,
        v___x_3480_,
        v___x_3479_,
    );
    return v___x_3484_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGE_x21___redArg(
    mut v_cmp_3485_: *mut crate::leanh::LeanObject,
    mut v_inst_3486_: *mut crate::leanh::LeanObject,
    mut v_t_3487_: *mut crate::leanh::LeanObject,
    mut v_k_3488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = crate::leanh::lean_box(0);
    v___x_3490_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3485_,
        v_k_3488_,
        v___x_3489_,
        v_t_3487_,
    );
    if crate::leanh::lean_obj_tag(v___x_3490_) == 0 {
        let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3491_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3492_ = l_panic___redArg(v_inst_3486_, v___x_3491_);
        return v___x_3492_;
    } else {
        let mut v_val_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3493_ = crate::leanh::lean_ctor_get(v___x_3490_, 0);
        crate::leanh::lean_inc(v_val_3493_);
        crate::leanh::lean_dec_ref_known(v___x_3490_, 1);
        return v_val_3493_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGE_x21___redArg___boxed(
    mut v_cmp_3494_: *mut crate::leanh::LeanObject,
    mut v_inst_3495_: *mut crate::leanh::LeanObject,
    mut v_t_3496_: *mut crate::leanh::LeanObject,
    mut v_k_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ =
        l_Std_TreeMap_Raw_getEntryGE_x21___redArg(v_cmp_3494_, v_inst_3495_, v_t_3496_, v_k_3497_);
    crate::leanh::lean_dec_ref(v_inst_3495_);
    return v_res_3498_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGE_x21(
    mut v_00_u03b1_3499_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3500_: *mut crate::leanh::LeanObject,
    mut v_cmp_3501_: *mut crate::leanh::LeanObject,
    mut v_inst_3502_: *mut crate::leanh::LeanObject,
    mut v_t_3503_: *mut crate::leanh::LeanObject,
    mut v_k_3504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3505_ = crate::leanh::lean_box(0);
    v___x_3506_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3501_,
        v_k_3504_,
        v___x_3505_,
        v_t_3503_,
    );
    if crate::leanh::lean_obj_tag(v___x_3506_) == 0 {
        let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3507_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3508_ = l_panic___redArg(v_inst_3502_, v___x_3507_);
        return v___x_3508_;
    } else {
        let mut v_val_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3509_ = crate::leanh::lean_ctor_get(v___x_3506_, 0);
        crate::leanh::lean_inc(v_val_3509_);
        crate::leanh::lean_dec_ref_known(v___x_3506_, 1);
        return v_val_3509_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGE_x21___boxed(
    mut v_00_u03b1_3510_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3511_: *mut crate::leanh::LeanObject,
    mut v_cmp_3512_: *mut crate::leanh::LeanObject,
    mut v_inst_3513_: *mut crate::leanh::LeanObject,
    mut v_t_3514_: *mut crate::leanh::LeanObject,
    mut v_k_3515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3516_ = l_Std_TreeMap_Raw_getEntryGE_x21(
        v_00_u03b1_3510_,
        v_00_u03b2_3511_,
        v_cmp_3512_,
        v_inst_3513_,
        v_t_3514_,
        v_k_3515_,
    );
    crate::leanh::lean_dec_ref(v_inst_3513_);
    return v_res_3516_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGT_x21___redArg(
    mut v_cmp_3517_: *mut crate::leanh::LeanObject,
    mut v_inst_3518_: *mut crate::leanh::LeanObject,
    mut v_t_3519_: *mut crate::leanh::LeanObject,
    mut v_k_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ = crate::leanh::lean_box(0);
    v___x_3522_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3517_,
        v_k_3520_,
        v___x_3521_,
        v_t_3519_,
    );
    if crate::leanh::lean_obj_tag(v___x_3522_) == 0 {
        let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3523_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3524_ = l_panic___redArg(v_inst_3518_, v___x_3523_);
        return v___x_3524_;
    } else {
        let mut v_val_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3525_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
        crate::leanh::lean_inc(v_val_3525_);
        crate::leanh::lean_dec_ref_known(v___x_3522_, 1);
        return v_val_3525_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGT_x21___redArg___boxed(
    mut v_cmp_3526_: *mut crate::leanh::LeanObject,
    mut v_inst_3527_: *mut crate::leanh::LeanObject,
    mut v_t_3528_: *mut crate::leanh::LeanObject,
    mut v_k_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3530_ =
        l_Std_TreeMap_Raw_getEntryGT_x21___redArg(v_cmp_3526_, v_inst_3527_, v_t_3528_, v_k_3529_);
    crate::leanh::lean_dec_ref(v_inst_3527_);
    return v_res_3530_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGT_x21(
    mut v_00_u03b1_3531_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3532_: *mut crate::leanh::LeanObject,
    mut v_cmp_3533_: *mut crate::leanh::LeanObject,
    mut v_inst_3534_: *mut crate::leanh::LeanObject,
    mut v_t_3535_: *mut crate::leanh::LeanObject,
    mut v_k_3536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = crate::leanh::lean_box(0);
    v___x_3538_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3533_,
        v_k_3536_,
        v___x_3537_,
        v_t_3535_,
    );
    if crate::leanh::lean_obj_tag(v___x_3538_) == 0 {
        let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3539_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3540_ = l_panic___redArg(v_inst_3534_, v___x_3539_);
        return v___x_3540_;
    } else {
        let mut v_val_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3541_ = crate::leanh::lean_ctor_get(v___x_3538_, 0);
        crate::leanh::lean_inc(v_val_3541_);
        crate::leanh::lean_dec_ref_known(v___x_3538_, 1);
        return v_val_3541_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGT_x21___boxed(
    mut v_00_u03b1_3542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3543_: *mut crate::leanh::LeanObject,
    mut v_cmp_3544_: *mut crate::leanh::LeanObject,
    mut v_inst_3545_: *mut crate::leanh::LeanObject,
    mut v_t_3546_: *mut crate::leanh::LeanObject,
    mut v_k_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3548_ = l_Std_TreeMap_Raw_getEntryGT_x21(
        v_00_u03b1_3542_,
        v_00_u03b2_3543_,
        v_cmp_3544_,
        v_inst_3545_,
        v_t_3546_,
        v_k_3547_,
    );
    crate::leanh::lean_dec_ref(v_inst_3545_);
    return v_res_3548_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLE_x21___redArg(
    mut v_cmp_3549_: *mut crate::leanh::LeanObject,
    mut v_inst_3550_: *mut crate::leanh::LeanObject,
    mut v_t_3551_: *mut crate::leanh::LeanObject,
    mut v_k_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = crate::leanh::lean_box(0);
    v___x_3554_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3549_,
        v_k_3552_,
        v___x_3553_,
        v_t_3551_,
    );
    if crate::leanh::lean_obj_tag(v___x_3554_) == 0 {
        let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3555_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3556_ = l_panic___redArg(v_inst_3550_, v___x_3555_);
        return v___x_3556_;
    } else {
        let mut v_val_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3557_ = crate::leanh::lean_ctor_get(v___x_3554_, 0);
        crate::leanh::lean_inc(v_val_3557_);
        crate::leanh::lean_dec_ref_known(v___x_3554_, 1);
        return v_val_3557_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLE_x21___redArg___boxed(
    mut v_cmp_3558_: *mut crate::leanh::LeanObject,
    mut v_inst_3559_: *mut crate::leanh::LeanObject,
    mut v_t_3560_: *mut crate::leanh::LeanObject,
    mut v_k_3561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3562_ =
        l_Std_TreeMap_Raw_getEntryLE_x21___redArg(v_cmp_3558_, v_inst_3559_, v_t_3560_, v_k_3561_);
    crate::leanh::lean_dec_ref(v_inst_3559_);
    return v_res_3562_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLE_x21(
    mut v_00_u03b1_3563_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3564_: *mut crate::leanh::LeanObject,
    mut v_cmp_3565_: *mut crate::leanh::LeanObject,
    mut v_inst_3566_: *mut crate::leanh::LeanObject,
    mut v_t_3567_: *mut crate::leanh::LeanObject,
    mut v_k_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3569_ = crate::leanh::lean_box(0);
    v___x_3570_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3565_,
        v_k_3568_,
        v___x_3569_,
        v_t_3567_,
    );
    if crate::leanh::lean_obj_tag(v___x_3570_) == 0 {
        let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3571_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3572_ = l_panic___redArg(v_inst_3566_, v___x_3571_);
        return v___x_3572_;
    } else {
        let mut v_val_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3573_ = crate::leanh::lean_ctor_get(v___x_3570_, 0);
        crate::leanh::lean_inc(v_val_3573_);
        crate::leanh::lean_dec_ref_known(v___x_3570_, 1);
        return v_val_3573_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLE_x21___boxed(
    mut v_00_u03b1_3574_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3575_: *mut crate::leanh::LeanObject,
    mut v_cmp_3576_: *mut crate::leanh::LeanObject,
    mut v_inst_3577_: *mut crate::leanh::LeanObject,
    mut v_t_3578_: *mut crate::leanh::LeanObject,
    mut v_k_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3580_ = l_Std_TreeMap_Raw_getEntryLE_x21(
        v_00_u03b1_3574_,
        v_00_u03b2_3575_,
        v_cmp_3576_,
        v_inst_3577_,
        v_t_3578_,
        v_k_3579_,
    );
    crate::leanh::lean_dec_ref(v_inst_3577_);
    return v_res_3580_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLT_x21___redArg(
    mut v_cmp_3581_: *mut crate::leanh::LeanObject,
    mut v_inst_3582_: *mut crate::leanh::LeanObject,
    mut v_t_3583_: *mut crate::leanh::LeanObject,
    mut v_k_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = crate::leanh::lean_box(0);
    v___x_3586_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3581_,
        v_k_3584_,
        v___x_3585_,
        v_t_3583_,
    );
    if crate::leanh::lean_obj_tag(v___x_3586_) == 0 {
        let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3587_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3588_ = l_panic___redArg(v_inst_3582_, v___x_3587_);
        return v___x_3588_;
    } else {
        let mut v_val_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3589_ = crate::leanh::lean_ctor_get(v___x_3586_, 0);
        crate::leanh::lean_inc(v_val_3589_);
        crate::leanh::lean_dec_ref_known(v___x_3586_, 1);
        return v_val_3589_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLT_x21___redArg___boxed(
    mut v_cmp_3590_: *mut crate::leanh::LeanObject,
    mut v_inst_3591_: *mut crate::leanh::LeanObject,
    mut v_t_3592_: *mut crate::leanh::LeanObject,
    mut v_k_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3594_ =
        l_Std_TreeMap_Raw_getEntryLT_x21___redArg(v_cmp_3590_, v_inst_3591_, v_t_3592_, v_k_3593_);
    crate::leanh::lean_dec_ref(v_inst_3591_);
    return v_res_3594_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLT_x21(
    mut v_00_u03b1_3595_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3596_: *mut crate::leanh::LeanObject,
    mut v_cmp_3597_: *mut crate::leanh::LeanObject,
    mut v_inst_3598_: *mut crate::leanh::LeanObject,
    mut v_t_3599_: *mut crate::leanh::LeanObject,
    mut v_k_3600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3601_ = crate::leanh::lean_box(0);
    v___x_3602_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3597_,
        v_k_3600_,
        v___x_3601_,
        v_t_3599_,
    );
    if crate::leanh::lean_obj_tag(v___x_3602_) == 0 {
        let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3603_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3604_ = l_panic___redArg(v_inst_3598_, v___x_3603_);
        return v___x_3604_;
    } else {
        let mut v_val_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3605_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
        crate::leanh::lean_inc(v_val_3605_);
        crate::leanh::lean_dec_ref_known(v___x_3602_, 1);
        return v_val_3605_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLT_x21___boxed(
    mut v_00_u03b1_3606_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3607_: *mut crate::leanh::LeanObject,
    mut v_cmp_3608_: *mut crate::leanh::LeanObject,
    mut v_inst_3609_: *mut crate::leanh::LeanObject,
    mut v_t_3610_: *mut crate::leanh::LeanObject,
    mut v_k_3611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ = l_Std_TreeMap_Raw_getEntryLT_x21(
        v_00_u03b1_3606_,
        v_00_u03b2_3607_,
        v_cmp_3608_,
        v_inst_3609_,
        v_t_3610_,
        v_k_3611_,
    );
    crate::leanh::lean_dec_ref(v_inst_3609_);
    return v_res_3612_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGED___redArg(
    mut v_cmp_3613_: *mut crate::leanh::LeanObject,
    mut v_t_3614_: *mut crate::leanh::LeanObject,
    mut v_k_3615_: *mut crate::leanh::LeanObject,
    mut v_fallback_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3617_ = crate::leanh::lean_box(0);
    v___x_3618_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3613_,
        v_k_3615_,
        v___x_3617_,
        v_t_3614_,
    );
    if crate::leanh::lean_obj_tag(v___x_3618_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3616_);
        return v_fallback_3616_;
    } else {
        let mut v_val_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3619_ = crate::leanh::lean_ctor_get(v___x_3618_, 0);
        crate::leanh::lean_inc(v_val_3619_);
        crate::leanh::lean_dec_ref_known(v___x_3618_, 1);
        return v_val_3619_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGED___redArg___boxed(
    mut v_cmp_3620_: *mut crate::leanh::LeanObject,
    mut v_t_3621_: *mut crate::leanh::LeanObject,
    mut v_k_3622_: *mut crate::leanh::LeanObject,
    mut v_fallback_3623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3624_ =
        l_Std_TreeMap_Raw_getEntryGED___redArg(v_cmp_3620_, v_t_3621_, v_k_3622_, v_fallback_3623_);
    crate::leanh::lean_dec_ref(v_fallback_3623_);
    return v_res_3624_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGED(
    mut v_00_u03b1_3625_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3626_: *mut crate::leanh::LeanObject,
    mut v_cmp_3627_: *mut crate::leanh::LeanObject,
    mut v_t_3628_: *mut crate::leanh::LeanObject,
    mut v_k_3629_: *mut crate::leanh::LeanObject,
    mut v_fallback_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = crate::leanh::lean_box(0);
    v___x_3632_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_cmp_3627_,
        v_k_3629_,
        v___x_3631_,
        v_t_3628_,
    );
    if crate::leanh::lean_obj_tag(v___x_3632_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3630_);
        return v_fallback_3630_;
    } else {
        let mut v_val_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3633_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
        crate::leanh::lean_inc(v_val_3633_);
        crate::leanh::lean_dec_ref_known(v___x_3632_, 1);
        return v_val_3633_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGED___boxed(
    mut v_00_u03b1_3634_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3635_: *mut crate::leanh::LeanObject,
    mut v_cmp_3636_: *mut crate::leanh::LeanObject,
    mut v_t_3637_: *mut crate::leanh::LeanObject,
    mut v_k_3638_: *mut crate::leanh::LeanObject,
    mut v_fallback_3639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3640_ = l_Std_TreeMap_Raw_getEntryGED(
        v_00_u03b1_3634_,
        v_00_u03b2_3635_,
        v_cmp_3636_,
        v_t_3637_,
        v_k_3638_,
        v_fallback_3639_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3639_);
    return v_res_3640_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGTD___redArg(
    mut v_cmp_3641_: *mut crate::leanh::LeanObject,
    mut v_t_3642_: *mut crate::leanh::LeanObject,
    mut v_k_3643_: *mut crate::leanh::LeanObject,
    mut v_fallback_3644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3645_ = crate::leanh::lean_box(0);
    v___x_3646_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3641_,
        v_k_3643_,
        v___x_3645_,
        v_t_3642_,
    );
    if crate::leanh::lean_obj_tag(v___x_3646_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3644_);
        return v_fallback_3644_;
    } else {
        let mut v_val_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3647_ = crate::leanh::lean_ctor_get(v___x_3646_, 0);
        crate::leanh::lean_inc(v_val_3647_);
        crate::leanh::lean_dec_ref_known(v___x_3646_, 1);
        return v_val_3647_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGTD___redArg___boxed(
    mut v_cmp_3648_: *mut crate::leanh::LeanObject,
    mut v_t_3649_: *mut crate::leanh::LeanObject,
    mut v_k_3650_: *mut crate::leanh::LeanObject,
    mut v_fallback_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3652_ =
        l_Std_TreeMap_Raw_getEntryGTD___redArg(v_cmp_3648_, v_t_3649_, v_k_3650_, v_fallback_3651_);
    crate::leanh::lean_dec_ref(v_fallback_3651_);
    return v_res_3652_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGTD(
    mut v_00_u03b1_3653_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3654_: *mut crate::leanh::LeanObject,
    mut v_cmp_3655_: *mut crate::leanh::LeanObject,
    mut v_t_3656_: *mut crate::leanh::LeanObject,
    mut v_k_3657_: *mut crate::leanh::LeanObject,
    mut v_fallback_3658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = crate::leanh::lean_box(0);
    v___x_3660_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_cmp_3655_,
        v_k_3657_,
        v___x_3659_,
        v_t_3656_,
    );
    if crate::leanh::lean_obj_tag(v___x_3660_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3658_);
        return v_fallback_3658_;
    } else {
        let mut v_val_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3661_ = crate::leanh::lean_ctor_get(v___x_3660_, 0);
        crate::leanh::lean_inc(v_val_3661_);
        crate::leanh::lean_dec_ref_known(v___x_3660_, 1);
        return v_val_3661_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryGTD___boxed(
    mut v_00_u03b1_3662_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3663_: *mut crate::leanh::LeanObject,
    mut v_cmp_3664_: *mut crate::leanh::LeanObject,
    mut v_t_3665_: *mut crate::leanh::LeanObject,
    mut v_k_3666_: *mut crate::leanh::LeanObject,
    mut v_fallback_3667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3668_ = l_Std_TreeMap_Raw_getEntryGTD(
        v_00_u03b1_3662_,
        v_00_u03b2_3663_,
        v_cmp_3664_,
        v_t_3665_,
        v_k_3666_,
        v_fallback_3667_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3667_);
    return v_res_3668_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLED___redArg(
    mut v_cmp_3669_: *mut crate::leanh::LeanObject,
    mut v_t_3670_: *mut crate::leanh::LeanObject,
    mut v_k_3671_: *mut crate::leanh::LeanObject,
    mut v_fallback_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ = crate::leanh::lean_box(0);
    v___x_3674_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3669_,
        v_k_3671_,
        v___x_3673_,
        v_t_3670_,
    );
    if crate::leanh::lean_obj_tag(v___x_3674_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3672_);
        return v_fallback_3672_;
    } else {
        let mut v_val_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3675_ = crate::leanh::lean_ctor_get(v___x_3674_, 0);
        crate::leanh::lean_inc(v_val_3675_);
        crate::leanh::lean_dec_ref_known(v___x_3674_, 1);
        return v_val_3675_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLED___redArg___boxed(
    mut v_cmp_3676_: *mut crate::leanh::LeanObject,
    mut v_t_3677_: *mut crate::leanh::LeanObject,
    mut v_k_3678_: *mut crate::leanh::LeanObject,
    mut v_fallback_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3680_ =
        l_Std_TreeMap_Raw_getEntryLED___redArg(v_cmp_3676_, v_t_3677_, v_k_3678_, v_fallback_3679_);
    crate::leanh::lean_dec_ref(v_fallback_3679_);
    return v_res_3680_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLED(
    mut v_00_u03b1_3681_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3682_: *mut crate::leanh::LeanObject,
    mut v_cmp_3683_: *mut crate::leanh::LeanObject,
    mut v_t_3684_: *mut crate::leanh::LeanObject,
    mut v_k_3685_: *mut crate::leanh::LeanObject,
    mut v_fallback_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3687_ = crate::leanh::lean_box(0);
    v___x_3688_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_cmp_3683_,
        v_k_3685_,
        v___x_3687_,
        v_t_3684_,
    );
    if crate::leanh::lean_obj_tag(v___x_3688_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3686_);
        return v_fallback_3686_;
    } else {
        let mut v_val_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3689_ = crate::leanh::lean_ctor_get(v___x_3688_, 0);
        crate::leanh::lean_inc(v_val_3689_);
        crate::leanh::lean_dec_ref_known(v___x_3688_, 1);
        return v_val_3689_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLED___boxed(
    mut v_00_u03b1_3690_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3691_: *mut crate::leanh::LeanObject,
    mut v_cmp_3692_: *mut crate::leanh::LeanObject,
    mut v_t_3693_: *mut crate::leanh::LeanObject,
    mut v_k_3694_: *mut crate::leanh::LeanObject,
    mut v_fallback_3695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3696_ = l_Std_TreeMap_Raw_getEntryLED(
        v_00_u03b1_3690_,
        v_00_u03b2_3691_,
        v_cmp_3692_,
        v_t_3693_,
        v_k_3694_,
        v_fallback_3695_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3695_);
    return v_res_3696_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLTD___redArg(
    mut v_cmp_3697_: *mut crate::leanh::LeanObject,
    mut v_t_3698_: *mut crate::leanh::LeanObject,
    mut v_k_3699_: *mut crate::leanh::LeanObject,
    mut v_fallback_3700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3701_ = crate::leanh::lean_box(0);
    v___x_3702_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3697_,
        v_k_3699_,
        v___x_3701_,
        v_t_3698_,
    );
    if crate::leanh::lean_obj_tag(v___x_3702_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3700_);
        return v_fallback_3700_;
    } else {
        let mut v_val_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3703_ = crate::leanh::lean_ctor_get(v___x_3702_, 0);
        crate::leanh::lean_inc(v_val_3703_);
        crate::leanh::lean_dec_ref_known(v___x_3702_, 1);
        return v_val_3703_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLTD___redArg___boxed(
    mut v_cmp_3704_: *mut crate::leanh::LeanObject,
    mut v_t_3705_: *mut crate::leanh::LeanObject,
    mut v_k_3706_: *mut crate::leanh::LeanObject,
    mut v_fallback_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3708_ =
        l_Std_TreeMap_Raw_getEntryLTD___redArg(v_cmp_3704_, v_t_3705_, v_k_3706_, v_fallback_3707_);
    crate::leanh::lean_dec_ref(v_fallback_3707_);
    return v_res_3708_;
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLTD(
    mut v_00_u03b1_3709_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3710_: *mut crate::leanh::LeanObject,
    mut v_cmp_3711_: *mut crate::leanh::LeanObject,
    mut v_t_3712_: *mut crate::leanh::LeanObject,
    mut v_k_3713_: *mut crate::leanh::LeanObject,
    mut v_fallback_3714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3715_ = crate::leanh::lean_box(0);
    v___x_3716_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_cmp_3711_,
        v_k_3713_,
        v___x_3715_,
        v_t_3712_,
    );
    if crate::leanh::lean_obj_tag(v___x_3716_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_3714_);
        return v_fallback_3714_;
    } else {
        let mut v_val_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3717_ = crate::leanh::lean_ctor_get(v___x_3716_, 0);
        crate::leanh::lean_inc(v_val_3717_);
        crate::leanh::lean_dec_ref_known(v___x_3716_, 1);
        return v_val_3717_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getEntryLTD___boxed(
    mut v_00_u03b1_3718_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3719_: *mut crate::leanh::LeanObject,
    mut v_cmp_3720_: *mut crate::leanh::LeanObject,
    mut v_t_3721_: *mut crate::leanh::LeanObject,
    mut v_k_3722_: *mut crate::leanh::LeanObject,
    mut v_fallback_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3724_ = l_Std_TreeMap_Raw_getEntryLTD(
        v_00_u03b1_3718_,
        v_00_u03b2_3719_,
        v_cmp_3720_,
        v_t_3721_,
        v_k_3722_,
        v_fallback_3723_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3723_);
    return v_res_3724_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGE_x3f___redArg(
    mut v_cmp_3725_: *mut crate::leanh::LeanObject,
    mut v_t_3726_: *mut crate::leanh::LeanObject,
    mut v_k_3727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ = crate::leanh::lean_box(0);
    v___x_3729_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3725_,
        v_k_3727_,
        v___x_3728_,
        v_t_3726_,
    );
    return v___x_3729_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGE_x3f(
    mut v_00_u03b1_3730_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3731_: *mut crate::leanh::LeanObject,
    mut v_cmp_3732_: *mut crate::leanh::LeanObject,
    mut v_t_3733_: *mut crate::leanh::LeanObject,
    mut v_k_3734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = crate::leanh::lean_box(0);
    v___x_3736_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3732_,
        v_k_3734_,
        v___x_3735_,
        v_t_3733_,
    );
    return v___x_3736_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGT_x3f___redArg(
    mut v_cmp_3737_: *mut crate::leanh::LeanObject,
    mut v_t_3738_: *mut crate::leanh::LeanObject,
    mut v_k_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3740_ = crate::leanh::lean_box(0);
    v___x_3741_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3737_,
        v_k_3739_,
        v___x_3740_,
        v_t_3738_,
    );
    return v___x_3741_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGT_x3f(
    mut v_00_u03b1_3742_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3743_: *mut crate::leanh::LeanObject,
    mut v_cmp_3744_: *mut crate::leanh::LeanObject,
    mut v_t_3745_: *mut crate::leanh::LeanObject,
    mut v_k_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3747_ = crate::leanh::lean_box(0);
    v___x_3748_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3744_,
        v_k_3746_,
        v___x_3747_,
        v_t_3745_,
    );
    return v___x_3748_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLE_x3f___redArg(
    mut v_cmp_3749_: *mut crate::leanh::LeanObject,
    mut v_t_3750_: *mut crate::leanh::LeanObject,
    mut v_k_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3752_ = crate::leanh::lean_box(0);
    v___x_3753_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3749_,
        v_k_3751_,
        v___x_3752_,
        v_t_3750_,
    );
    return v___x_3753_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLE_x3f(
    mut v_00_u03b1_3754_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3755_: *mut crate::leanh::LeanObject,
    mut v_cmp_3756_: *mut crate::leanh::LeanObject,
    mut v_t_3757_: *mut crate::leanh::LeanObject,
    mut v_k_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3759_ = crate::leanh::lean_box(0);
    v___x_3760_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3756_,
        v_k_3758_,
        v___x_3759_,
        v_t_3757_,
    );
    return v___x_3760_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLT_x3f___redArg(
    mut v_cmp_3761_: *mut crate::leanh::LeanObject,
    mut v_t_3762_: *mut crate::leanh::LeanObject,
    mut v_k_3763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3764_ = crate::leanh::lean_box(0);
    v___x_3765_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3761_,
        v_k_3763_,
        v___x_3764_,
        v_t_3762_,
    );
    return v___x_3765_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLT_x3f(
    mut v_00_u03b1_3766_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3767_: *mut crate::leanh::LeanObject,
    mut v_cmp_3768_: *mut crate::leanh::LeanObject,
    mut v_t_3769_: *mut crate::leanh::LeanObject,
    mut v_k_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3771_ = crate::leanh::lean_box(0);
    v___x_3772_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3768_,
        v_k_3770_,
        v___x_3771_,
        v_t_3769_,
    );
    return v___x_3772_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGE_x21___redArg(
    mut v_cmp_3773_: *mut crate::leanh::LeanObject,
    mut v_inst_3774_: *mut crate::leanh::LeanObject,
    mut v_t_3775_: *mut crate::leanh::LeanObject,
    mut v_k_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3777_ = crate::leanh::lean_box(0);
    v___x_3778_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3773_,
        v_k_3776_,
        v___x_3777_,
        v_t_3775_,
    );
    if crate::leanh::lean_obj_tag(v___x_3778_) == 0 {
        let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3779_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3780_ = l_panic___redArg(v_inst_3774_, v___x_3779_);
        return v___x_3780_;
    } else {
        let mut v_val_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3781_ = crate::leanh::lean_ctor_get(v___x_3778_, 0);
        crate::leanh::lean_inc(v_val_3781_);
        crate::leanh::lean_dec_ref_known(v___x_3778_, 1);
        return v_val_3781_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGE_x21___redArg___boxed(
    mut v_cmp_3782_: *mut crate::leanh::LeanObject,
    mut v_inst_3783_: *mut crate::leanh::LeanObject,
    mut v_t_3784_: *mut crate::leanh::LeanObject,
    mut v_k_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3786_ =
        l_Std_TreeMap_Raw_getKeyGE_x21___redArg(v_cmp_3782_, v_inst_3783_, v_t_3784_, v_k_3785_);
    crate::leanh::lean_dec(v_inst_3783_);
    return v_res_3786_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGE_x21(
    mut v_00_u03b1_3787_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3788_: *mut crate::leanh::LeanObject,
    mut v_cmp_3789_: *mut crate::leanh::LeanObject,
    mut v_inst_3790_: *mut crate::leanh::LeanObject,
    mut v_t_3791_: *mut crate::leanh::LeanObject,
    mut v_k_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3793_ = crate::leanh::lean_box(0);
    v___x_3794_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3789_,
        v_k_3792_,
        v___x_3793_,
        v_t_3791_,
    );
    if crate::leanh::lean_obj_tag(v___x_3794_) == 0 {
        let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3795_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3796_ = l_panic___redArg(v_inst_3790_, v___x_3795_);
        return v___x_3796_;
    } else {
        let mut v_val_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3797_ = crate::leanh::lean_ctor_get(v___x_3794_, 0);
        crate::leanh::lean_inc(v_val_3797_);
        crate::leanh::lean_dec_ref_known(v___x_3794_, 1);
        return v_val_3797_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGE_x21___boxed(
    mut v_00_u03b1_3798_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3799_: *mut crate::leanh::LeanObject,
    mut v_cmp_3800_: *mut crate::leanh::LeanObject,
    mut v_inst_3801_: *mut crate::leanh::LeanObject,
    mut v_t_3802_: *mut crate::leanh::LeanObject,
    mut v_k_3803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3804_ = l_Std_TreeMap_Raw_getKeyGE_x21(
        v_00_u03b1_3798_,
        v_00_u03b2_3799_,
        v_cmp_3800_,
        v_inst_3801_,
        v_t_3802_,
        v_k_3803_,
    );
    crate::leanh::lean_dec(v_inst_3801_);
    return v_res_3804_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGT_x21___redArg(
    mut v_cmp_3805_: *mut crate::leanh::LeanObject,
    mut v_inst_3806_: *mut crate::leanh::LeanObject,
    mut v_t_3807_: *mut crate::leanh::LeanObject,
    mut v_k_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3809_ = crate::leanh::lean_box(0);
    v___x_3810_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3805_,
        v_k_3808_,
        v___x_3809_,
        v_t_3807_,
    );
    if crate::leanh::lean_obj_tag(v___x_3810_) == 0 {
        let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3811_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3812_ = l_panic___redArg(v_inst_3806_, v___x_3811_);
        return v___x_3812_;
    } else {
        let mut v_val_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3813_ = crate::leanh::lean_ctor_get(v___x_3810_, 0);
        crate::leanh::lean_inc(v_val_3813_);
        crate::leanh::lean_dec_ref_known(v___x_3810_, 1);
        return v_val_3813_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGT_x21___redArg___boxed(
    mut v_cmp_3814_: *mut crate::leanh::LeanObject,
    mut v_inst_3815_: *mut crate::leanh::LeanObject,
    mut v_t_3816_: *mut crate::leanh::LeanObject,
    mut v_k_3817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3818_ =
        l_Std_TreeMap_Raw_getKeyGT_x21___redArg(v_cmp_3814_, v_inst_3815_, v_t_3816_, v_k_3817_);
    crate::leanh::lean_dec(v_inst_3815_);
    return v_res_3818_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGT_x21(
    mut v_00_u03b1_3819_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3820_: *mut crate::leanh::LeanObject,
    mut v_cmp_3821_: *mut crate::leanh::LeanObject,
    mut v_inst_3822_: *mut crate::leanh::LeanObject,
    mut v_t_3823_: *mut crate::leanh::LeanObject,
    mut v_k_3824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = crate::leanh::lean_box(0);
    v___x_3826_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3821_,
        v_k_3824_,
        v___x_3825_,
        v_t_3823_,
    );
    if crate::leanh::lean_obj_tag(v___x_3826_) == 0 {
        let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3827_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3828_ = l_panic___redArg(v_inst_3822_, v___x_3827_);
        return v___x_3828_;
    } else {
        let mut v_val_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3829_ = crate::leanh::lean_ctor_get(v___x_3826_, 0);
        crate::leanh::lean_inc(v_val_3829_);
        crate::leanh::lean_dec_ref_known(v___x_3826_, 1);
        return v_val_3829_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGT_x21___boxed(
    mut v_00_u03b1_3830_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3831_: *mut crate::leanh::LeanObject,
    mut v_cmp_3832_: *mut crate::leanh::LeanObject,
    mut v_inst_3833_: *mut crate::leanh::LeanObject,
    mut v_t_3834_: *mut crate::leanh::LeanObject,
    mut v_k_3835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3836_ = l_Std_TreeMap_Raw_getKeyGT_x21(
        v_00_u03b1_3830_,
        v_00_u03b2_3831_,
        v_cmp_3832_,
        v_inst_3833_,
        v_t_3834_,
        v_k_3835_,
    );
    crate::leanh::lean_dec(v_inst_3833_);
    return v_res_3836_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLE_x21___redArg(
    mut v_cmp_3837_: *mut crate::leanh::LeanObject,
    mut v_inst_3838_: *mut crate::leanh::LeanObject,
    mut v_t_3839_: *mut crate::leanh::LeanObject,
    mut v_k_3840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = crate::leanh::lean_box(0);
    v___x_3842_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3837_,
        v_k_3840_,
        v___x_3841_,
        v_t_3839_,
    );
    if crate::leanh::lean_obj_tag(v___x_3842_) == 0 {
        let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3843_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3844_ = l_panic___redArg(v_inst_3838_, v___x_3843_);
        return v___x_3844_;
    } else {
        let mut v_val_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3845_ = crate::leanh::lean_ctor_get(v___x_3842_, 0);
        crate::leanh::lean_inc(v_val_3845_);
        crate::leanh::lean_dec_ref_known(v___x_3842_, 1);
        return v_val_3845_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLE_x21___redArg___boxed(
    mut v_cmp_3846_: *mut crate::leanh::LeanObject,
    mut v_inst_3847_: *mut crate::leanh::LeanObject,
    mut v_t_3848_: *mut crate::leanh::LeanObject,
    mut v_k_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3850_ =
        l_Std_TreeMap_Raw_getKeyLE_x21___redArg(v_cmp_3846_, v_inst_3847_, v_t_3848_, v_k_3849_);
    crate::leanh::lean_dec(v_inst_3847_);
    return v_res_3850_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLE_x21(
    mut v_00_u03b1_3851_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3852_: *mut crate::leanh::LeanObject,
    mut v_cmp_3853_: *mut crate::leanh::LeanObject,
    mut v_inst_3854_: *mut crate::leanh::LeanObject,
    mut v_t_3855_: *mut crate::leanh::LeanObject,
    mut v_k_3856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3857_ = crate::leanh::lean_box(0);
    v___x_3858_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3853_,
        v_k_3856_,
        v___x_3857_,
        v_t_3855_,
    );
    if crate::leanh::lean_obj_tag(v___x_3858_) == 0 {
        let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3859_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3860_ = l_panic___redArg(v_inst_3854_, v___x_3859_);
        return v___x_3860_;
    } else {
        let mut v_val_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3861_ = crate::leanh::lean_ctor_get(v___x_3858_, 0);
        crate::leanh::lean_inc(v_val_3861_);
        crate::leanh::lean_dec_ref_known(v___x_3858_, 1);
        return v_val_3861_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLE_x21___boxed(
    mut v_00_u03b1_3862_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3863_: *mut crate::leanh::LeanObject,
    mut v_cmp_3864_: *mut crate::leanh::LeanObject,
    mut v_inst_3865_: *mut crate::leanh::LeanObject,
    mut v_t_3866_: *mut crate::leanh::LeanObject,
    mut v_k_3867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Std_TreeMap_Raw_getKeyLE_x21(
        v_00_u03b1_3862_,
        v_00_u03b2_3863_,
        v_cmp_3864_,
        v_inst_3865_,
        v_t_3866_,
        v_k_3867_,
    );
    crate::leanh::lean_dec(v_inst_3865_);
    return v_res_3868_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLT_x21___redArg(
    mut v_cmp_3869_: *mut crate::leanh::LeanObject,
    mut v_inst_3870_: *mut crate::leanh::LeanObject,
    mut v_t_3871_: *mut crate::leanh::LeanObject,
    mut v_k_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3873_ = crate::leanh::lean_box(0);
    v___x_3874_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3869_,
        v_k_3872_,
        v___x_3873_,
        v_t_3871_,
    );
    if crate::leanh::lean_obj_tag(v___x_3874_) == 0 {
        let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3875_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3876_ = l_panic___redArg(v_inst_3870_, v___x_3875_);
        return v___x_3876_;
    } else {
        let mut v_val_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3877_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
        crate::leanh::lean_inc(v_val_3877_);
        crate::leanh::lean_dec_ref_known(v___x_3874_, 1);
        return v_val_3877_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLT_x21___redArg___boxed(
    mut v_cmp_3878_: *mut crate::leanh::LeanObject,
    mut v_inst_3879_: *mut crate::leanh::LeanObject,
    mut v_t_3880_: *mut crate::leanh::LeanObject,
    mut v_k_3881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3882_ =
        l_Std_TreeMap_Raw_getKeyLT_x21___redArg(v_cmp_3878_, v_inst_3879_, v_t_3880_, v_k_3881_);
    crate::leanh::lean_dec(v_inst_3879_);
    return v_res_3882_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLT_x21(
    mut v_00_u03b1_3883_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3884_: *mut crate::leanh::LeanObject,
    mut v_cmp_3885_: *mut crate::leanh::LeanObject,
    mut v_inst_3886_: *mut crate::leanh::LeanObject,
    mut v_t_3887_: *mut crate::leanh::LeanObject,
    mut v_k_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3889_ = crate::leanh::lean_box(0);
    v___x_3890_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3885_,
        v_k_3888_,
        v___x_3889_,
        v_t_3887_,
    );
    if crate::leanh::lean_obj_tag(v___x_3890_) == 0 {
        let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3891_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeMap_Raw_getEntryGE_x21___redArg___closed__3,
        );
        v___x_3892_ = l_panic___redArg(v_inst_3886_, v___x_3891_);
        return v___x_3892_;
    } else {
        let mut v_val_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3893_ = crate::leanh::lean_ctor_get(v___x_3890_, 0);
        crate::leanh::lean_inc(v_val_3893_);
        crate::leanh::lean_dec_ref_known(v___x_3890_, 1);
        return v_val_3893_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLT_x21___boxed(
    mut v_00_u03b1_3894_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3895_: *mut crate::leanh::LeanObject,
    mut v_cmp_3896_: *mut crate::leanh::LeanObject,
    mut v_inst_3897_: *mut crate::leanh::LeanObject,
    mut v_t_3898_: *mut crate::leanh::LeanObject,
    mut v_k_3899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3900_ = l_Std_TreeMap_Raw_getKeyLT_x21(
        v_00_u03b1_3894_,
        v_00_u03b2_3895_,
        v_cmp_3896_,
        v_inst_3897_,
        v_t_3898_,
        v_k_3899_,
    );
    crate::leanh::lean_dec(v_inst_3897_);
    return v_res_3900_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGED___redArg(
    mut v_cmp_3901_: *mut crate::leanh::LeanObject,
    mut v_t_3902_: *mut crate::leanh::LeanObject,
    mut v_k_3903_: *mut crate::leanh::LeanObject,
    mut v_fallback_3904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3905_ = crate::leanh::lean_box(0);
    v___x_3906_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3901_,
        v_k_3903_,
        v___x_3905_,
        v_t_3902_,
    );
    if crate::leanh::lean_obj_tag(v___x_3906_) == 0 {
        crate::leanh::lean_inc(v_fallback_3904_);
        return v_fallback_3904_;
    } else {
        let mut v_val_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3907_ = crate::leanh::lean_ctor_get(v___x_3906_, 0);
        crate::leanh::lean_inc(v_val_3907_);
        crate::leanh::lean_dec_ref_known(v___x_3906_, 1);
        return v_val_3907_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGED___redArg___boxed(
    mut v_cmp_3908_: *mut crate::leanh::LeanObject,
    mut v_t_3909_: *mut crate::leanh::LeanObject,
    mut v_k_3910_: *mut crate::leanh::LeanObject,
    mut v_fallback_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3912_ =
        l_Std_TreeMap_Raw_getKeyGED___redArg(v_cmp_3908_, v_t_3909_, v_k_3910_, v_fallback_3911_);
    crate::leanh::lean_dec(v_fallback_3911_);
    return v_res_3912_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGED(
    mut v_00_u03b1_3913_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3914_: *mut crate::leanh::LeanObject,
    mut v_cmp_3915_: *mut crate::leanh::LeanObject,
    mut v_t_3916_: *mut crate::leanh::LeanObject,
    mut v_k_3917_: *mut crate::leanh::LeanObject,
    mut v_fallback_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ = crate::leanh::lean_box(0);
    v___x_3920_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_3915_,
        v_k_3917_,
        v___x_3919_,
        v_t_3916_,
    );
    if crate::leanh::lean_obj_tag(v___x_3920_) == 0 {
        crate::leanh::lean_inc(v_fallback_3918_);
        return v_fallback_3918_;
    } else {
        let mut v_val_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3921_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
        crate::leanh::lean_inc(v_val_3921_);
        crate::leanh::lean_dec_ref_known(v___x_3920_, 1);
        return v_val_3921_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGED___boxed(
    mut v_00_u03b1_3922_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3923_: *mut crate::leanh::LeanObject,
    mut v_cmp_3924_: *mut crate::leanh::LeanObject,
    mut v_t_3925_: *mut crate::leanh::LeanObject,
    mut v_k_3926_: *mut crate::leanh::LeanObject,
    mut v_fallback_3927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3928_ = l_Std_TreeMap_Raw_getKeyGED(
        v_00_u03b1_3922_,
        v_00_u03b2_3923_,
        v_cmp_3924_,
        v_t_3925_,
        v_k_3926_,
        v_fallback_3927_,
    );
    crate::leanh::lean_dec(v_fallback_3927_);
    return v_res_3928_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGTD___redArg(
    mut v_cmp_3929_: *mut crate::leanh::LeanObject,
    mut v_t_3930_: *mut crate::leanh::LeanObject,
    mut v_k_3931_: *mut crate::leanh::LeanObject,
    mut v_fallback_3932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3933_ = crate::leanh::lean_box(0);
    v___x_3934_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3929_,
        v_k_3931_,
        v___x_3933_,
        v_t_3930_,
    );
    if crate::leanh::lean_obj_tag(v___x_3934_) == 0 {
        crate::leanh::lean_inc(v_fallback_3932_);
        return v_fallback_3932_;
    } else {
        let mut v_val_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3935_ = crate::leanh::lean_ctor_get(v___x_3934_, 0);
        crate::leanh::lean_inc(v_val_3935_);
        crate::leanh::lean_dec_ref_known(v___x_3934_, 1);
        return v_val_3935_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGTD___redArg___boxed(
    mut v_cmp_3936_: *mut crate::leanh::LeanObject,
    mut v_t_3937_: *mut crate::leanh::LeanObject,
    mut v_k_3938_: *mut crate::leanh::LeanObject,
    mut v_fallback_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3940_ =
        l_Std_TreeMap_Raw_getKeyGTD___redArg(v_cmp_3936_, v_t_3937_, v_k_3938_, v_fallback_3939_);
    crate::leanh::lean_dec(v_fallback_3939_);
    return v_res_3940_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGTD(
    mut v_00_u03b1_3941_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3942_: *mut crate::leanh::LeanObject,
    mut v_cmp_3943_: *mut crate::leanh::LeanObject,
    mut v_t_3944_: *mut crate::leanh::LeanObject,
    mut v_k_3945_: *mut crate::leanh::LeanObject,
    mut v_fallback_3946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3947_ = crate::leanh::lean_box(0);
    v___x_3948_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_3943_,
        v_k_3945_,
        v___x_3947_,
        v_t_3944_,
    );
    if crate::leanh::lean_obj_tag(v___x_3948_) == 0 {
        crate::leanh::lean_inc(v_fallback_3946_);
        return v_fallback_3946_;
    } else {
        let mut v_val_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3949_ = crate::leanh::lean_ctor_get(v___x_3948_, 0);
        crate::leanh::lean_inc(v_val_3949_);
        crate::leanh::lean_dec_ref_known(v___x_3948_, 1);
        return v_val_3949_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyGTD___boxed(
    mut v_00_u03b1_3950_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3951_: *mut crate::leanh::LeanObject,
    mut v_cmp_3952_: *mut crate::leanh::LeanObject,
    mut v_t_3953_: *mut crate::leanh::LeanObject,
    mut v_k_3954_: *mut crate::leanh::LeanObject,
    mut v_fallback_3955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Std_TreeMap_Raw_getKeyGTD(
        v_00_u03b1_3950_,
        v_00_u03b2_3951_,
        v_cmp_3952_,
        v_t_3953_,
        v_k_3954_,
        v_fallback_3955_,
    );
    crate::leanh::lean_dec(v_fallback_3955_);
    return v_res_3956_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLED___redArg(
    mut v_cmp_3957_: *mut crate::leanh::LeanObject,
    mut v_t_3958_: *mut crate::leanh::LeanObject,
    mut v_k_3959_: *mut crate::leanh::LeanObject,
    mut v_fallback_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3961_ = crate::leanh::lean_box(0);
    v___x_3962_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3957_,
        v_k_3959_,
        v___x_3961_,
        v_t_3958_,
    );
    if crate::leanh::lean_obj_tag(v___x_3962_) == 0 {
        crate::leanh::lean_inc(v_fallback_3960_);
        return v_fallback_3960_;
    } else {
        let mut v_val_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3963_ = crate::leanh::lean_ctor_get(v___x_3962_, 0);
        crate::leanh::lean_inc(v_val_3963_);
        crate::leanh::lean_dec_ref_known(v___x_3962_, 1);
        return v_val_3963_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLED___redArg___boxed(
    mut v_cmp_3964_: *mut crate::leanh::LeanObject,
    mut v_t_3965_: *mut crate::leanh::LeanObject,
    mut v_k_3966_: *mut crate::leanh::LeanObject,
    mut v_fallback_3967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3968_ =
        l_Std_TreeMap_Raw_getKeyLED___redArg(v_cmp_3964_, v_t_3965_, v_k_3966_, v_fallback_3967_);
    crate::leanh::lean_dec(v_fallback_3967_);
    return v_res_3968_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLED(
    mut v_00_u03b1_3969_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3970_: *mut crate::leanh::LeanObject,
    mut v_cmp_3971_: *mut crate::leanh::LeanObject,
    mut v_t_3972_: *mut crate::leanh::LeanObject,
    mut v_k_3973_: *mut crate::leanh::LeanObject,
    mut v_fallback_3974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3975_ = crate::leanh::lean_box(0);
    v___x_3976_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_3971_,
        v_k_3973_,
        v___x_3975_,
        v_t_3972_,
    );
    if crate::leanh::lean_obj_tag(v___x_3976_) == 0 {
        crate::leanh::lean_inc(v_fallback_3974_);
        return v_fallback_3974_;
    } else {
        let mut v_val_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3977_ = crate::leanh::lean_ctor_get(v___x_3976_, 0);
        crate::leanh::lean_inc(v_val_3977_);
        crate::leanh::lean_dec_ref_known(v___x_3976_, 1);
        return v_val_3977_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLED___boxed(
    mut v_00_u03b1_3978_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3979_: *mut crate::leanh::LeanObject,
    mut v_cmp_3980_: *mut crate::leanh::LeanObject,
    mut v_t_3981_: *mut crate::leanh::LeanObject,
    mut v_k_3982_: *mut crate::leanh::LeanObject,
    mut v_fallback_3983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3984_ = l_Std_TreeMap_Raw_getKeyLED(
        v_00_u03b1_3978_,
        v_00_u03b2_3979_,
        v_cmp_3980_,
        v_t_3981_,
        v_k_3982_,
        v_fallback_3983_,
    );
    crate::leanh::lean_dec(v_fallback_3983_);
    return v_res_3984_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLTD___redArg(
    mut v_cmp_3985_: *mut crate::leanh::LeanObject,
    mut v_t_3986_: *mut crate::leanh::LeanObject,
    mut v_k_3987_: *mut crate::leanh::LeanObject,
    mut v_fallback_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3989_ = crate::leanh::lean_box(0);
    v___x_3990_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3985_,
        v_k_3987_,
        v___x_3989_,
        v_t_3986_,
    );
    if crate::leanh::lean_obj_tag(v___x_3990_) == 0 {
        crate::leanh::lean_inc(v_fallback_3988_);
        return v_fallback_3988_;
    } else {
        let mut v_val_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3991_ = crate::leanh::lean_ctor_get(v___x_3990_, 0);
        crate::leanh::lean_inc(v_val_3991_);
        crate::leanh::lean_dec_ref_known(v___x_3990_, 1);
        return v_val_3991_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLTD___redArg___boxed(
    mut v_cmp_3992_: *mut crate::leanh::LeanObject,
    mut v_t_3993_: *mut crate::leanh::LeanObject,
    mut v_k_3994_: *mut crate::leanh::LeanObject,
    mut v_fallback_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3996_ =
        l_Std_TreeMap_Raw_getKeyLTD___redArg(v_cmp_3992_, v_t_3993_, v_k_3994_, v_fallback_3995_);
    crate::leanh::lean_dec(v_fallback_3995_);
    return v_res_3996_;
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLTD(
    mut v_00_u03b1_3997_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3998_: *mut crate::leanh::LeanObject,
    mut v_cmp_3999_: *mut crate::leanh::LeanObject,
    mut v_t_4000_: *mut crate::leanh::LeanObject,
    mut v_k_4001_: *mut crate::leanh::LeanObject,
    mut v_fallback_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4003_ = crate::leanh::lean_box(0);
    v___x_4004_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_3999_,
        v_k_4001_,
        v___x_4003_,
        v_t_4000_,
    );
    if crate::leanh::lean_obj_tag(v___x_4004_) == 0 {
        crate::leanh::lean_inc(v_fallback_4002_);
        return v_fallback_4002_;
    } else {
        let mut v_val_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4005_ = crate::leanh::lean_ctor_get(v___x_4004_, 0);
        crate::leanh::lean_inc(v_val_4005_);
        crate::leanh::lean_dec_ref_known(v___x_4004_, 1);
        return v_val_4005_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_getKeyLTD___boxed(
    mut v_00_u03b1_4006_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4007_: *mut crate::leanh::LeanObject,
    mut v_cmp_4008_: *mut crate::leanh::LeanObject,
    mut v_t_4009_: *mut crate::leanh::LeanObject,
    mut v_k_4010_: *mut crate::leanh::LeanObject,
    mut v_fallback_4011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4012_ = l_Std_TreeMap_Raw_getKeyLTD(
        v_00_u03b1_4006_,
        v_00_u03b2_4007_,
        v_cmp_4008_,
        v_t_4009_,
        v_k_4010_,
        v_fallback_4011_,
    );
    crate::leanh::lean_dec(v_fallback_4011_);
    return v_res_4012_;
}
pub unsafe fn l_Std_TreeMap_Raw_filter___redArg(
    mut v_f_4013_: *mut crate::leanh::LeanObject,
    mut v_t_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4015_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_4013_, v_t_4014_);
    return v___x_4015_;
}
pub unsafe fn l_Std_TreeMap_Raw_filter(
    mut v_00_u03b1_4016_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4017_: *mut crate::leanh::LeanObject,
    mut v_cmp_4018_: *mut crate::leanh::LeanObject,
    mut v_f_4019_: *mut crate::leanh::LeanObject,
    mut v_t_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_4019_, v_t_4020_);
    return v___x_4021_;
}
pub unsafe fn l_Std_TreeMap_Raw_filter___boxed(
    mut v_00_u03b1_4022_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4023_: *mut crate::leanh::LeanObject,
    mut v_cmp_4024_: *mut crate::leanh::LeanObject,
    mut v_f_4025_: *mut crate::leanh::LeanObject,
    mut v_t_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4027_ = l_Std_TreeMap_Raw_filter(
        v_00_u03b1_4022_,
        v_00_u03b2_4023_,
        v_cmp_4024_,
        v_f_4025_,
        v_t_4026_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4024_);
    return v_res_4027_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldlM___redArg(
    mut v_inst_4028_: *mut crate::leanh::LeanObject,
    mut v_f_4029_: *mut crate::leanh::LeanObject,
    mut v_init_4030_: *mut crate::leanh::LeanObject,
    mut v_t_4031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4032_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4028_,
        v_f_4029_,
        v_init_4030_,
        v_t_4031_,
    );
    return v___x_4032_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldlM(
    mut v_00_u03b1_4033_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4034_: *mut crate::leanh::LeanObject,
    mut v_cmp_4035_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4036_: *mut crate::leanh::LeanObject,
    mut v_m_4037_: *mut crate::leanh::LeanObject,
    mut v_inst_4038_: *mut crate::leanh::LeanObject,
    mut v_f_4039_: *mut crate::leanh::LeanObject,
    mut v_init_4040_: *mut crate::leanh::LeanObject,
    mut v_t_4041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4038_,
        v_f_4039_,
        v_init_4040_,
        v_t_4041_,
    );
    return v___x_4042_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldlM___boxed(
    mut v_00_u03b1_4043_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4044_: *mut crate::leanh::LeanObject,
    mut v_cmp_4045_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4046_: *mut crate::leanh::LeanObject,
    mut v_m_4047_: *mut crate::leanh::LeanObject,
    mut v_inst_4048_: *mut crate::leanh::LeanObject,
    mut v_f_4049_: *mut crate::leanh::LeanObject,
    mut v_init_4050_: *mut crate::leanh::LeanObject,
    mut v_t_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4052_ = l_Std_TreeMap_Raw_foldlM(
        v_00_u03b1_4043_,
        v_00_u03b2_4044_,
        v_cmp_4045_,
        v_00_u03b4_4046_,
        v_m_4047_,
        v_inst_4048_,
        v_f_4049_,
        v_init_4050_,
        v_t_4051_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4045_);
    return v_res_4052_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldl___redArg(
    mut v_f_4053_: *mut crate::leanh::LeanObject,
    mut v_init_4054_: *mut crate::leanh::LeanObject,
    mut v_t_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_4053_, v_init_4054_, v_t_4055_);
    return v___x_4056_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldl(
    mut v_00_u03b1_4057_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4058_: *mut crate::leanh::LeanObject,
    mut v_cmp_4059_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4060_: *mut crate::leanh::LeanObject,
    mut v_f_4061_: *mut crate::leanh::LeanObject,
    mut v_init_4062_: *mut crate::leanh::LeanObject,
    mut v_t_4063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4064_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_4061_, v_init_4062_, v_t_4063_);
    return v___x_4064_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldl___boxed(
    mut v_00_u03b1_4065_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4066_: *mut crate::leanh::LeanObject,
    mut v_cmp_4067_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4068_: *mut crate::leanh::LeanObject,
    mut v_f_4069_: *mut crate::leanh::LeanObject,
    mut v_init_4070_: *mut crate::leanh::LeanObject,
    mut v_t_4071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4072_ = l_Std_TreeMap_Raw_foldl(
        v_00_u03b1_4065_,
        v_00_u03b2_4066_,
        v_cmp_4067_,
        v_00_u03b4_4068_,
        v_f_4069_,
        v_init_4070_,
        v_t_4071_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4067_);
    return v_res_4072_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldrM___redArg(
    mut v_inst_4073_: *mut crate::leanh::LeanObject,
    mut v_f_4074_: *mut crate::leanh::LeanObject,
    mut v_init_4075_: *mut crate::leanh::LeanObject,
    mut v_t_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4077_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_4073_,
        v_f_4074_,
        v_init_4075_,
        v_t_4076_,
    );
    return v___x_4077_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldrM(
    mut v_00_u03b1_4078_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4079_: *mut crate::leanh::LeanObject,
    mut v_cmp_4080_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4081_: *mut crate::leanh::LeanObject,
    mut v_m_4082_: *mut crate::leanh::LeanObject,
    mut v_inst_4083_: *mut crate::leanh::LeanObject,
    mut v_f_4084_: *mut crate::leanh::LeanObject,
    mut v_init_4085_: *mut crate::leanh::LeanObject,
    mut v_t_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4087_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_4083_,
        v_f_4084_,
        v_init_4085_,
        v_t_4086_,
    );
    return v___x_4087_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldrM___boxed(
    mut v_00_u03b1_4088_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4089_: *mut crate::leanh::LeanObject,
    mut v_cmp_4090_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4091_: *mut crate::leanh::LeanObject,
    mut v_m_4092_: *mut crate::leanh::LeanObject,
    mut v_inst_4093_: *mut crate::leanh::LeanObject,
    mut v_f_4094_: *mut crate::leanh::LeanObject,
    mut v_init_4095_: *mut crate::leanh::LeanObject,
    mut v_t_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Std_TreeMap_Raw_foldrM(
        v_00_u03b1_4088_,
        v_00_u03b2_4089_,
        v_cmp_4090_,
        v_00_u03b4_4091_,
        v_m_4092_,
        v_inst_4093_,
        v_f_4094_,
        v_init_4095_,
        v_t_4096_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4090_);
    return v_res_4097_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldr___redArg___lam__0(
    mut v_f_4098_: *mut crate::leanh::LeanObject,
    mut v_x1_4099_: *mut crate::leanh::LeanObject,
    mut v_x2_4100_: *mut crate::leanh::LeanObject,
    mut v_x3_4101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4102_ = crate::leanh::lean_apply_3(v_f_4098_, v_x1_4099_, v_x2_4100_, v_x3_4101_);
    return v___x_4102_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldr___redArg(
    mut v_f_4122_: *mut crate::leanh::LeanObject,
    mut v_init_4123_: *mut crate::leanh::LeanObject,
    mut v_t_4124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4125_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4125_, 0, v_f_4122_);
    v___x_4126_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4127_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4126_,
        v___f_4125_,
        v_init_4123_,
        v_t_4124_,
    );
    return v___x_4127_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldr(
    mut v_00_u03b1_4128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4129_: *mut crate::leanh::LeanObject,
    mut v_cmp_4130_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4131_: *mut crate::leanh::LeanObject,
    mut v_f_4132_: *mut crate::leanh::LeanObject,
    mut v_init_4133_: *mut crate::leanh::LeanObject,
    mut v_t_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4135_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4135_, 0, v_f_4132_);
    v___x_4136_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4137_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4136_,
        v___f_4135_,
        v_init_4133_,
        v_t_4134_,
    );
    return v___x_4137_;
}
pub unsafe fn l_Std_TreeMap_Raw_foldr___boxed(
    mut v_00_u03b1_4138_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4139_: *mut crate::leanh::LeanObject,
    mut v_cmp_4140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4141_: *mut crate::leanh::LeanObject,
    mut v_f_4142_: *mut crate::leanh::LeanObject,
    mut v_init_4143_: *mut crate::leanh::LeanObject,
    mut v_t_4144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4145_ = l_Std_TreeMap_Raw_foldr(
        v_00_u03b1_4138_,
        v_00_u03b2_4139_,
        v_cmp_4140_,
        v_00_u03b4_4141_,
        v_f_4142_,
        v_init_4143_,
        v_t_4144_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4140_);
    return v_res_4145_;
}
pub unsafe fn l_Std_TreeMap_Raw_partition___redArg___lam__0(
    mut v_f_4146_: *mut crate::leanh::LeanObject,
    mut v_cmp_4147_: *mut crate::leanh::LeanObject,
    mut v_x_4148_: *mut crate::leanh::LeanObject,
    mut v_a_4149_: *mut crate::leanh::LeanObject,
    mut v_b_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4166_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4151_ = crate::leanh::lean_ctor_get(v_x_4148_, 0);
                v_snd_4152_ = crate::leanh::lean_ctor_get(v_x_4148_, 1);
                v_isSharedCheck_4166_ = (!crate::leanh::lean_is_exclusive(v_x_4148_)) as u8;
                if v_isSharedCheck_4166_ == 0 {
                    v___x_4154_ = v_x_4148_;
                    v_isShared_4155_ = v_isSharedCheck_4166_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4152_);
                    crate::leanh::lean_inc(v_fst_4151_);
                    crate::leanh::lean_dec(v_x_4148_);
                    v___x_4154_ = crate::leanh::lean_box(0);
                    v_isShared_4155_ = v_isSharedCheck_4166_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_b_4150_);
                crate::leanh::lean_inc(v_a_4149_);
                v___x_4156_ = crate::leanh::lean_apply_2(v_f_4146_, v_a_4149_, v_b_4150_);
                v___x_4157_ = (crate::leanh::lean_unbox(v___x_4156_) as u8);
                if v___x_4157_ == 0 {
                    v___x_4158_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                        v_cmp_4147_,
                        v_a_4149_,
                        v_b_4150_,
                        v_snd_4152_,
                    );
                    if v_isShared_4155_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4154_, 1, v___x_4158_);
                        v___x_4160_ = v___x_4154_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4161_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_fst_4151_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___x_4158_);
                        v___x_4160_ = v_reuseFailAlloc_4161_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4162_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                        v_cmp_4147_,
                        v_a_4149_,
                        v_b_4150_,
                        v_fst_4151_,
                    );
                    if v_isShared_4155_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4154_, 0, v___x_4162_);
                        v___x_4164_ = v___x_4154_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4165_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_snd_4152_);
                        v___x_4164_ = v_reuseFailAlloc_4165_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4160_;
            }
            3 => {
                return v___x_4164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_partition___redArg(
    mut v_cmp_4169_: *mut crate::leanh::LeanObject,
    mut v_f_4170_: *mut crate::leanh::LeanObject,
    mut v_t_4171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4172_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeMap_Raw_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4172_, 0, v_f_4170_);
                crate::leanh::lean_closure_set(v___f_4172_, 1, v_cmp_4169_);
                v___x_4173_ = l_Std_TreeMap_Raw_partition___redArg___closed__0;
                v_p_4174_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4172_,
                    v___x_4173_,
                    v_t_4171_,
                );
                v_fst_4175_ = crate::leanh::lean_ctor_get(v_p_4174_, 0);
                v_snd_4176_ = crate::leanh::lean_ctor_get(v_p_4174_, 1);
                v_isSharedCheck_4183_ = (!crate::leanh::lean_is_exclusive(v_p_4174_)) as u8;
                if v_isSharedCheck_4183_ == 0 {
                    v___x_4178_ = v_p_4174_;
                    v_isShared_4179_ = v_isSharedCheck_4183_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4176_);
                    crate::leanh::lean_inc(v_fst_4175_);
                    crate::leanh::lean_dec(v_p_4174_);
                    v___x_4178_ = crate::leanh::lean_box(0);
                    v_isShared_4179_ = v_isSharedCheck_4183_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4179_ == 0 {
                    v___x_4181_ = v___x_4178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_fst_4175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_snd_4176_);
                    v___x_4181_ = v_reuseFailAlloc_4182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_partition(
    mut v_00_u03b1_4184_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4185_: *mut crate::leanh::LeanObject,
    mut v_cmp_4186_: *mut crate::leanh::LeanObject,
    mut v_f_4187_: *mut crate::leanh::LeanObject,
    mut v_t_4188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4196_: u8 = 0;
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4189_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeMap_Raw_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4189_, 0, v_f_4187_);
                crate::leanh::lean_closure_set(v___f_4189_, 1, v_cmp_4186_);
                v___x_4190_ = l_Std_TreeMap_Raw_partition___redArg___closed__0;
                v_p_4191_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4189_,
                    v___x_4190_,
                    v_t_4188_,
                );
                v_fst_4192_ = crate::leanh::lean_ctor_get(v_p_4191_, 0);
                v_snd_4193_ = crate::leanh::lean_ctor_get(v_p_4191_, 1);
                v_isSharedCheck_4200_ = (!crate::leanh::lean_is_exclusive(v_p_4191_)) as u8;
                if v_isSharedCheck_4200_ == 0 {
                    v___x_4195_ = v_p_4191_;
                    v_isShared_4196_ = v_isSharedCheck_4200_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4193_);
                    crate::leanh::lean_inc(v_fst_4192_);
                    crate::leanh::lean_dec(v_p_4191_);
                    v___x_4195_ = crate::leanh::lean_box(0);
                    v_isShared_4196_ = v_isSharedCheck_4200_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4196_ == 0 {
                    v___x_4198_ = v___x_4195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4199_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_fst_4192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4199_, 1, v_snd_4193_);
                    v___x_4198_ = v_reuseFailAlloc_4199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_forM___redArg___lam__0(
    mut v_f_4201_: *mut crate::leanh::LeanObject,
    mut v_x_4202_: *mut crate::leanh::LeanObject,
    mut v_k_4203_: *mut crate::leanh::LeanObject,
    mut v_v_4204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4205_ = crate::leanh::lean_apply_2(v_f_4201_, v_k_4203_, v_v_4204_);
    return v___x_4205_;
}
pub unsafe fn l_Std_TreeMap_Raw_forM___redArg(
    mut v_inst_4206_: *mut crate::leanh::LeanObject,
    mut v_f_4207_: *mut crate::leanh::LeanObject,
    mut v_t_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4209_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4209_, 0, v_f_4207_);
    v___x_4210_ = crate::leanh::lean_box(0);
    v___x_4211_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4206_,
        v___f_4209_,
        v___x_4210_,
        v_t_4208_,
    );
    return v___x_4211_;
}
pub unsafe fn l_Std_TreeMap_Raw_forM(
    mut v_00_u03b1_4212_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4213_: *mut crate::leanh::LeanObject,
    mut v_cmp_4214_: *mut crate::leanh::LeanObject,
    mut v_m_4215_: *mut crate::leanh::LeanObject,
    mut v_inst_4216_: *mut crate::leanh::LeanObject,
    mut v_f_4217_: *mut crate::leanh::LeanObject,
    mut v_t_4218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4219_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4219_, 0, v_f_4217_);
    v___x_4220_ = crate::leanh::lean_box(0);
    v___x_4221_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4216_,
        v___f_4219_,
        v___x_4220_,
        v_t_4218_,
    );
    return v___x_4221_;
}
pub unsafe fn l_Std_TreeMap_Raw_forM___boxed(
    mut v_00_u03b1_4222_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4223_: *mut crate::leanh::LeanObject,
    mut v_cmp_4224_: *mut crate::leanh::LeanObject,
    mut v_m_4225_: *mut crate::leanh::LeanObject,
    mut v_inst_4226_: *mut crate::leanh::LeanObject,
    mut v_f_4227_: *mut crate::leanh::LeanObject,
    mut v_t_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Std_TreeMap_Raw_forM(
        v_00_u03b1_4222_,
        v_00_u03b2_4223_,
        v_cmp_4224_,
        v_m_4225_,
        v_inst_4226_,
        v_f_4227_,
        v_t_4228_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4224_);
    return v_res_4229_;
}
pub unsafe fn l_Std_TreeMap_Raw_forIn___redArg___lam__0(
    mut v_f_4230_: *mut crate::leanh::LeanObject,
    mut v_a_4231_: *mut crate::leanh::LeanObject,
    mut v_b_4232_: *mut crate::leanh::LeanObject,
    mut v_c_4233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4234_ = crate::leanh::lean_apply_3(v_f_4230_, v_a_4231_, v_b_4232_, v_c_4233_);
    return v___x_4234_;
}
pub unsafe fn l_Std_TreeMap_Raw_forIn___redArg___lam__1(
    mut v_toPure_4235_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_4237_ = crate::leanh::lean_ctor_get(v_____do__lift_4236_, 0);
    crate::leanh::lean_inc(v_a_4237_);
    crate::leanh::lean_dec_ref(v_____do__lift_4236_);
    v___x_4238_ = crate::leanh::lean_apply_2(v_toPure_4235_, crate::leanh::lean_box(0), v_a_4237_);
    return v___x_4238_;
}
pub unsafe fn l_Std_TreeMap_Raw_forIn___redArg(
    mut v_inst_4239_: *mut crate::leanh::LeanObject,
    mut v_f_4240_: *mut crate::leanh::LeanObject,
    mut v_init_4241_: *mut crate::leanh::LeanObject,
    mut v_t_4242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4243_ = crate::leanh::lean_ctor_get(v_inst_4239_, 0);
    v_toBind_4244_ = crate::leanh::lean_ctor_get(v_inst_4239_, 1);
    crate::leanh::lean_inc(v_toBind_4244_);
    v_toPure_4245_ = crate::leanh::lean_ctor_get(v_toApplicative_4243_, 1);
    crate::leanh::lean_inc(v_toPure_4245_);
    v___f_4246_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4246_, 0, v_f_4240_);
    v___x_4247_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4239_,
        v___f_4246_,
        v_init_4241_,
        v_t_4242_,
    );
    v___f_4248_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4248_, 0, v_toPure_4245_);
    v___x_4249_ = crate::leanh::lean_apply_4(
        v_toBind_4244_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4247_,
        v___f_4248_,
    );
    return v___x_4249_;
}
pub unsafe fn l_Std_TreeMap_Raw_forIn(
    mut v_00_u03b1_4250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4251_: *mut crate::leanh::LeanObject,
    mut v_cmp_4252_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4253_: *mut crate::leanh::LeanObject,
    mut v_m_4254_: *mut crate::leanh::LeanObject,
    mut v_inst_4255_: *mut crate::leanh::LeanObject,
    mut v_f_4256_: *mut crate::leanh::LeanObject,
    mut v_init_4257_: *mut crate::leanh::LeanObject,
    mut v_t_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4259_ = crate::leanh::lean_ctor_get(v_inst_4255_, 0);
    v_toBind_4260_ = crate::leanh::lean_ctor_get(v_inst_4255_, 1);
    crate::leanh::lean_inc(v_toBind_4260_);
    v_toPure_4261_ = crate::leanh::lean_ctor_get(v_toApplicative_4259_, 1);
    crate::leanh::lean_inc(v_toPure_4261_);
    v___f_4262_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4262_, 0, v_f_4256_);
    v___x_4263_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4255_,
        v___f_4262_,
        v_init_4257_,
        v_t_4258_,
    );
    v___f_4264_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4264_, 0, v_toPure_4261_);
    v___x_4265_ = crate::leanh::lean_apply_4(
        v_toBind_4260_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4263_,
        v___f_4264_,
    );
    return v___x_4265_;
}
pub unsafe fn l_Std_TreeMap_Raw_forIn___boxed(
    mut v_00_u03b1_4266_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4267_: *mut crate::leanh::LeanObject,
    mut v_cmp_4268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4269_: *mut crate::leanh::LeanObject,
    mut v_m_4270_: *mut crate::leanh::LeanObject,
    mut v_inst_4271_: *mut crate::leanh::LeanObject,
    mut v_f_4272_: *mut crate::leanh::LeanObject,
    mut v_init_4273_: *mut crate::leanh::LeanObject,
    mut v_t_4274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4275_ = l_Std_TreeMap_Raw_forIn(
        v_00_u03b1_4266_,
        v_00_u03b2_4267_,
        v_cmp_4268_,
        v_00_u03b4_4269_,
        v_m_4270_,
        v_inst_4271_,
        v_f_4272_,
        v_init_4273_,
        v_t_4274_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4268_);
    return v_res_4275_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0(
    mut v_f_4276_: *mut crate::leanh::LeanObject,
    mut v_x_4277_: *mut crate::leanh::LeanObject,
    mut v_k_4278_: *mut crate::leanh::LeanObject,
    mut v_v_4279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4280_, 0, v_k_4278_);
    crate::leanh::lean_ctor_set(v___x_4280_, 1, v_v_4279_);
    v___x_4281_ = crate::leanh::lean_apply_1(v_f_4276_, v___x_4280_);
    return v___x_4281_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1(
    mut v_inst_4282_: *mut crate::leanh::LeanObject,
    mut v_t_4283_: *mut crate::leanh::LeanObject,
    mut v_f_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4285_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4285_, 0, v_f_4284_);
    v___x_4286_ = crate::leanh::lean_box(0);
    v___x_4287_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_4282_,
        v___f_4285_,
        v___x_4286_,
        v_t_4283_,
    );
    return v___x_4287_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForMProdOfMonad___redArg(
    mut v_inst_4288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4289_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4289_, 0, v_inst_4288_);
    return v___f_4289_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForMProdOfMonad(
    mut v_00_u03b1_4290_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4291_: *mut crate::leanh::LeanObject,
    mut v_cmp_4292_: *mut crate::leanh::LeanObject,
    mut v_m_4293_: *mut crate::leanh::LeanObject,
    mut v_inst_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4295_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4295_, 0, v_inst_4294_);
    return v___f_4295_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForMProdOfMonad___boxed(
    mut v_00_u03b1_4296_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4297_: *mut crate::leanh::LeanObject,
    mut v_cmp_4298_: *mut crate::leanh::LeanObject,
    mut v_m_4299_: *mut crate::leanh::LeanObject,
    mut v_inst_4300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4301_ = l_Std_TreeMap_Raw_instForMProdOfMonad(
        v_00_u03b1_4296_,
        v_00_u03b2_4297_,
        v_cmp_4298_,
        v_m_4299_,
        v_inst_4300_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4298_);
    return v_res_4301_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0(
    mut v_f_4302_: *mut crate::leanh::LeanObject,
    mut v_a_4303_: *mut crate::leanh::LeanObject,
    mut v_b_4304_: *mut crate::leanh::LeanObject,
    mut v_c_4305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4306_, 0, v_a_4303_);
    crate::leanh::lean_ctor_set(v___x_4306_, 1, v_b_4304_);
    v___x_4307_ = crate::leanh::lean_apply_2(v_f_4302_, v___x_4306_, v_c_4305_);
    return v___x_4307_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2(
    mut v_inst_4308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4309_: *mut crate::leanh::LeanObject,
    mut v_t_4310_: *mut crate::leanh::LeanObject,
    mut v_init_4311_: *mut crate::leanh::LeanObject,
    mut v_f_4312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4313_ = crate::leanh::lean_ctor_get(v_inst_4308_, 0);
    v_toBind_4314_ = crate::leanh::lean_ctor_get(v_inst_4308_, 1);
    crate::leanh::lean_inc(v_toBind_4314_);
    v_toPure_4315_ = crate::leanh::lean_ctor_get(v_toApplicative_4313_, 1);
    crate::leanh::lean_inc(v_toPure_4315_);
    v___f_4316_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4316_, 0, v_f_4312_);
    v___x_4317_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_4308_,
        v___f_4316_,
        v_init_4311_,
        v_t_4310_,
    );
    v___f_4318_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4318_, 0, v_toPure_4315_);
    v___x_4319_ = crate::leanh::lean_apply_4(
        v_toBind_4314_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4317_,
        v___f_4318_,
    );
    return v___x_4319_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForInProdOfMonad___redArg(
    mut v_inst_4320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4321_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4321_, 0, v_inst_4320_);
    return v___f_4321_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForInProdOfMonad(
    mut v_00_u03b1_4322_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4323_: *mut crate::leanh::LeanObject,
    mut v_cmp_4324_: *mut crate::leanh::LeanObject,
    mut v_m_4325_: *mut crate::leanh::LeanObject,
    mut v_inst_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4327_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4327_, 0, v_inst_4326_);
    return v___f_4327_;
}
pub unsafe fn l_Std_TreeMap_Raw_instForInProdOfMonad___boxed(
    mut v_00_u03b1_4328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4329_: *mut crate::leanh::LeanObject,
    mut v_cmp_4330_: *mut crate::leanh::LeanObject,
    mut v_m_4331_: *mut crate::leanh::LeanObject,
    mut v_inst_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4333_ = l_Std_TreeMap_Raw_instForInProdOfMonad(
        v_00_u03b1_4328_,
        v_00_u03b2_4329_,
        v_cmp_4330_,
        v_m_4331_,
        v_inst_4332_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4330_);
    return v_res_4333_;
}
pub unsafe fn l_Std_TreeMap_Raw_any___redArg___lam__0(
    mut v_p_4334_: *mut crate::leanh::LeanObject,
    mut v___x_4335_: *mut crate::leanh::LeanObject,
    mut v___x_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_b_4338_: *mut crate::leanh::LeanObject,
    mut v_acc_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: u8 = 0;
    v___x_4340_ = crate::leanh::lean_apply_2(v_p_4334_, v_a_4337_, v_b_4338_);
    v___x_4341_ = (crate::leanh::lean_unbox(v___x_4340_) as u8);
    if v___x_4341_ == 0 {
        let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4342_, 0, v___x_4335_);
        return v___x_4342_;
    } else {
        let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_4335_);
        v___x_4343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4343_, 0, v___x_4340_);
        v___x_4344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4344_, 0, v___x_4343_);
        crate::leanh::lean_ctor_set(v___x_4344_, 1, v___x_4336_);
        v___x_4345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4345_, 0, v___x_4344_);
        return v___x_4345_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_any___redArg___lam__0___boxed(
    mut v_p_4346_: *mut crate::leanh::LeanObject,
    mut v___x_4347_: *mut crate::leanh::LeanObject,
    mut v___x_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_b_4350_: *mut crate::leanh::LeanObject,
    mut v_acc_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4352_ = l_Std_TreeMap_Raw_any___redArg___lam__0(
        v_p_4346_,
        v___x_4347_,
        v___x_4348_,
        v_a_4349_,
        v_b_4350_,
        v_acc_4351_,
    );
    crate::leanh::lean_dec_ref(v_acc_4351_);
    return v_res_4352_;
}
pub unsafe fn l_Std_TreeMap_Raw_any___redArg(
    mut v_t_4356_: *mut crate::leanh::LeanObject,
    mut v_p_4357_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: u8 = 0;
    let mut v_val_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4364_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
                v___x_4365_ = crate::leanh::lean_box(0);
                v___x_4366_ = l_Std_TreeMap_Raw_any___redArg___closed__0;
                v___f_4367_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4367_, 0, v_p_4357_);
                crate::leanh::lean_closure_set(v___f_4367_, 1, v___x_4366_);
                crate::leanh::lean_closure_set(v___f_4367_, 2, v___x_4365_);
                v___x_4368_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4364_,
                    v___f_4367_,
                    v___x_4366_,
                    v_t_4356_,
                );
                v_a_4369_ = crate::leanh::lean_ctor_get(v___x_4368_, 0);
                crate::leanh::lean_inc(v_a_4369_);
                crate::leanh::lean_dec(v___x_4368_);
                v___y_4359_ = v_a_4369_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4360_ = crate::leanh::lean_ctor_get(v___y_4359_, 0);
                crate::leanh::lean_inc(v_fst_4360_);
                crate::leanh::lean_dec_ref(v___y_4359_);
                if crate::leanh::lean_obj_tag(v_fst_4360_) == 0 {
                    v___x_4361_ = 0;
                    return v___x_4361_;
                } else {
                    v_val_4362_ = crate::leanh::lean_ctor_get(v_fst_4360_, 0);
                    crate::leanh::lean_inc(v_val_4362_);
                    crate::leanh::lean_dec_ref_known(v_fst_4360_, 1);
                    v___x_4363_ = (crate::leanh::lean_unbox(v_val_4362_) as u8);
                    crate::leanh::lean_dec(v_val_4362_);
                    return v___x_4363_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_any___redArg___boxed(
    mut v_t_4370_: *mut crate::leanh::LeanObject,
    mut v_p_4371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4372_: u8 = 0;
    let mut v_r_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4372_ = l_Std_TreeMap_Raw_any___redArg(v_t_4370_, v_p_4371_);
    v_r_4373_ = crate::leanh::lean_box((v_res_4372_) as usize);
    return v_r_4373_;
}
pub unsafe fn l_Std_TreeMap_Raw_any(
    mut v_00_u03b1_4374_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4375_: *mut crate::leanh::LeanObject,
    mut v_cmp_4376_: *mut crate::leanh::LeanObject,
    mut v_t_4377_: *mut crate::leanh::LeanObject,
    mut v_p_4378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: u8 = 0;
    let mut v_val_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4385_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
                v___x_4386_ = crate::leanh::lean_box(0);
                v___x_4387_ = l_Std_TreeMap_Raw_any___redArg___closed__0;
                v___f_4388_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4388_, 0, v_p_4378_);
                crate::leanh::lean_closure_set(v___f_4388_, 1, v___x_4387_);
                crate::leanh::lean_closure_set(v___f_4388_, 2, v___x_4386_);
                v___x_4389_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4385_,
                    v___f_4388_,
                    v___x_4387_,
                    v_t_4377_,
                );
                v_a_4390_ = crate::leanh::lean_ctor_get(v___x_4389_, 0);
                crate::leanh::lean_inc(v_a_4390_);
                crate::leanh::lean_dec(v___x_4389_);
                v___y_4380_ = v_a_4390_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4381_ = crate::leanh::lean_ctor_get(v___y_4380_, 0);
                crate::leanh::lean_inc(v_fst_4381_);
                crate::leanh::lean_dec_ref(v___y_4380_);
                if crate::leanh::lean_obj_tag(v_fst_4381_) == 0 {
                    v___x_4382_ = 0;
                    return v___x_4382_;
                } else {
                    v_val_4383_ = crate::leanh::lean_ctor_get(v_fst_4381_, 0);
                    crate::leanh::lean_inc(v_val_4383_);
                    crate::leanh::lean_dec_ref_known(v_fst_4381_, 1);
                    v___x_4384_ = (crate::leanh::lean_unbox(v_val_4383_) as u8);
                    crate::leanh::lean_dec(v_val_4383_);
                    return v___x_4384_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_any___boxed(
    mut v_00_u03b1_4391_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4392_: *mut crate::leanh::LeanObject,
    mut v_cmp_4393_: *mut crate::leanh::LeanObject,
    mut v_t_4394_: *mut crate::leanh::LeanObject,
    mut v_p_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4396_: u8 = 0;
    let mut v_r_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4396_ = l_Std_TreeMap_Raw_any(
        v_00_u03b1_4391_,
        v_00_u03b2_4392_,
        v_cmp_4393_,
        v_t_4394_,
        v_p_4395_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4393_);
    v_r_4397_ = crate::leanh::lean_box((v_res_4396_) as usize);
    return v_r_4397_;
}
pub unsafe fn l_Std_TreeMap_Raw_all___redArg___lam__0(
    mut v_p_4398_: *mut crate::leanh::LeanObject,
    mut v___x_4399_: *mut crate::leanh::LeanObject,
    mut v___x_4400_: *mut crate::leanh::LeanObject,
    mut v_a_4401_: *mut crate::leanh::LeanObject,
    mut v_b_4402_: *mut crate::leanh::LeanObject,
    mut v_acc_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: u8 = 0;
    v___x_4404_ = crate::leanh::lean_apply_2(v_p_4398_, v_a_4401_, v_b_4402_);
    v___x_4405_ = (crate::leanh::lean_unbox(v___x_4404_) as u8);
    if v___x_4405_ == 0 {
        let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_4400_);
        v___x_4406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4406_, 0, v___x_4404_);
        v___x_4407_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4407_, 0, v___x_4406_);
        crate::leanh::lean_ctor_set(v___x_4407_, 1, v___x_4399_);
        v___x_4408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4407_);
        return v___x_4408_;
    } else {
        let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4409_, 0, v___x_4400_);
        return v___x_4409_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_all___redArg___lam__0___boxed(
    mut v_p_4410_: *mut crate::leanh::LeanObject,
    mut v___x_4411_: *mut crate::leanh::LeanObject,
    mut v___x_4412_: *mut crate::leanh::LeanObject,
    mut v_a_4413_: *mut crate::leanh::LeanObject,
    mut v_b_4414_: *mut crate::leanh::LeanObject,
    mut v_acc_4415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4416_ = l_Std_TreeMap_Raw_all___redArg___lam__0(
        v_p_4410_,
        v___x_4411_,
        v___x_4412_,
        v_a_4413_,
        v_b_4414_,
        v_acc_4415_,
    );
    crate::leanh::lean_dec_ref(v_acc_4415_);
    return v_res_4416_;
}
pub unsafe fn l_Std_TreeMap_Raw_all___redArg(
    mut v_t_4417_: *mut crate::leanh::LeanObject,
    mut v_p_4418_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    let mut v_val_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: u8 = 0;
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4425_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
                v___x_4426_ = crate::leanh::lean_box(0);
                v___x_4427_ = l_Std_TreeMap_Raw_any___redArg___closed__0;
                v___f_4428_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4428_, 0, v_p_4418_);
                crate::leanh::lean_closure_set(v___f_4428_, 1, v___x_4426_);
                crate::leanh::lean_closure_set(v___f_4428_, 2, v___x_4427_);
                v___x_4429_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4425_,
                    v___f_4428_,
                    v___x_4427_,
                    v_t_4417_,
                );
                v_a_4430_ = crate::leanh::lean_ctor_get(v___x_4429_, 0);
                crate::leanh::lean_inc(v_a_4430_);
                crate::leanh::lean_dec(v___x_4429_);
                v___y_4420_ = v_a_4430_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4421_ = crate::leanh::lean_ctor_get(v___y_4420_, 0);
                crate::leanh::lean_inc(v_fst_4421_);
                crate::leanh::lean_dec_ref(v___y_4420_);
                if crate::leanh::lean_obj_tag(v_fst_4421_) == 0 {
                    v___x_4422_ = 1;
                    return v___x_4422_;
                } else {
                    v_val_4423_ = crate::leanh::lean_ctor_get(v_fst_4421_, 0);
                    crate::leanh::lean_inc(v_val_4423_);
                    crate::leanh::lean_dec_ref_known(v_fst_4421_, 1);
                    v___x_4424_ = (crate::leanh::lean_unbox(v_val_4423_) as u8);
                    crate::leanh::lean_dec(v_val_4423_);
                    return v___x_4424_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_all___redArg___boxed(
    mut v_t_4431_: *mut crate::leanh::LeanObject,
    mut v_p_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4433_: u8 = 0;
    let mut v_r_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4433_ = l_Std_TreeMap_Raw_all___redArg(v_t_4431_, v_p_4432_);
    v_r_4434_ = crate::leanh::lean_box((v_res_4433_) as usize);
    return v_r_4434_;
}
pub unsafe fn l_Std_TreeMap_Raw_all(
    mut v_00_u03b1_4435_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4436_: *mut crate::leanh::LeanObject,
    mut v_cmp_4437_: *mut crate::leanh::LeanObject,
    mut v_t_4438_: *mut crate::leanh::LeanObject,
    mut v_p_4439_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: u8 = 0;
    let mut v_val_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4446_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
                v___x_4447_ = crate::leanh::lean_box(0);
                v___x_4448_ = l_Std_TreeMap_Raw_any___redArg___closed__0;
                v___f_4449_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4449_, 0, v_p_4439_);
                crate::leanh::lean_closure_set(v___f_4449_, 1, v___x_4447_);
                crate::leanh::lean_closure_set(v___f_4449_, 2, v___x_4448_);
                v___x_4450_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_4446_,
                    v___f_4449_,
                    v___x_4448_,
                    v_t_4438_,
                );
                v_a_4451_ = crate::leanh::lean_ctor_get(v___x_4450_, 0);
                crate::leanh::lean_inc(v_a_4451_);
                crate::leanh::lean_dec(v___x_4450_);
                v___y_4441_ = v_a_4451_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4442_ = crate::leanh::lean_ctor_get(v___y_4441_, 0);
                crate::leanh::lean_inc(v_fst_4442_);
                crate::leanh::lean_dec_ref(v___y_4441_);
                if crate::leanh::lean_obj_tag(v_fst_4442_) == 0 {
                    v___x_4443_ = 1;
                    return v___x_4443_;
                } else {
                    v_val_4444_ = crate::leanh::lean_ctor_get(v_fst_4442_, 0);
                    crate::leanh::lean_inc(v_val_4444_);
                    crate::leanh::lean_dec_ref_known(v_fst_4442_, 1);
                    v___x_4445_ = (crate::leanh::lean_unbox(v_val_4444_) as u8);
                    crate::leanh::lean_dec(v_val_4444_);
                    return v___x_4445_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_all___boxed(
    mut v_00_u03b1_4452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4453_: *mut crate::leanh::LeanObject,
    mut v_cmp_4454_: *mut crate::leanh::LeanObject,
    mut v_t_4455_: *mut crate::leanh::LeanObject,
    mut v_p_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4457_: u8 = 0;
    let mut v_r_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_Std_TreeMap_Raw_all(
        v_00_u03b1_4452_,
        v_00_u03b2_4453_,
        v_cmp_4454_,
        v_t_4455_,
        v_p_4456_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4454_);
    v_r_4458_ = crate::leanh::lean_box((v_res_4457_) as usize);
    return v_r_4458_;
}
pub unsafe fn l_Std_TreeMap_Raw_keys___redArg___lam__0(
    mut v_x1_4459_: *mut crate::leanh::LeanObject,
    mut v_x2_4460_: *mut crate::leanh::LeanObject,
    mut v_x3_4461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4462_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4462_, 0, v_x1_4459_);
    crate::leanh::lean_ctor_set(v___x_4462_, 1, v_x3_4461_);
    return v___x_4462_;
}
pub unsafe fn l_Std_TreeMap_Raw_keys___redArg___lam__0___boxed(
    mut v_x1_4463_: *mut crate::leanh::LeanObject,
    mut v_x2_4464_: *mut crate::leanh::LeanObject,
    mut v_x3_4465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4466_ = l_Std_TreeMap_Raw_keys___redArg___lam__0(v_x1_4463_, v_x2_4464_, v_x3_4465_);
    crate::leanh::lean_dec(v_x2_4464_);
    return v_res_4466_;
}
pub unsafe fn l_Std_TreeMap_Raw_keys___redArg(
    mut v_t_4468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4469_ = l_Std_TreeMap_Raw_keys___redArg___closed__0;
    v___x_4470_ = crate::leanh::lean_box(0);
    v___x_4471_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4472_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4471_,
        v___f_4469_,
        v___x_4470_,
        v_t_4468_,
    );
    return v___x_4472_;
}
pub unsafe fn l_Std_TreeMap_Raw_keys(
    mut v_00_u03b1_4473_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4474_: *mut crate::leanh::LeanObject,
    mut v_cmp_4475_: *mut crate::leanh::LeanObject,
    mut v_t_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4477_ = l_Std_TreeMap_Raw_keys___redArg___closed__0;
    v___x_4478_ = crate::leanh::lean_box(0);
    v___x_4479_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4480_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4479_,
        v___f_4477_,
        v___x_4478_,
        v_t_4476_,
    );
    return v___x_4480_;
}
pub unsafe fn l_Std_TreeMap_Raw_keys___boxed(
    mut v_00_u03b1_4481_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4482_: *mut crate::leanh::LeanObject,
    mut v_cmp_4483_: *mut crate::leanh::LeanObject,
    mut v_t_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4485_ =
        l_Std_TreeMap_Raw_keys(v_00_u03b1_4481_, v_00_u03b2_4482_, v_cmp_4483_, v_t_4484_);
    crate::leanh::lean_dec_ref(v_cmp_4483_);
    return v_res_4485_;
}
pub unsafe fn l_Std_TreeMap_Raw_keysArray___redArg___lam__0(
    mut v_l_4486_: *mut crate::leanh::LeanObject,
    mut v_k_4487_: *mut crate::leanh::LeanObject,
    mut v_x_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4489_ = lean_array_push(v_l_4486_, v_k_4487_);
    return v___x_4489_;
}
pub unsafe fn l_Std_TreeMap_Raw_keysArray___redArg___lam__0___boxed(
    mut v_l_4490_: *mut crate::leanh::LeanObject,
    mut v_k_4491_: *mut crate::leanh::LeanObject,
    mut v_x_4492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4493_ = l_Std_TreeMap_Raw_keysArray___redArg___lam__0(v_l_4490_, v_k_4491_, v_x_4492_);
    crate::leanh::lean_dec(v_x_4492_);
    return v_res_4493_;
}
pub unsafe fn l_Std_TreeMap_Raw_keysArray___redArg(
    mut v_t_4495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4496_ = l_Std_TreeMap_Raw_keysArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_4495_) == 0 {
                    v_size_4501_ = crate::leanh::lean_ctor_get(v_t_4495_, 0);
                    crate::leanh::lean_inc(v_size_4501_);
                    v___y_4498_ = v_size_4501_;
                    state = 1;
                    continue;
                } else {
                    v___x_4502_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4498_ = v___x_4502_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4499_ = lean_mk_empty_array_with_capacity(v___y_4498_);
                crate::leanh::lean_dec(v___y_4498_);
                v___x_4500_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4496_,
                    v___x_4499_,
                    v_t_4495_,
                );
                return v___x_4500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_keysArray(
    mut v_00_u03b1_4503_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4504_: *mut crate::leanh::LeanObject,
    mut v_cmp_4505_: *mut crate::leanh::LeanObject,
    mut v_t_4506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4507_ = l_Std_TreeMap_Raw_keysArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_4506_) == 0 {
                    v_size_4512_ = crate::leanh::lean_ctor_get(v_t_4506_, 0);
                    crate::leanh::lean_inc(v_size_4512_);
                    v___y_4509_ = v_size_4512_;
                    state = 1;
                    continue;
                } else {
                    v___x_4513_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4509_ = v___x_4513_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4510_ = lean_mk_empty_array_with_capacity(v___y_4509_);
                crate::leanh::lean_dec(v___y_4509_);
                v___x_4511_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4507_,
                    v___x_4510_,
                    v_t_4506_,
                );
                return v___x_4511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_keysArray___boxed(
    mut v_00_u03b1_4514_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4515_: *mut crate::leanh::LeanObject,
    mut v_cmp_4516_: *mut crate::leanh::LeanObject,
    mut v_t_4517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4518_ =
        l_Std_TreeMap_Raw_keysArray(v_00_u03b1_4514_, v_00_u03b2_4515_, v_cmp_4516_, v_t_4517_);
    crate::leanh::lean_dec_ref(v_cmp_4516_);
    return v_res_4518_;
}
pub unsafe fn l_Std_TreeMap_Raw_values___redArg___lam__0(
    mut v_x1_4519_: *mut crate::leanh::LeanObject,
    mut v_x2_4520_: *mut crate::leanh::LeanObject,
    mut v_x3_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4522_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4522_, 0, v_x2_4520_);
    crate::leanh::lean_ctor_set(v___x_4522_, 1, v_x3_4521_);
    return v___x_4522_;
}
pub unsafe fn l_Std_TreeMap_Raw_values___redArg___lam__0___boxed(
    mut v_x1_4523_: *mut crate::leanh::LeanObject,
    mut v_x2_4524_: *mut crate::leanh::LeanObject,
    mut v_x3_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4526_ = l_Std_TreeMap_Raw_values___redArg___lam__0(v_x1_4523_, v_x2_4524_, v_x3_4525_);
    crate::leanh::lean_dec(v_x1_4523_);
    return v_res_4526_;
}
pub unsafe fn l_Std_TreeMap_Raw_values___redArg(
    mut v_t_4528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4529_ = l_Std_TreeMap_Raw_values___redArg___closed__0;
    v___x_4530_ = crate::leanh::lean_box(0);
    v___x_4531_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4532_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4531_,
        v___f_4529_,
        v___x_4530_,
        v_t_4528_,
    );
    return v___x_4532_;
}
pub unsafe fn l_Std_TreeMap_Raw_values(
    mut v_00_u03b1_4533_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4534_: *mut crate::leanh::LeanObject,
    mut v_cmp_4535_: *mut crate::leanh::LeanObject,
    mut v_t_4536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4537_ = l_Std_TreeMap_Raw_values___redArg___closed__0;
    v___x_4538_ = crate::leanh::lean_box(0);
    v___x_4539_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4540_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4539_,
        v___f_4537_,
        v___x_4538_,
        v_t_4536_,
    );
    return v___x_4540_;
}
pub unsafe fn l_Std_TreeMap_Raw_values___boxed(
    mut v_00_u03b1_4541_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4542_: *mut crate::leanh::LeanObject,
    mut v_cmp_4543_: *mut crate::leanh::LeanObject,
    mut v_t_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4545_ =
        l_Std_TreeMap_Raw_values(v_00_u03b1_4541_, v_00_u03b2_4542_, v_cmp_4543_, v_t_4544_);
    crate::leanh::lean_dec_ref(v_cmp_4543_);
    return v_res_4545_;
}
pub unsafe fn l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(
    mut v_l_4546_: *mut crate::leanh::LeanObject,
    mut v_x_4547_: *mut crate::leanh::LeanObject,
    mut v_v_4548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4549_ = lean_array_push(v_l_4546_, v_v_4548_);
    return v___x_4549_;
}
pub unsafe fn l_Std_TreeMap_Raw_valuesArray___redArg___lam__0___boxed(
    mut v_l_4550_: *mut crate::leanh::LeanObject,
    mut v_x_4551_: *mut crate::leanh::LeanObject,
    mut v_v_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4553_ = l_Std_TreeMap_Raw_valuesArray___redArg___lam__0(v_l_4550_, v_x_4551_, v_v_4552_);
    crate::leanh::lean_dec(v_x_4551_);
    return v_res_4553_;
}
pub unsafe fn l_Std_TreeMap_Raw_valuesArray___redArg(
    mut v_t_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4556_ = l_Std_TreeMap_Raw_valuesArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_4555_) == 0 {
                    v_size_4561_ = crate::leanh::lean_ctor_get(v_t_4555_, 0);
                    crate::leanh::lean_inc(v_size_4561_);
                    v___y_4558_ = v_size_4561_;
                    state = 1;
                    continue;
                } else {
                    v___x_4562_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4558_ = v___x_4562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4559_ = lean_mk_empty_array_with_capacity(v___y_4558_);
                crate::leanh::lean_dec(v___y_4558_);
                v___x_4560_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4556_,
                    v___x_4559_,
                    v_t_4555_,
                );
                return v___x_4560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_valuesArray(
    mut v_00_u03b1_4563_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4564_: *mut crate::leanh::LeanObject,
    mut v_cmp_4565_: *mut crate::leanh::LeanObject,
    mut v_t_4566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4567_ = l_Std_TreeMap_Raw_valuesArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_4566_) == 0 {
                    v_size_4572_ = crate::leanh::lean_ctor_get(v_t_4566_, 0);
                    crate::leanh::lean_inc(v_size_4572_);
                    v___y_4569_ = v_size_4572_;
                    state = 1;
                    continue;
                } else {
                    v___x_4573_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4569_ = v___x_4573_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4570_ = lean_mk_empty_array_with_capacity(v___y_4569_);
                crate::leanh::lean_dec(v___y_4569_);
                v___x_4571_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4567_,
                    v___x_4570_,
                    v_t_4566_,
                );
                return v___x_4571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_valuesArray___boxed(
    mut v_00_u03b1_4574_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4575_: *mut crate::leanh::LeanObject,
    mut v_cmp_4576_: *mut crate::leanh::LeanObject,
    mut v_t_4577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4578_ =
        l_Std_TreeMap_Raw_valuesArray(v_00_u03b1_4574_, v_00_u03b2_4575_, v_cmp_4576_, v_t_4577_);
    crate::leanh::lean_dec_ref(v_cmp_4576_);
    return v_res_4578_;
}
pub unsafe fn l_Std_TreeMap_Raw_toList___redArg___lam__0(
    mut v_x1_4579_: *mut crate::leanh::LeanObject,
    mut v_x2_4580_: *mut crate::leanh::LeanObject,
    mut v_x3_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4582_, 0, v_x1_4579_);
    crate::leanh::lean_ctor_set(v___x_4582_, 1, v_x2_4580_);
    v___x_4583_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4583_, 0, v___x_4582_);
    crate::leanh::lean_ctor_set(v___x_4583_, 1, v_x3_4581_);
    return v___x_4583_;
}
pub unsafe fn l_Std_TreeMap_Raw_toList___redArg(
    mut v_t_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4586_ = l_Std_TreeMap_Raw_toList___redArg___closed__0;
    v___x_4587_ = crate::leanh::lean_box(0);
    v___x_4588_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4589_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4588_,
        v___f_4586_,
        v___x_4587_,
        v_t_4585_,
    );
    return v___x_4589_;
}
pub unsafe fn l_Std_TreeMap_Raw_toList(
    mut v_00_u03b1_4590_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4591_: *mut crate::leanh::LeanObject,
    mut v_cmp_4592_: *mut crate::leanh::LeanObject,
    mut v_t_4593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4594_ = l_Std_TreeMap_Raw_toList___redArg___closed__0;
    v___x_4595_ = crate::leanh::lean_box(0);
    v___x_4596_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4597_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4596_,
        v___f_4594_,
        v___x_4595_,
        v_t_4593_,
    );
    return v___x_4597_;
}
pub unsafe fn l_Std_TreeMap_Raw_toList___boxed(
    mut v_00_u03b1_4598_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4599_: *mut crate::leanh::LeanObject,
    mut v_cmp_4600_: *mut crate::leanh::LeanObject,
    mut v_t_4601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4602_ =
        l_Std_TreeMap_Raw_toList(v_00_u03b1_4598_, v_00_u03b2_4599_, v_cmp_4600_, v_t_4601_);
    crate::leanh::lean_dec_ref(v_cmp_4600_);
    return v_res_4602_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw_ofList___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4603_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__26,
    );
    return v___x_4603_;
}
pub unsafe fn l_Std_TreeMap_Raw_ofList___redArg___lam__0(
    mut v_cmp_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_x_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4608_ = crate::leanh::lean_ctor_get(v_a_4605_, 0);
    crate::leanh::lean_inc(v_fst_4608_);
    v_snd_4609_ = crate::leanh::lean_ctor_get(v_a_4605_, 1);
    crate::leanh::lean_inc(v_snd_4609_);
    crate::leanh::lean_dec_ref(v_a_4605_);
    v_r_4610_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
        v_cmp_4604_,
        v_fst_4608_,
        v_snd_4609_,
        v___y_4607_,
    );
    v___x_4611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4611_, 0, v_r_4610_);
    return v___x_4611_;
}
pub unsafe fn l_Std_TreeMap_Raw_ofList___redArg(
    mut v_l_4612_: *mut crate::leanh::LeanObject,
    mut v_cmp_4613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4614_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4614_, 0, v_cmp_4613_);
    v___x_4615_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4616_ = crate::leanh::lean_box(1);
    v___x_4617_ = l_List_forIn_x27_loop___redArg(v___x_4615_, v___f_4614_, v_l_4612_, v_r_4616_);
    return v___x_4617_;
}
pub unsafe fn l_Std_TreeMap_Raw_ofList___redArg___boxed(
    mut v_l_4618_: *mut crate::leanh::LeanObject,
    mut v_cmp_4619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4620_ = l_Std_TreeMap_Raw_ofList___redArg(v_l_4618_, v_cmp_4619_);
    crate::leanh::lean_dec(v_l_4618_);
    return v_res_4620_;
}
pub unsafe fn l_Std_TreeMap_Raw_ofList(
    mut v_00_u03b1_4621_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4622_: *mut crate::leanh::LeanObject,
    mut v_l_4623_: *mut crate::leanh::LeanObject,
    mut v_cmp_4624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4625_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4625_, 0, v_cmp_4624_);
    v___x_4626_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4627_ = crate::leanh::lean_box(1);
    v___x_4628_ = l_List_forIn_x27_loop___redArg(v___x_4626_, v___f_4625_, v_l_4623_, v_r_4627_);
    return v___x_4628_;
}
pub unsafe fn l_Std_TreeMap_Raw_ofList___boxed(
    mut v_00_u03b1_4629_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4630_: *mut crate::leanh::LeanObject,
    mut v_l_4631_: *mut crate::leanh::LeanObject,
    mut v_cmp_4632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4633_ =
        l_Std_TreeMap_Raw_ofList(v_00_u03b1_4629_, v_00_u03b2_4630_, v_l_4631_, v_cmp_4632_);
    crate::leanh::lean_dec(v_l_4631_);
    return v_res_4633_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw_unitOfList___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4634_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__26,
    );
    return v___x_4634_;
}
pub unsafe fn l_Std_TreeMap_Raw_unitOfList___redArg___lam__0(
    mut v_cmp_4635_: *mut crate::leanh::LeanObject,
    mut v_a_4636_: *mut crate::leanh::LeanObject,
    mut v_x_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4639_: u8 = 0;
    crate::leanh::lean_inc(v___y_4638_);
    crate::leanh::lean_inc(v_a_4636_);
    crate::leanh::lean_inc_ref(v_cmp_4635_);
    v___x_4639_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4635_, v_a_4636_, v___y_4638_);
    if v___x_4639_ == 0 {
        let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4640_ = crate::leanh::lean_box(0);
        v___x_4641_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_4635_,
            v_a_4636_,
            v___x_4640_,
            v___y_4638_,
        );
        v___x_4642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4642_, 0, v___x_4641_);
        return v___x_4642_;
    } else {
        let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_4636_);
        crate::leanh::lean_dec_ref(v_cmp_4635_);
        v___x_4643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4643_, 0, v___y_4638_);
        return v___x_4643_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_unitOfList___redArg(
    mut v_l_4644_: *mut crate::leanh::LeanObject,
    mut v_cmp_4645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4646_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4646_, 0, v_cmp_4645_);
    v___x_4647_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4648_ = crate::leanh::lean_box(1);
    v___x_4649_ = l_List_forIn_x27_loop___redArg(v___x_4647_, v___f_4646_, v_l_4644_, v_r_4648_);
    return v___x_4649_;
}
pub unsafe fn l_Std_TreeMap_Raw_unitOfList___redArg___boxed(
    mut v_l_4650_: *mut crate::leanh::LeanObject,
    mut v_cmp_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4652_ = l_Std_TreeMap_Raw_unitOfList___redArg(v_l_4650_, v_cmp_4651_);
    crate::leanh::lean_dec(v_l_4650_);
    return v_res_4652_;
}
pub unsafe fn l_Std_TreeMap_Raw_unitOfList(
    mut v_00_u03b1_4653_: *mut crate::leanh::LeanObject,
    mut v_l_4654_: *mut crate::leanh::LeanObject,
    mut v_cmp_4655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4656_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4656_, 0, v_cmp_4655_);
    v___x_4657_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4658_ = crate::leanh::lean_box(1);
    v___x_4659_ = l_List_forIn_x27_loop___redArg(v___x_4657_, v___f_4656_, v_l_4654_, v_r_4658_);
    return v___x_4659_;
}
pub unsafe fn l_Std_TreeMap_Raw_unitOfList___boxed(
    mut v_00_u03b1_4660_: *mut crate::leanh::LeanObject,
    mut v_l_4661_: *mut crate::leanh::LeanObject,
    mut v_cmp_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4663_ = l_Std_TreeMap_Raw_unitOfList(v_00_u03b1_4660_, v_l_4661_, v_cmp_4662_);
    crate::leanh::lean_dec(v_l_4661_);
    return v_res_4663_;
}
pub unsafe fn l_Std_TreeMap_Raw_toArray___redArg___lam__0(
    mut v_l_4664_: *mut crate::leanh::LeanObject,
    mut v_k_4665_: *mut crate::leanh::LeanObject,
    mut v_v_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4667_, 0, v_k_4665_);
    crate::leanh::lean_ctor_set(v___x_4667_, 1, v_v_4666_);
    v___x_4668_ = lean_array_push(v_l_4664_, v___x_4667_);
    return v___x_4668_;
}
pub unsafe fn l_Std_TreeMap_Raw_toArray___redArg(
    mut v_t_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4671_ = l_Std_TreeMap_Raw_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_4670_) == 0 {
                    v_size_4676_ = crate::leanh::lean_ctor_get(v_t_4670_, 0);
                    crate::leanh::lean_inc(v_size_4676_);
                    v___y_4673_ = v_size_4676_;
                    state = 1;
                    continue;
                } else {
                    v___x_4677_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4673_ = v___x_4677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4674_ = lean_mk_empty_array_with_capacity(v___y_4673_);
                crate::leanh::lean_dec(v___y_4673_);
                v___x_4675_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4671_,
                    v___x_4674_,
                    v_t_4670_,
                );
                return v___x_4675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_toArray(
    mut v_00_u03b1_4678_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4679_: *mut crate::leanh::LeanObject,
    mut v_cmp_4680_: *mut crate::leanh::LeanObject,
    mut v_t_4681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4682_ = l_Std_TreeMap_Raw_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_4681_) == 0 {
                    v_size_4687_ = crate::leanh::lean_ctor_get(v_t_4681_, 0);
                    crate::leanh::lean_inc(v_size_4687_);
                    v___y_4684_ = v_size_4687_;
                    state = 1;
                    continue;
                } else {
                    v___x_4688_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4684_ = v___x_4688_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4685_ = lean_mk_empty_array_with_capacity(v___y_4684_);
                crate::leanh::lean_dec(v___y_4684_);
                v___x_4686_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_4682_,
                    v___x_4685_,
                    v_t_4681_,
                );
                return v___x_4686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_toArray___boxed(
    mut v_00_u03b1_4689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4690_: *mut crate::leanh::LeanObject,
    mut v_cmp_4691_: *mut crate::leanh::LeanObject,
    mut v_t_4692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4693_ =
        l_Std_TreeMap_Raw_toArray(v_00_u03b1_4689_, v_00_u03b2_4690_, v_cmp_4691_, v_t_4692_);
    crate::leanh::lean_dec_ref(v_cmp_4691_);
    return v_res_4693_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw_ofArray___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4694_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__26,
    );
    return v___x_4694_;
}
pub unsafe fn l_Std_TreeMap_Raw_ofArray___redArg(
    mut v_a_4695_: *mut crate::leanh::LeanObject,
    mut v_cmp_4696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4700_: usize = 0;
    let mut v___x_4701_: usize = 0;
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4697_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4697_, 0, v_cmp_4696_);
    v___x_4698_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4699_ = crate::leanh::lean_box(1);
    v_sz_4700_ = lean_array_size(v_a_4695_);
    v___x_4701_ = 0usize;
    v___x_4702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4698_,
        v_a_4695_,
        v___f_4697_,
        v_sz_4700_,
        v___x_4701_,
        v_r_4699_,
    );
    return v___x_4702_;
}
pub unsafe fn l_Std_TreeMap_Raw_ofArray(
    mut v_00_u03b1_4703_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4704_: *mut crate::leanh::LeanObject,
    mut v_a_4705_: *mut crate::leanh::LeanObject,
    mut v_cmp_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4710_: usize = 0;
    let mut v___x_4711_: usize = 0;
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4707_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4707_, 0, v_cmp_4706_);
    v___x_4708_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4709_ = crate::leanh::lean_box(1);
    v_sz_4710_ = lean_array_size(v_a_4705_);
    v___x_4711_ = 0usize;
    v___x_4712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4708_,
        v_a_4705_,
        v___f_4707_,
        v_sz_4710_,
        v___x_4711_,
        v_r_4709_,
    );
    return v___x_4712_;
}
pub unsafe fn _init_l_Std_TreeMap_Raw_unitOfArray___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeMap_Raw___auto__1___closed__26,
    );
    return v___x_4713_;
}
pub unsafe fn l_Std_TreeMap_Raw_unitOfArray___redArg(
    mut v_a_4714_: *mut crate::leanh::LeanObject,
    mut v_cmp_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4719_: usize = 0;
    let mut v___x_4720_: usize = 0;
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4716_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4716_, 0, v_cmp_4715_);
    v___x_4717_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4718_ = crate::leanh::lean_box(1);
    v_sz_4719_ = lean_array_size(v_a_4714_);
    v___x_4720_ = 0usize;
    v___x_4721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4717_,
        v_a_4714_,
        v___f_4716_,
        v_sz_4719_,
        v___x_4720_,
        v_r_4718_,
    );
    return v___x_4721_;
}
pub unsafe fn l_Std_TreeMap_Raw_unitOfArray(
    mut v_00_u03b1_4722_: *mut crate::leanh::LeanObject,
    mut v_a_4723_: *mut crate::leanh::LeanObject,
    mut v_cmp_4724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4728_: usize = 0;
    let mut v___x_4729_: usize = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4725_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_unitOfList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4725_, 0, v_cmp_4724_);
    v___x_4726_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v_r_4727_ = crate::leanh::lean_box(1);
    v_sz_4728_ = lean_array_size(v_a_4723_);
    v___x_4729_ = 0usize;
    v___x_4730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4726_,
        v_a_4723_,
        v___f_4725_,
        v_sz_4728_,
        v___x_4729_,
        v_r_4727_,
    );
    return v___x_4730_;
}
pub unsafe fn l_Std_TreeMap_Raw_modify___redArg(
    mut v_cmp_4731_: *mut crate::leanh::LeanObject,
    mut v_t_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
    mut v_f_4734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4735_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_4731_,
        v_a_4733_,
        v_f_4734_,
        v_t_4732_,
    );
    return v___x_4735_;
}
pub unsafe fn l_Std_TreeMap_Raw_modify(
    mut v_00_u03b1_4736_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4737_: *mut crate::leanh::LeanObject,
    mut v_cmp_4738_: *mut crate::leanh::LeanObject,
    mut v_t_4739_: *mut crate::leanh::LeanObject,
    mut v_a_4740_: *mut crate::leanh::LeanObject,
    mut v_f_4741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4742_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(
        v_cmp_4738_,
        v_a_4740_,
        v_f_4741_,
        v_t_4739_,
    );
    return v___x_4742_;
}
pub unsafe fn l_Std_TreeMap_Raw_alter___redArg(
    mut v_cmp_4743_: *mut crate::leanh::LeanObject,
    mut v_t_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_f_4746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4747_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(
        v_cmp_4743_,
        v_a_4745_,
        v_f_4746_,
        v_t_4744_,
    );
    return v___x_4747_;
}
pub unsafe fn l_Std_TreeMap_Raw_alter(
    mut v_00_u03b1_4748_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4749_: *mut crate::leanh::LeanObject,
    mut v_cmp_4750_: *mut crate::leanh::LeanObject,
    mut v_t_4751_: *mut crate::leanh::LeanObject,
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_f_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4754_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(
        v_cmp_4750_,
        v_a_4752_,
        v_f_4753_,
        v_t_4751_,
    );
    return v___x_4754_;
}
pub unsafe fn l_Std_TreeMap_Raw_mergeWith___redArg___lam__0(
    mut v_b_u2082_4755_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_x_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4763_: u8 = 0;
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4758_) == 0 {
                    crate::leanh::lean_dec(v_a_4757_);
                    crate::leanh::lean_dec(v_mergeFn_4756_);
                    v___x_4759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4759_, 0, v_b_u2082_4755_);
                    return v___x_4759_;
                } else {
                    v_val_4760_ = crate::leanh::lean_ctor_get(v_x_4758_, 0);
                    v_isSharedCheck_4768_ = (!crate::leanh::lean_is_exclusive(v_x_4758_)) as u8;
                    if v_isSharedCheck_4768_ == 0 {
                        v___x_4762_ = v_x_4758_;
                        v_isShared_4763_ = v_isSharedCheck_4768_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4760_);
                        crate::leanh::lean_dec(v_x_4758_);
                        v___x_4762_ = crate::leanh::lean_box(0);
                        v_isShared_4763_ = v_isSharedCheck_4768_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4764_ = crate::leanh::lean_apply_3(
                    v_mergeFn_4756_,
                    v_a_4757_,
                    v_val_4760_,
                    v_b_u2082_4755_,
                );
                if v_isShared_4763_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4762_, 0, v___x_4764_);
                    v___x_4766_ = v___x_4762_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4764_);
                    v___x_4766_ = v_reuseFailAlloc_4767_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeMap_Raw_mergeWith___redArg___lam__1(
    mut v_mergeFn_4769_: *mut crate::leanh::LeanObject,
    mut v_cmp_4770_: *mut crate::leanh::LeanObject,
    mut v_t_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_4772_);
    v___f_4774_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_mergeWith___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4774_, 0, v_b_u2082_4773_);
    crate::leanh::lean_closure_set(v___f_4774_, 1, v_mergeFn_4769_);
    crate::leanh::lean_closure_set(v___f_4774_, 2, v_a_4772_);
    v___x_4775_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(
        v_cmp_4770_,
        v_a_4772_,
        v___f_4774_,
        v_t_4771_,
    );
    return v___x_4775_;
}
pub unsafe fn l_Std_TreeMap_Raw_mergeWith___redArg(
    mut v_cmp_4776_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_4777_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4778_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4780_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4780_, 0, v_mergeFn_4777_);
    crate::leanh::lean_closure_set(v___f_4780_, 1, v_cmp_4776_);
    v___x_4781_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_4780_, v_t_u2081_4778_, v_t_u2082_4779_);
    return v___x_4781_;
}
pub unsafe fn l_Std_TreeMap_Raw_mergeWith(
    mut v_00_u03b1_4782_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4783_: *mut crate::leanh::LeanObject,
    mut v_cmp_4784_: *mut crate::leanh::LeanObject,
    mut v_mergeFn_4785_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4786_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4788_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_mergeWith___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4788_, 0, v_mergeFn_4785_);
    crate::leanh::lean_closure_set(v___f_4788_, 1, v_cmp_4784_);
    v___x_4789_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_4788_, v_t_u2081_4786_, v_t_u2082_4787_);
    return v___x_4789_;
}
pub unsafe fn l_Std_TreeMap_Raw_insertMany___redArg___lam__0(
    mut v_cmp_4790_: *mut crate::leanh::LeanObject,
    mut v_x_4791_: *mut crate::leanh::LeanObject,
    mut v_____s_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4793_ = crate::leanh::lean_ctor_get(v_x_4791_, 0);
    crate::leanh::lean_inc(v_fst_4793_);
    v_snd_4794_ = crate::leanh::lean_ctor_get(v_x_4791_, 1);
    crate::leanh::lean_inc(v_snd_4794_);
    crate::leanh::lean_dec_ref(v_x_4791_);
    v_r_4795_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
        v_cmp_4790_,
        v_fst_4793_,
        v_snd_4794_,
        v_____s_4792_,
    );
    v___x_4796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4796_, 0, v_r_4795_);
    return v___x_4796_;
}
pub unsafe fn l_Std_TreeMap_Raw_insertMany___redArg(
    mut v_cmp_4797_: *mut crate::leanh::LeanObject,
    mut v_inst_4798_: *mut crate::leanh::LeanObject,
    mut v_t_4799_: *mut crate::leanh::LeanObject,
    mut v_l_4800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4801_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4801_, 0, v_cmp_4797_);
    v___x_4802_ = crate::leanh::lean_apply_4(
        v_inst_4798_,
        crate::leanh::lean_box(0),
        v_l_4800_,
        v_t_4799_,
        v___f_4801_,
    );
    return v___x_4802_;
}
pub unsafe fn l_Std_TreeMap_Raw_insertMany(
    mut v_00_u03b1_4803_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4804_: *mut crate::leanh::LeanObject,
    mut v_cmp_4805_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4806_: *mut crate::leanh::LeanObject,
    mut v_inst_4807_: *mut crate::leanh::LeanObject,
    mut v_t_4808_: *mut crate::leanh::LeanObject,
    mut v_l_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4810_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4810_, 0, v_cmp_4805_);
    v___x_4811_ = crate::leanh::lean_apply_4(
        v_inst_4807_,
        crate::leanh::lean_box(0),
        v_l_4809_,
        v_t_4808_,
        v___f_4810_,
    );
    return v___x_4811_;
}
pub unsafe fn l_Std_TreeMap_Raw_union___redArg(
    mut v_cmp_4812_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4813_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4815_ =
        l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(
            v_cmp_4812_,
            v_t_u2081_4813_,
            v_t_u2082_4814_,
        );
    return v___x_4815_;
}
pub unsafe fn l_Std_TreeMap_Raw_union(
    mut v_00_u03b1_4816_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4817_: *mut crate::leanh::LeanObject,
    mut v_cmp_4818_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4819_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4821_ =
        l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(
            v_cmp_4818_,
            v_t_u2081_4819_,
            v_t_u2082_4820_,
        );
    return v___x_4821_;
}
pub unsafe fn l_Std_TreeMap_Raw_instUnion___redArg(
    mut v_cmp_4822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeMap_Raw_union as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_4823_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4823_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4823_, 2, v_cmp_4822_);
    return v___x_4823_;
}
pub unsafe fn l_Std_TreeMap_Raw_instUnion(
    mut v_00_u03b1_4824_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4825_: *mut crate::leanh::LeanObject,
    mut v_cmp_4826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4827_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeMap_Raw_union as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_4827_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4827_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4827_, 2, v_cmp_4826_);
    return v___x_4827_;
}
pub unsafe fn l_Std_TreeMap_Raw_inter___redArg(
    mut v_cmp_4828_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4829_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ =
        l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(
            v_cmp_4828_,
            v_t_u2081_4829_,
            v_t_u2082_4830_,
        );
    return v___x_4831_;
}
pub unsafe fn l_Std_TreeMap_Raw_inter(
    mut v_00_u03b1_4832_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4833_: *mut crate::leanh::LeanObject,
    mut v_cmp_4834_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4835_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4837_ =
        l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(
            v_cmp_4834_,
            v_t_u2081_4835_,
            v_t_u2082_4836_,
        );
    return v___x_4837_;
}
pub unsafe fn l_Std_TreeMap_Raw_instInter___redArg(
    mut v_cmp_4838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4839_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeMap_Raw_inter as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_4839_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4839_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4839_, 2, v_cmp_4838_);
    return v___x_4839_;
}
pub unsafe fn l_Std_TreeMap_Raw_instInter(
    mut v_00_u03b1_4840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4841_: *mut crate::leanh::LeanObject,
    mut v_cmp_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4843_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeMap_Raw_inter as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_4843_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4843_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4843_, 2, v_cmp_4842_);
    return v___x_4843_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___redArg(
    mut v_cmp_4844_: *mut crate::leanh::LeanObject,
    mut v_inst_4845_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4846_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4847_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4848_: u8 = 0;
    v___x_4848_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_4844_,
        v_inst_4845_,
        v_t_u2081_4846_,
        v_t_u2082_4847_,
    );
    return v___x_4848_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___redArg___boxed(
    mut v_cmp_4849_: *mut crate::leanh::LeanObject,
    mut v_inst_4850_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4851_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4853_: u8 = 0;
    let mut v_r_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4853_ =
        l_Std_TreeMap_Raw_beq___redArg(v_cmp_4849_, v_inst_4850_, v_t_u2081_4851_, v_t_u2082_4852_);
    v_r_4854_ = crate::leanh::lean_box((v_res_4853_) as usize);
    return v_r_4854_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq(
    mut v_00_u03b1_4855_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4856_: *mut crate::leanh::LeanObject,
    mut v_cmp_4857_: *mut crate::leanh::LeanObject,
    mut v_inst_4858_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4859_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4860_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4861_: u8 = 0;
    v___x_4861_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(
        v_cmp_4857_,
        v_inst_4858_,
        v_t_u2081_4859_,
        v_t_u2082_4860_,
    );
    return v___x_4861_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___boxed(
    mut v_00_u03b1_4862_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4863_: *mut crate::leanh::LeanObject,
    mut v_cmp_4864_: *mut crate::leanh::LeanObject,
    mut v_inst_4865_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4866_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4868_: u8 = 0;
    let mut v_r_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4868_ = l_Std_TreeMap_Raw_beq(
        v_00_u03b1_4862_,
        v_00_u03b2_4863_,
        v_cmp_4864_,
        v_inst_4865_,
        v_t_u2081_4866_,
        v_t_u2082_4867_,
    );
    v_r_4869_ = crate::leanh::lean_box((v_res_4868_) as usize);
    return v_r_4869_;
}
pub unsafe fn l_Std_TreeMap_Raw_instBEq___redArg(
    mut v_cmp_4870_: *mut crate::leanh::LeanObject,
    mut v_inst_4871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4872_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_4872_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4872_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4872_, 2, v_cmp_4870_);
    crate::leanh::lean_closure_set(v___x_4872_, 3, v_inst_4871_);
    return v___x_4872_;
}
pub unsafe fn l_Std_TreeMap_Raw_instBEq(
    mut v_00_u03b1_4873_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4874_: *mut crate::leanh::LeanObject,
    mut v_cmp_4875_: *mut crate::leanh::LeanObject,
    mut v_inst_4876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4877_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_beq___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_4877_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4877_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4877_, 2, v_cmp_4875_);
    crate::leanh::lean_closure_set(v___x_4877_, 3, v_inst_4876_);
    return v___x_4877_;
}
pub unsafe fn l_Std_TreeMap_Raw_diff___redArg(
    mut v_cmp_4878_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4879_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4881_ =
        l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(
            v_cmp_4878_,
            v_t_u2081_4879_,
            v_t_u2082_4880_,
        );
    return v___x_4881_;
}
pub unsafe fn l_Std_TreeMap_Raw_diff(
    mut v_00_u03b1_4882_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4883_: *mut crate::leanh::LeanObject,
    mut v_cmp_4884_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4885_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4887_ =
        l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(
            v_cmp_4884_,
            v_t_u2081_4885_,
            v_t_u2082_4886_,
        );
    return v___x_4887_;
}
pub unsafe fn l_Std_TreeMap_Raw_instSDiff___redArg(
    mut v_cmp_4888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4889_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeMap_Raw_diff as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_4889_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4889_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4889_, 2, v_cmp_4888_);
    return v___x_4889_;
}
pub unsafe fn l_Std_TreeMap_Raw_instSDiff(
    mut v_00_u03b1_4890_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4891_: *mut crate::leanh::LeanObject,
    mut v_cmp_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4893_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeMap_Raw_diff as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_4893_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4893_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4893_, 2, v_cmp_4892_);
    return v___x_4893_;
}
pub unsafe fn l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0(
    mut v_cmp_4894_: *mut crate::leanh::LeanObject,
    mut v_a_4895_: *mut crate::leanh::LeanObject,
    mut v_____s_4896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4897_: u8 = 0;
    crate::leanh::lean_inc(v_____s_4896_);
    crate::leanh::lean_inc(v_a_4895_);
    crate::leanh::lean_inc_ref(v_cmp_4894_);
    v___x_4897_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_4894_, v_a_4895_, v_____s_4896_);
    if v___x_4897_ == 0 {
        let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4898_ = crate::leanh::lean_box(0);
        v___x_4899_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_4894_,
            v_a_4895_,
            v___x_4898_,
            v_____s_4896_,
        );
        v___x_4900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4900_, 0, v___x_4899_);
        return v___x_4900_;
    } else {
        let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_4895_);
        crate::leanh::lean_dec_ref(v_cmp_4894_);
        v___x_4901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4901_, 0, v_____s_4896_);
        return v___x_4901_;
    }
}
pub unsafe fn l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg(
    mut v_cmp_4902_: *mut crate::leanh::LeanObject,
    mut v_inst_4903_: *mut crate::leanh::LeanObject,
    mut v_t_4904_: *mut crate::leanh::LeanObject,
    mut v_l_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4906_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4906_, 0, v_cmp_4902_);
    v___x_4907_ = crate::leanh::lean_apply_4(
        v_inst_4903_,
        crate::leanh::lean_box(0),
        v_l_4905_,
        v_t_4904_,
        v___f_4906_,
    );
    return v___x_4907_;
}
pub unsafe fn l_Std_TreeMap_Raw_insertManyIfNewUnit(
    mut v_00_u03b1_4908_: *mut crate::leanh::LeanObject,
    mut v_cmp_4909_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4910_: *mut crate::leanh::LeanObject,
    mut v_inst_4911_: *mut crate::leanh::LeanObject,
    mut v_t_4912_: *mut crate::leanh::LeanObject,
    mut v_l_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4914_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_insertManyIfNewUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4914_, 0, v_cmp_4909_);
    v___x_4915_ = crate::leanh::lean_apply_4(
        v_inst_4911_,
        crate::leanh::lean_box(0),
        v_l_4913_,
        v_t_4912_,
        v___f_4914_,
    );
    return v___x_4915_;
}
pub unsafe fn l_Std_TreeMap_Raw_eraseMany___redArg___lam__0(
    mut v_cmp_4916_: *mut crate::leanh::LeanObject,
    mut v_a_4917_: *mut crate::leanh::LeanObject,
    mut v_____s_4918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4919_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_4916_, v_a_4917_, v_____s_4918_);
    v___x_4920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4920_, 0, v_r_4919_);
    return v___x_4920_;
}
pub unsafe fn l_Std_TreeMap_Raw_eraseMany___redArg(
    mut v_cmp_4921_: *mut crate::leanh::LeanObject,
    mut v_inst_4922_: *mut crate::leanh::LeanObject,
    mut v_t_4923_: *mut crate::leanh::LeanObject,
    mut v_l_4924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4925_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4925_, 0, v_cmp_4921_);
    v___x_4926_ = crate::leanh::lean_apply_4(
        v_inst_4922_,
        crate::leanh::lean_box(0),
        v_l_4924_,
        v_t_4923_,
        v___f_4925_,
    );
    return v___x_4926_;
}
pub unsafe fn l_Std_TreeMap_Raw_eraseMany(
    mut v_00_u03b1_4927_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4928_: *mut crate::leanh::LeanObject,
    mut v_cmp_4929_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4930_: *mut crate::leanh::LeanObject,
    mut v_inst_4931_: *mut crate::leanh::LeanObject,
    mut v_t_4932_: *mut crate::leanh::LeanObject,
    mut v_l_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4934_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4934_, 0, v_cmp_4929_);
    v___x_4935_ = crate::leanh::lean_apply_4(
        v_inst_4931_,
        crate::leanh::lean_box(0),
        v_l_4933_,
        v_t_4932_,
        v___f_4934_,
    );
    return v___x_4935_;
}
pub unsafe fn l_Std_TreeMap_Raw_instRepr___redArg___lam__1(
    mut v___f_4939_: *mut crate::leanh::LeanObject,
    mut v___x_4940_: *mut crate::leanh::LeanObject,
    mut v_m_4941_: *mut crate::leanh::LeanObject,
    mut v_prec_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4943_ = l_Std_TreeMap_Raw_instRepr___redArg___lam__1___closed__1;
    v___x_4944_ = crate::leanh::lean_box(0);
    v___x_4945_ = l_Std_TreeMap_Raw_foldr___redArg___closed__9;
    v___x_4946_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4945_,
        v___f_4939_,
        v___x_4944_,
        v_m_4941_,
    );
    v___x_4947_ = l_List_repr___redArg(v___x_4940_, v___x_4946_);
    v___x_4948_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4948_, 0, v___x_4943_);
    crate::leanh::lean_ctor_set(v___x_4948_, 1, v___x_4947_);
    v___x_4949_ = l_Repr_addAppParen(v___x_4948_, v_prec_4942_);
    return v___x_4949_;
}
pub unsafe fn l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed(
    mut v___f_4950_: *mut crate::leanh::LeanObject,
    mut v___x_4951_: *mut crate::leanh::LeanObject,
    mut v_m_4952_: *mut crate::leanh::LeanObject,
    mut v_prec_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4954_ = l_Std_TreeMap_Raw_instRepr___redArg___lam__1(
        v___f_4950_,
        v___x_4951_,
        v_m_4952_,
        v_prec_4953_,
    );
    crate::leanh::lean_dec(v_prec_4953_);
    return v_res_4954_;
}
pub unsafe fn l_Std_TreeMap_Raw_instRepr___redArg(
    mut v_inst_4955_: *mut crate::leanh::LeanObject,
    mut v_inst_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4957_ = l_Std_TreeMap_Raw_toList___redArg___closed__0;
    v___f_4958_ = crate::leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4958_, 0, v_inst_4956_);
    v___x_4959_ =
        crate::leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4959_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4959_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4959_, 2, v_inst_4955_);
    crate::leanh::lean_closure_set(v___x_4959_, 3, v___f_4958_);
    v___f_4960_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeMap_Raw_instRepr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4960_, 0, v___f_4957_);
    crate::leanh::lean_closure_set(v___f_4960_, 1, v___x_4959_);
    return v___f_4960_;
}
pub unsafe fn l_Std_TreeMap_Raw_instRepr(
    mut v_00_u03b1_4961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4962_: *mut crate::leanh::LeanObject,
    mut v_cmp_4963_: *mut crate::leanh::LeanObject,
    mut v_inst_4964_: *mut crate::leanh::LeanObject,
    mut v_inst_4965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4966_ = l_Std_TreeMap_Raw_instRepr___redArg(v_inst_4964_, v_inst_4965_);
    return v___x_4966_;
}
pub unsafe fn l_Std_TreeMap_Raw_instRepr___boxed(
    mut v_00_u03b1_4967_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4968_: *mut crate::leanh::LeanObject,
    mut v_cmp_4969_: *mut crate::leanh::LeanObject,
    mut v_inst_4970_: *mut crate::leanh::LeanObject,
    mut v_inst_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4972_ = l_Std_TreeMap_Raw_instRepr(
        v_00_u03b1_4967_,
        v_00_u03b2_4968_,
        v_cmp_4969_,
        v_inst_4970_,
        v_inst_4971_,
    );
    crate::leanh::lean_dec_ref(v_cmp_4969_);
    return v_res_4972_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Raw_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_Raw_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeMap_Raw___auto__1 = _init_l_Std_TreeMap_Raw___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeMap_Raw___auto__1);
    l_Std_TreeMap_Raw_ofList___auto__1 = _init_l_Std_TreeMap_Raw_ofList___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeMap_Raw_ofList___auto__1);
    l_Std_TreeMap_Raw_unitOfList___auto__1 = _init_l_Std_TreeMap_Raw_unitOfList___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeMap_Raw_unitOfList___auto__1);
    l_Std_TreeMap_Raw_ofArray___auto__1 = _init_l_Std_TreeMap_Raw_ofArray___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeMap_Raw_ofArray___auto__1);
    l_Std_TreeMap_Raw_unitOfArray___auto__1 = _init_l_Std_TreeMap_Raw_unitOfArray___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeMap_Raw_unitOfArray___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_Raw_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Raw_Basic(builtin);
}
