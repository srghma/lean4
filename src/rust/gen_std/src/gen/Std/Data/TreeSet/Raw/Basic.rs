// Lean compiler output
// Module: Std.Data.TreeSet.Raw.Basic
// Imports: Std.Data.TreeMap.Raw.Basic Std.Data.TreeSet.Basic
use crate::ffi::{lean_array_push, lean_array_size, lean_nat_dec_eq, lean_string_utf8_byte_size};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::List::Control::l_List_forIn_x27_loop___redArg;
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_Lean_replaceRef, l_String_toRawSubstring_x27, l_panic___redArg,
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
pub static l_Std_TreeSet_Raw___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet_Raw___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet_Raw___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet_Raw___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_Raw___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_Raw___auto__1___closed__14_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_TreeSet_Raw___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_Raw___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_Raw___auto__1___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16710690322389477741 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_Raw___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_Raw___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_Raw___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [84, 114, 101, 101, 83, 101, 116, 0],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__3_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            206985604220839926 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            9795449845313637869 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            2456139370004573775 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__9_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_term___x7em___00__closed__13_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_term___x7em___00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_Raw_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,206985604220839926 as *mut crate::leanh::LeanObject] };
static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw_term___x7em___00__closed__2_value) as *mut crate::leanh::LeanObject,9795449845313637869 as *mut crate::leanh::LeanObject] };
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,14075073652097311246 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<
    26,
> = crate::leanh::LeanStringObject {
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
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
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
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_foldr___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_Raw_foldr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_foldr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_partition___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_TreeSet_Raw_partition___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_partition___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_any___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_TreeSet_Raw_any___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_any___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_Raw_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_Raw_ofList___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_Raw_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_toArray___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Std_TreeSet_Raw_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_Raw_ofArray___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value:
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
        83, 116, 100, 46, 84, 114, 101, 101, 83, 101, 116, 46, 82, 97, 119, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = l_Std_TreeSet_Raw___auto__1___closed__10;
    v___x_1711_ = l_Lean_mkAtom(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__12_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__12,
    );
    v___x_1713_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1714_ = lean_array_push(v___x_1713_, v___x_1712_);
    return v___x_1714_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Std_TreeSet_Raw___auto__1___closed__14;
    v___x_1717_ = lean_string_utf8_byte_size(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__15_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__15,
    );
    v___x_1719_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1720_ = l_Std_TreeSet_Raw___auto__1___closed__14;
    v___x_1721_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1720_);
    crate::leanh::lean_ctor_set(v___x_1721_, 1, v___x_1719_);
    crate::leanh::lean_ctor_set(v___x_1721_, 2, v___x_1718_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = crate::leanh::lean_box(0);
    v___x_1725_ = l_Std_TreeSet_Raw___auto__1___closed__17;
    v___x_1726_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__16_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__16,
    );
    v___x_1727_ = crate::leanh::lean_box(2);
    v___x_1728_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1728_, 0, v___x_1727_);
    crate::leanh::lean_ctor_set(v___x_1728_, 1, v___x_1726_);
    crate::leanh::lean_ctor_set(v___x_1728_, 2, v___x_1725_);
    crate::leanh::lean_ctor_set(v___x_1728_, 3, v___x_1724_);
    return v___x_1728_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__18_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__18,
    );
    v___x_1730_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__13_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__13,
    );
    v___x_1731_ = lean_array_push(v___x_1730_, v___x_1729_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__19_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__19,
    );
    v___x_1733_ = l_Std_TreeSet_Raw___auto__1___closed__11;
    v___x_1734_ = crate::leanh::lean_box(2);
    v___x_1735_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1735_, 0, v___x_1734_);
    crate::leanh::lean_ctor_set(v___x_1735_, 1, v___x_1733_);
    crate::leanh::lean_ctor_set(v___x_1735_, 2, v___x_1732_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__20_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__20,
    );
    v___x_1737_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1738_ = lean_array_push(v___x_1737_, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__21_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__21,
    );
    v___x_1740_ = l_Std_TreeSet_Raw___auto__1___closed__9;
    v___x_1741_ = crate::leanh::lean_box(2);
    v___x_1742_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1741_);
    crate::leanh::lean_ctor_set(v___x_1742_, 1, v___x_1740_);
    crate::leanh::lean_ctor_set(v___x_1742_, 2, v___x_1739_);
    return v___x_1742_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__22_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__22,
    );
    v___x_1744_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1745_ = lean_array_push(v___x_1744_, v___x_1743_);
    return v___x_1745_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__23_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__23,
    );
    v___x_1747_ = l_Std_TreeSet_Raw___auto__1___closed__7;
    v___x_1748_ = crate::leanh::lean_box(2);
    v___x_1749_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1749_, 0, v___x_1748_);
    crate::leanh::lean_ctor_set(v___x_1749_, 1, v___x_1747_);
    crate::leanh::lean_ctor_set(v___x_1749_, 2, v___x_1746_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__24_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__24,
    );
    v___x_1751_ = l_Std_TreeSet_Raw___auto__1___closed__5;
    v___x_1752_ = lean_array_push(v___x_1751_, v___x_1750_);
    return v___x_1752_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__25_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__25,
    );
    v___x_1754_ = l_Std_TreeSet_Raw___auto__1___closed__4;
    v___x_1755_ = crate::leanh::lean_box(2);
    v___x_1756_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1755_);
    crate::leanh::lean_ctor_set(v___x_1756_, 1, v___x_1754_);
    crate::leanh::lean_ctor_set(v___x_1756_, 2, v___x_1753_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__26,
    );
    return v___x_1757_;
}
pub unsafe fn l_Std_TreeSet_Raw_instCoeWFWFUnitInner(
    mut v_00_u03b1_1758_: *mut crate::leanh::LeanObject,
    mut v_cmp_1759_: *mut crate::leanh::LeanObject,
    mut v_t_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = crate::leanh::lean_box(0);
    return v___x_1761_;
}
pub unsafe fn l_Std_TreeSet_Raw_instCoeWFWFUnitInner___boxed(
    mut v_00_u03b1_1762_: *mut crate::leanh::LeanObject,
    mut v_cmp_1763_: *mut crate::leanh::LeanObject,
    mut v_t_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1765_ = l_Std_TreeSet_Raw_instCoeWFWFUnitInner(v_00_u03b1_1762_, v_cmp_1763_, v_t_1764_);
    crate::leanh::lean_dec(v_t_1764_);
    crate::leanh::lean_dec_ref(v_cmp_1763_);
    return v_res_1765_;
}
pub unsafe fn l_Std_TreeSet_Raw_empty(
    mut v_00_u03b1_1766_: *mut crate::leanh::LeanObject,
    mut v_cmp_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = crate::leanh::lean_box(1);
    return v___x_1768_;
}
pub unsafe fn l_Std_TreeSet_Raw_empty___boxed(
    mut v_00_u03b1_1769_: *mut crate::leanh::LeanObject,
    mut v_cmp_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Std_TreeSet_Raw_empty(v_00_u03b1_1769_, v_cmp_1770_);
    crate::leanh::lean_dec_ref(v_cmp_1770_);
    return v_res_1771_;
}
pub unsafe fn l_Std_TreeSet_Raw_instEmptyCollection(
    mut v_00_u03b1_1772_: *mut crate::leanh::LeanObject,
    mut v_cmp_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = crate::leanh::lean_box(1);
    return v___x_1774_;
}
pub unsafe fn l_Std_TreeSet_Raw_instEmptyCollection___boxed(
    mut v_00_u03b1_1775_: *mut crate::leanh::LeanObject,
    mut v_cmp_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Std_TreeSet_Raw_instEmptyCollection(v_00_u03b1_1775_, v_cmp_1776_);
    crate::leanh::lean_dec_ref(v_cmp_1776_);
    return v_res_1777_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInhabited(
    mut v_00_u03b1_1778_: *mut crate::leanh::LeanObject,
    mut v_cmp_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = crate::leanh::lean_box(1);
    return v___x_1780_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInhabited___boxed(
    mut v_00_u03b1_1781_: *mut crate::leanh::LeanObject,
    mut v_cmp_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l_Std_TreeSet_Raw_instInhabited(v_00_u03b1_1781_, v_cmp_1782_);
    crate::leanh::lean_dec_ref(v_cmp_1782_);
    return v_res_1783_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1823_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__3;
    v___x_1824_ = l_String_toRawSubstring_x27(v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(
    mut v_x_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
    mut v_a_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    v___x_1846_ = l_Std_TreeSet_Raw_term___x7em___00__closed__4;
    crate::leanh::lean_inc(v_x_1843_);
    v___x_1847_ = l_Lean_Syntax_isOfKind(v_x_1843_, v___x_1846_);
    if v___x_1847_ == 0 {
        let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1843_);
        v___x_1848_ = crate::leanh::lean_box(1);
        v___x_1849_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1848_);
        crate::leanh::lean_ctor_set(v___x_1849_, 1, v_a_1845_);
        return v___x_1849_;
    } else {
        let mut v_quotContext_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: u8 = 0;
        let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1850_ = crate::leanh::lean_ctor_get(v_a_1844_, 1);
        v_currMacroScope_1851_ = crate::leanh::lean_ctor_get(v_a_1844_, 2);
        v_ref_1852_ = crate::leanh::lean_ctor_get(v_a_1844_, 5);
        v___x_1853_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1854_ = l_Lean_Syntax_getArg(v_x_1843_, v___x_1853_);
        v___x_1855_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1856_ = l_Lean_Syntax_getArg(v_x_1843_, v___x_1855_);
        crate::leanh::lean_dec(v_x_1843_);
        v___x_1857_ = 0;
        v___x_1858_ = l_Lean_SourceInfo_fromRef(v_ref_1852_, v___x_1857_);
        v___x_1859_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2;
        v___x_1860_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4), core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4_once), _init_l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__4);
        v___x_1861_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__5;
        crate::leanh::lean_inc(v_currMacroScope_1851_);
        crate::leanh::lean_inc(v_quotContext_1850_);
        v___x_1862_ =
            l_Lean_addMacroScope(v_quotContext_1850_, v___x_1861_, v_currMacroScope_1851_);
        v___x_1863_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__10;
        crate::leanh::lean_inc_n(v___x_1858_, 2);
        v___x_1864_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1858_);
        crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1860_);
        crate::leanh::lean_ctor_set(v___x_1864_, 2, v___x_1862_);
        crate::leanh::lean_ctor_set(v___x_1864_, 3, v___x_1863_);
        v___x_1865_ = l_Std_TreeSet_Raw___auto__1___closed__9;
        v___x_1866_ = l_Lean_Syntax_node2(v___x_1858_, v___x_1865_, v___x_1854_, v___x_1856_);
        v___x_1867_ = l_Lean_Syntax_node2(v___x_1858_, v___x_1859_, v___x_1864_, v___x_1866_);
        v___x_1868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
        crate::leanh::lean_ctor_set(v___x_1868_, 1, v_a_1845_);
        return v___x_1868_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___boxed(
    mut v_x_1869_: *mut crate::leanh::LeanObject,
    mut v_a_1870_: *mut crate::leanh::LeanObject,
    mut v_a_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1(v_x_1869_, v_a_1870_, v_a_1871_);
    crate::leanh::lean_dec_ref(v_a_1870_);
    return v_res_1872_;
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(
    mut v_x_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
    mut v_a_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    v___x_1879_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______macroRules__Std__TreeSet__Raw__term___x7em____1___closed__2;
    crate::leanh::lean_inc(v_x_1876_);
    v___x_1880_ = l_Lean_Syntax_isOfKind(v_x_1876_, v___x_1879_);
    if v___x_1880_ == 0 {
        let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1876_);
        v___x_1881_ = crate::leanh::lean_box(0);
        v___x_1882_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
        crate::leanh::lean_ctor_set(v___x_1882_, 1, v_a_1878_);
        return v___x_1882_;
    } else {
        let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: u8 = 0;
        v___x_1883_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1884_ = l_Lean_Syntax_getArg(v_x_1876_, v___x_1883_);
        v___x_1885_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_1884_);
        v___x_1886_ = l_Lean_Syntax_isOfKind(v___x_1884_, v___x_1885_);
        if v___x_1886_ == 0 {
            let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1884_);
            crate::leanh::lean_dec(v_x_1876_);
            v___x_1887_ = crate::leanh::lean_box(0);
            v___x_1888_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1888_, 0, v___x_1887_);
            crate::leanh::lean_ctor_set(v___x_1888_, 1, v_a_1878_);
            return v___x_1888_;
        } else {
            let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1892_: u8 = 0;
            v___x_1889_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1890_ = l_Lean_Syntax_getArg(v_x_1876_, v___x_1889_);
            crate::leanh::lean_dec(v_x_1876_);
            v___x_1891_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1890_);
            v___x_1892_ = l_Lean_Syntax_matchesNull(v___x_1890_, v___x_1891_);
            if v___x_1892_ == 0 {
                let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1890_);
                crate::leanh::lean_dec(v___x_1884_);
                v___x_1893_ = crate::leanh::lean_box(0);
                v___x_1894_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1894_, 0, v___x_1893_);
                crate::leanh::lean_ctor_set(v___x_1894_, 1, v_a_1878_);
                return v___x_1894_;
            } else {
                let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1898_: u8 = 0;
                let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1895_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1883_);
                v___x_1896_ = l_Lean_Syntax_getArg(v___x_1890_, v___x_1889_);
                crate::leanh::lean_dec(v___x_1890_);
                v_ref_1897_ = l_Lean_replaceRef(v___x_1884_, v_a_1877_);
                crate::leanh::lean_dec(v___x_1884_);
                v___x_1898_ = 0;
                v___x_1899_ = l_Lean_SourceInfo_fromRef(v_ref_1897_, v___x_1898_);
                crate::leanh::lean_dec(v_ref_1897_);
                v___x_1900_ = l_Std_TreeSet_Raw_term___x7em___00__closed__4;
                v___x_1901_ = l_Std_TreeSet_Raw_term___x7em___00__closed__7;
                crate::leanh::lean_inc(v___x_1899_);
                v___x_1902_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1902_, 0, v___x_1899_);
                crate::leanh::lean_ctor_set(v___x_1902_, 1, v___x_1901_);
                v___x_1903_ = l_Lean_Syntax_node3(
                    v___x_1899_,
                    v___x_1900_,
                    v___x_1895_,
                    v___x_1902_,
                    v___x_1896_,
                );
                v___x_1904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1904_, 0, v___x_1903_);
                crate::leanh::lean_ctor_set(v___x_1904_, 1, v_a_1878_);
                return v___x_1904_;
            }
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1___boxed(
    mut v_x_1905_: *mut crate::leanh::LeanObject,
    mut v_a_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Std_TreeSet_Raw___aux__Std__Data__TreeSet__Raw__Basic______unexpand__Std__TreeSet__Raw__Equiv__1(v_x_1905_, v_a_1906_, v_a_1907_);
    crate::leanh::lean_dec(v_a_1906_);
    return v_res_1908_;
}
pub unsafe fn l_Std_TreeSet_Raw_insert___redArg(
    mut v_cmp_1909_: *mut crate::leanh::LeanObject,
    mut v_l_1910_: *mut crate::leanh::LeanObject,
    mut v_a_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: u8 = 0;
    crate::leanh::lean_inc(v_l_1910_);
    crate::leanh::lean_inc(v_a_1911_);
    crate::leanh::lean_inc_ref(v_cmp_1909_);
    v___x_1912_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1909_, v_a_1911_, v_l_1910_);
    if v___x_1912_ == 0 {
        let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1913_ = crate::leanh::lean_box(0);
        v___x_1914_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1909_,
            v_a_1911_,
            v___x_1913_,
            v_l_1910_,
        );
        return v___x_1914_;
    } else {
        crate::leanh::lean_dec(v_a_1911_);
        crate::leanh::lean_dec_ref(v_cmp_1909_);
        return v_l_1910_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_insert(
    mut v_00_u03b1_1915_: *mut crate::leanh::LeanObject,
    mut v_cmp_1916_: *mut crate::leanh::LeanObject,
    mut v_l_1917_: *mut crate::leanh::LeanObject,
    mut v_a_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: u8 = 0;
    crate::leanh::lean_inc(v_l_1917_);
    crate::leanh::lean_inc(v_a_1918_);
    crate::leanh::lean_inc_ref(v_cmp_1916_);
    v___x_1919_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1916_, v_a_1918_, v_l_1917_);
    if v___x_1919_ == 0 {
        let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1920_ = crate::leanh::lean_box(0);
        v___x_1921_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1916_,
            v_a_1918_,
            v___x_1920_,
            v_l_1917_,
        );
        return v___x_1921_;
    } else {
        crate::leanh::lean_dec(v_a_1918_);
        crate::leanh::lean_dec_ref(v_cmp_1916_);
        return v_l_1917_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_instSingleton___redArg___lam__0(
    mut v_cmp_1922_: *mut crate::leanh::LeanObject,
    mut v_e_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    v___x_1924_ = crate::leanh::lean_box(1);
    crate::leanh::lean_inc(v_e_1923_);
    crate::leanh::lean_inc_ref(v_cmp_1922_);
    v___x_1925_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1922_, v_e_1923_, v___x_1924_);
    if v___x_1925_ == 0 {
        let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1926_ = crate::leanh::lean_box(0);
        v___x_1927_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1922_,
            v_e_1923_,
            v___x_1926_,
            v___x_1924_,
        );
        return v___x_1927_;
    } else {
        crate::leanh::lean_dec(v_e_1923_);
        crate::leanh::lean_dec_ref(v_cmp_1922_);
        return v___x_1924_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_instSingleton___redArg(
    mut v_cmp_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1929_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1929_, 0, v_cmp_1928_);
    return v___f_1929_;
}
pub unsafe fn l_Std_TreeSet_Raw_instSingleton(
    mut v_00_u03b1_1930_: *mut crate::leanh::LeanObject,
    mut v_cmp_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1932_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1932_, 0, v_cmp_1931_);
    return v___f_1932_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInsert___redArg___lam__0(
    mut v_cmp_1933_: *mut crate::leanh::LeanObject,
    mut v_e_1934_: *mut crate::leanh::LeanObject,
    mut v_s_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1936_: u8 = 0;
    crate::leanh::lean_inc(v_s_1935_);
    crate::leanh::lean_inc(v_e_1934_);
    crate::leanh::lean_inc_ref(v_cmp_1933_);
    v___x_1936_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1933_, v_e_1934_, v_s_1935_);
    if v___x_1936_ == 0 {
        let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1937_ = crate::leanh::lean_box(0);
        v___x_1938_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1933_,
            v_e_1934_,
            v___x_1937_,
            v_s_1935_,
        );
        return v___x_1938_;
    } else {
        crate::leanh::lean_dec(v_e_1934_);
        crate::leanh::lean_dec_ref(v_cmp_1933_);
        return v_s_1935_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_instInsert___redArg(
    mut v_cmp_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1940_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1940_, 0, v_cmp_1939_);
    return v___f_1940_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInsert(
    mut v_00_u03b1_1941_: *mut crate::leanh::LeanObject,
    mut v_cmp_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1943_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1943_, 0, v_cmp_1942_);
    return v___f_1943_;
}
pub unsafe fn l_Std_TreeSet_Raw_containsThenInsert___redArg(
    mut v_cmp_1944_: *mut crate::leanh::LeanObject,
    mut v_t_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1947_: u8 = 0;
    crate::leanh::lean_inc(v_t_1945_);
    crate::leanh::lean_inc(v_a_1946_);
    crate::leanh::lean_inc_ref(v_cmp_1944_);
    v___x_1947_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1944_, v_a_1946_, v_t_1945_);
    if v___x_1947_ == 0 {
        let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1948_ = crate::leanh::lean_box(0);
        v___x_1949_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1944_,
            v_a_1946_,
            v___x_1948_,
            v_t_1945_,
        );
        v___x_1950_ = crate::leanh::lean_box((v___x_1947_) as usize);
        v___x_1951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1951_, 0, v___x_1950_);
        crate::leanh::lean_ctor_set(v___x_1951_, 1, v___x_1949_);
        return v___x_1951_;
    } else {
        let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1946_);
        crate::leanh::lean_dec_ref(v_cmp_1944_);
        v___x_1952_ = crate::leanh::lean_box((v___x_1947_) as usize);
        v___x_1953_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1953_, 0, v___x_1952_);
        crate::leanh::lean_ctor_set(v___x_1953_, 1, v_t_1945_);
        return v___x_1953_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_containsThenInsert(
    mut v_00_u03b1_1954_: *mut crate::leanh::LeanObject,
    mut v_cmp_1955_: *mut crate::leanh::LeanObject,
    mut v_t_1956_: *mut crate::leanh::LeanObject,
    mut v_a_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: u8 = 0;
    crate::leanh::lean_inc(v_t_1956_);
    crate::leanh::lean_inc(v_a_1957_);
    crate::leanh::lean_inc_ref(v_cmp_1955_);
    v___x_1958_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1955_, v_a_1957_, v_t_1956_);
    if v___x_1958_ == 0 {
        let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1959_ = crate::leanh::lean_box(0);
        v___x_1960_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_1955_,
            v_a_1957_,
            v___x_1959_,
            v_t_1956_,
        );
        v___x_1961_ = crate::leanh::lean_box((v___x_1958_) as usize);
        v___x_1962_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
        crate::leanh::lean_ctor_set(v___x_1962_, 1, v___x_1960_);
        return v___x_1962_;
    } else {
        let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1957_);
        crate::leanh::lean_dec_ref(v_cmp_1955_);
        v___x_1963_ = crate::leanh::lean_box((v___x_1958_) as usize);
        v___x_1964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1964_, 0, v___x_1963_);
        crate::leanh::lean_ctor_set(v___x_1964_, 1, v_t_1956_);
        return v___x_1964_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_contains___redArg(
    mut v_cmp_1965_: *mut crate::leanh::LeanObject,
    mut v_l_1966_: *mut crate::leanh::LeanObject,
    mut v_a_1967_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1968_: u8 = 0;
    v___x_1968_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1965_, v_a_1967_, v_l_1966_);
    return v___x_1968_;
}
pub unsafe fn l_Std_TreeSet_Raw_contains___redArg___boxed(
    mut v_cmp_1969_: *mut crate::leanh::LeanObject,
    mut v_l_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1972_: u8 = 0;
    let mut v_r_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1972_ = l_Std_TreeSet_Raw_contains___redArg(v_cmp_1969_, v_l_1970_, v_a_1971_);
    v_r_1973_ = crate::leanh::lean_box((v_res_1972_) as usize);
    return v_r_1973_;
}
pub unsafe fn l_Std_TreeSet_Raw_contains(
    mut v_00_u03b1_1974_: *mut crate::leanh::LeanObject,
    mut v_cmp_1975_: *mut crate::leanh::LeanObject,
    mut v_l_1976_: *mut crate::leanh::LeanObject,
    mut v_a_1977_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1978_: u8 = 0;
    v___x_1978_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1975_, v_a_1977_, v_l_1976_);
    return v___x_1978_;
}
pub unsafe fn l_Std_TreeSet_Raw_contains___boxed(
    mut v_00_u03b1_1979_: *mut crate::leanh::LeanObject,
    mut v_cmp_1980_: *mut crate::leanh::LeanObject,
    mut v_l_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1983_: u8 = 0;
    let mut v_r_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Std_TreeSet_Raw_contains(v_00_u03b1_1979_, v_cmp_1980_, v_l_1981_, v_a_1982_);
    v_r_1984_ = crate::leanh::lean_box((v_res_1983_) as usize);
    return v_r_1984_;
}
pub unsafe fn l_Std_TreeSet_Raw_instMembership(
    mut v_00_u03b1_1985_: *mut crate::leanh::LeanObject,
    mut v_cmp_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1987_ = crate::leanh::lean_box(0);
    return v___x_1987_;
}
pub unsafe fn l_Std_TreeSet_Raw_instMembership___boxed(
    mut v_00_u03b1_1988_: *mut crate::leanh::LeanObject,
    mut v_cmp_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1990_ = l_Std_TreeSet_Raw_instMembership(v_00_u03b1_1988_, v_cmp_1989_);
    crate::leanh::lean_dec_ref(v_cmp_1989_);
    return v_res_1990_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem___redArg(
    mut v_cmp_1991_: *mut crate::leanh::LeanObject,
    mut v_t_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1994_: u8 = 0;
    v___x_1994_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1991_, v_a_1993_, v_t_1992_);
    return v___x_1994_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem___redArg___boxed(
    mut v_cmp_1995_: *mut crate::leanh::LeanObject,
    mut v_t_1996_: *mut crate::leanh::LeanObject,
    mut v_a_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1998_: u8 = 0;
    let mut v_r_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Std_TreeSet_Raw_instDecidableMem___redArg(v_cmp_1995_, v_t_1996_, v_a_1997_);
    v_r_1999_ = crate::leanh::lean_box((v_res_1998_) as usize);
    return v_r_1999_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem(
    mut v_00_u03b1_2000_: *mut crate::leanh::LeanObject,
    mut v_cmp_2001_: *mut crate::leanh::LeanObject,
    mut v_t_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2004_: u8 = 0;
    v___x_2004_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2001_, v_a_2003_, v_t_2002_);
    return v___x_2004_;
}
pub unsafe fn l_Std_TreeSet_Raw_instDecidableMem___boxed(
    mut v_00_u03b1_2005_: *mut crate::leanh::LeanObject,
    mut v_cmp_2006_: *mut crate::leanh::LeanObject,
    mut v_t_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: u8 = 0;
    let mut v_r_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ =
        l_Std_TreeSet_Raw_instDecidableMem(v_00_u03b1_2005_, v_cmp_2006_, v_t_2007_, v_a_2008_);
    v_r_2010_ = crate::leanh::lean_box((v_res_2009_) as usize);
    return v_r_2010_;
}
pub unsafe fn l_Std_TreeSet_Raw_size___redArg(
    mut v_t_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2011_) == 0 {
        let mut v_size_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_2012_ = crate::leanh::lean_ctor_get(v_t_2011_, 0);
        crate::leanh::lean_inc(v_size_2012_);
        return v_size_2012_;
    } else {
        let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2013_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2013_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_size___redArg___boxed(
    mut v_t_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2015_ = l_Std_TreeSet_Raw_size___redArg(v_t_2014_);
    crate::leanh::lean_dec(v_t_2014_);
    return v_res_2015_;
}
pub unsafe fn l_Std_TreeSet_Raw_size(
    mut v_00_u03b1_2016_: *mut crate::leanh::LeanObject,
    mut v_cmp_2017_: *mut crate::leanh::LeanObject,
    mut v_t_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2018_) == 0 {
        let mut v_size_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_2019_ = crate::leanh::lean_ctor_get(v_t_2018_, 0);
        crate::leanh::lean_inc(v_size_2019_);
        return v_size_2019_;
    } else {
        let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2020_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2020_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_size___boxed(
    mut v_00_u03b1_2021_: *mut crate::leanh::LeanObject,
    mut v_cmp_2022_: *mut crate::leanh::LeanObject,
    mut v_t_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2024_ = l_Std_TreeSet_Raw_size(v_00_u03b1_2021_, v_cmp_2022_, v_t_2023_);
    crate::leanh::lean_dec(v_t_2023_);
    crate::leanh::lean_dec_ref(v_cmp_2022_);
    return v_res_2024_;
}
pub unsafe fn l_Std_TreeSet_Raw_isEmpty___redArg(
    mut v_t_2025_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_2025_) == 0 {
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
    mut v_t_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2029_: u8 = 0;
    let mut v_r_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2029_ = l_Std_TreeSet_Raw_isEmpty___redArg(v_t_2028_);
    crate::leanh::lean_dec(v_t_2028_);
    v_r_2030_ = crate::leanh::lean_box((v_res_2029_) as usize);
    return v_r_2030_;
}
pub unsafe fn l_Std_TreeSet_Raw_isEmpty(
    mut v_00_u03b1_2031_: *mut crate::leanh::LeanObject,
    mut v_cmp_2032_: *mut crate::leanh::LeanObject,
    mut v_t_2033_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_2033_) == 0 {
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
    mut v_00_u03b1_2036_: *mut crate::leanh::LeanObject,
    mut v_cmp_2037_: *mut crate::leanh::LeanObject,
    mut v_t_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2039_: u8 = 0;
    let mut v_r_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Std_TreeSet_Raw_isEmpty(v_00_u03b1_2036_, v_cmp_2037_, v_t_2038_);
    crate::leanh::lean_dec(v_t_2038_);
    crate::leanh::lean_dec_ref(v_cmp_2037_);
    v_r_2040_ = crate::leanh::lean_box((v_res_2039_) as usize);
    return v_r_2040_;
}
pub unsafe fn l_Std_TreeSet_Raw_erase___redArg(
    mut v_cmp_2041_: *mut crate::leanh::LeanObject,
    mut v_t_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2041_, v_a_2043_, v_t_2042_);
    return v___x_2044_;
}
pub unsafe fn l_Std_TreeSet_Raw_erase(
    mut v_00_u03b1_2045_: *mut crate::leanh::LeanObject,
    mut v_cmp_2046_: *mut crate::leanh::LeanObject,
    mut v_t_2047_: *mut crate::leanh::LeanObject,
    mut v_a_2048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_2046_, v_a_2048_, v_t_2047_);
    return v___x_2049_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x3f___redArg(
    mut v_cmp_2050_: *mut crate::leanh::LeanObject,
    mut v_t_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2050_, v_t_2051_, v_a_2052_);
    return v___x_2053_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x3f(
    mut v_00_u03b1_2054_: *mut crate::leanh::LeanObject,
    mut v_cmp_2055_: *mut crate::leanh::LeanObject,
    mut v_t_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2055_, v_t_2056_, v_a_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Std_TreeSet_Raw_get___redArg(
    mut v_cmp_2059_: *mut crate::leanh::LeanObject,
    mut v_t_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2059_, v_t_2060_, v_a_2061_);
    return v___x_2062_;
}
pub unsafe fn l_Std_TreeSet_Raw_get(
    mut v_00_u03b1_2063_: *mut crate::leanh::LeanObject,
    mut v_cmp_2064_: *mut crate::leanh::LeanObject,
    mut v_t_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
    mut v_h_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2068_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2064_, v_t_2065_, v_a_2066_);
    return v___x_2068_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21___redArg(
    mut v_cmp_2069_: *mut crate::leanh::LeanObject,
    mut v_inst_2070_: *mut crate::leanh::LeanObject,
    mut v_t_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2073_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2069_,
        v_t_2071_,
        v_a_2072_,
        v_inst_2070_,
    );
    return v___x_2073_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21___redArg___boxed(
    mut v_cmp_2074_: *mut crate::leanh::LeanObject,
    mut v_inst_2075_: *mut crate::leanh::LeanObject,
    mut v_t_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2078_ =
        l_Std_TreeSet_Raw_get_x21___redArg(v_cmp_2074_, v_inst_2075_, v_t_2076_, v_a_2077_);
    crate::leanh::lean_dec(v_inst_2075_);
    return v_res_2078_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21(
    mut v_00_u03b1_2079_: *mut crate::leanh::LeanObject,
    mut v_cmp_2080_: *mut crate::leanh::LeanObject,
    mut v_inst_2081_: *mut crate::leanh::LeanObject,
    mut v_t_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2080_,
        v_t_2082_,
        v_a_2083_,
        v_inst_2081_,
    );
    return v___x_2084_;
}
pub unsafe fn l_Std_TreeSet_Raw_get_x21___boxed(
    mut v_00_u03b1_2085_: *mut crate::leanh::LeanObject,
    mut v_cmp_2086_: *mut crate::leanh::LeanObject,
    mut v_inst_2087_: *mut crate::leanh::LeanObject,
    mut v_t_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Std_TreeSet_Raw_get_x21(
        v_00_u03b1_2085_,
        v_cmp_2086_,
        v_inst_2087_,
        v_t_2088_,
        v_a_2089_,
    );
    crate::leanh::lean_dec(v_inst_2087_);
    return v_res_2090_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD___redArg(
    mut v_cmp_2091_: *mut crate::leanh::LeanObject,
    mut v_t_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
    mut v_fallback_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2091_,
        v_t_2092_,
        v_a_2093_,
        v_fallback_2094_,
    );
    return v___x_2095_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD___redArg___boxed(
    mut v_cmp_2096_: *mut crate::leanh::LeanObject,
    mut v_t_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_fallback_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ =
        l_Std_TreeSet_Raw_getD___redArg(v_cmp_2096_, v_t_2097_, v_a_2098_, v_fallback_2099_);
    crate::leanh::lean_dec(v_fallback_2099_);
    return v_res_2100_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD(
    mut v_00_u03b1_2101_: *mut crate::leanh::LeanObject,
    mut v_cmp_2102_: *mut crate::leanh::LeanObject,
    mut v_t_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
    mut v_fallback_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2102_,
        v_t_2103_,
        v_a_2104_,
        v_fallback_2105_,
    );
    return v___x_2106_;
}
pub unsafe fn l_Std_TreeSet_Raw_getD___boxed(
    mut v_00_u03b1_2107_: *mut crate::leanh::LeanObject,
    mut v_cmp_2108_: *mut crate::leanh::LeanObject,
    mut v_t_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_fallback_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2112_ = l_Std_TreeSet_Raw_getD(
        v_00_u03b1_2107_,
        v_cmp_2108_,
        v_t_2109_,
        v_a_2110_,
        v_fallback_2111_,
    );
    crate::leanh::lean_dec(v_fallback_2111_);
    return v_res_2112_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f___redArg(
    mut v_t_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2113_);
    return v___x_2114_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f___redArg___boxed(
    mut v_t_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Std_TreeSet_Raw_min_x3f___redArg(v_t_2115_);
    crate::leanh::lean_dec(v_t_2115_);
    return v_res_2116_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f(
    mut v_00_u03b1_2117_: *mut crate::leanh::LeanObject,
    mut v_cmp_2118_: *mut crate::leanh::LeanObject,
    mut v_t_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2119_);
    return v___x_2120_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x3f___boxed(
    mut v_00_u03b1_2121_: *mut crate::leanh::LeanObject,
    mut v_cmp_2122_: *mut crate::leanh::LeanObject,
    mut v_t_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_Std_TreeSet_Raw_min_x3f(v_00_u03b1_2121_, v_cmp_2122_, v_t_2123_);
    crate::leanh::lean_dec(v_t_2123_);
    crate::leanh::lean_dec_ref(v_cmp_2122_);
    return v_res_2124_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21___redArg(
    mut v_inst_2125_: *mut crate::leanh::LeanObject,
    mut v_t_2126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2125_, v_t_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21___redArg___boxed(
    mut v_inst_2128_: *mut crate::leanh::LeanObject,
    mut v_t_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2130_ = l_Std_TreeSet_Raw_min_x21___redArg(v_inst_2128_, v_t_2129_);
    crate::leanh::lean_dec(v_t_2129_);
    crate::leanh::lean_dec(v_inst_2128_);
    return v_res_2130_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21(
    mut v_00_u03b1_2131_: *mut crate::leanh::LeanObject,
    mut v_cmp_2132_: *mut crate::leanh::LeanObject,
    mut v_inst_2133_: *mut crate::leanh::LeanObject,
    mut v_t_2134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2135_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2133_, v_t_2134_);
    return v___x_2135_;
}
pub unsafe fn l_Std_TreeSet_Raw_min_x21___boxed(
    mut v_00_u03b1_2136_: *mut crate::leanh::LeanObject,
    mut v_cmp_2137_: *mut crate::leanh::LeanObject,
    mut v_inst_2138_: *mut crate::leanh::LeanObject,
    mut v_t_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Std_TreeSet_Raw_min_x21(v_00_u03b1_2136_, v_cmp_2137_, v_inst_2138_, v_t_2139_);
    crate::leanh::lean_dec(v_t_2139_);
    crate::leanh::lean_dec(v_inst_2138_);
    crate::leanh::lean_dec_ref(v_cmp_2137_);
    return v_res_2140_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD___redArg(
    mut v_t_2141_: *mut crate::leanh::LeanObject,
    mut v_fallback_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2141_, v_fallback_2142_);
    return v___x_2143_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD___redArg___boxed(
    mut v_t_2144_: *mut crate::leanh::LeanObject,
    mut v_fallback_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2146_ = l_Std_TreeSet_Raw_minD___redArg(v_t_2144_, v_fallback_2145_);
    crate::leanh::lean_dec(v_fallback_2145_);
    crate::leanh::lean_dec(v_t_2144_);
    return v_res_2146_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD(
    mut v_00_u03b1_2147_: *mut crate::leanh::LeanObject,
    mut v_cmp_2148_: *mut crate::leanh::LeanObject,
    mut v_t_2149_: *mut crate::leanh::LeanObject,
    mut v_fallback_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2151_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2149_, v_fallback_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Std_TreeSet_Raw_minD___boxed(
    mut v_00_u03b1_2152_: *mut crate::leanh::LeanObject,
    mut v_cmp_2153_: *mut crate::leanh::LeanObject,
    mut v_t_2154_: *mut crate::leanh::LeanObject,
    mut v_fallback_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ =
        l_Std_TreeSet_Raw_minD(v_00_u03b1_2152_, v_cmp_2153_, v_t_2154_, v_fallback_2155_);
    crate::leanh::lean_dec(v_fallback_2155_);
    crate::leanh::lean_dec(v_t_2154_);
    crate::leanh::lean_dec_ref(v_cmp_2153_);
    return v_res_2156_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f___redArg(
    mut v_t_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2158_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2157_);
    return v___x_2158_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f___redArg___boxed(
    mut v_t_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2160_ = l_Std_TreeSet_Raw_max_x3f___redArg(v_t_2159_);
    crate::leanh::lean_dec(v_t_2159_);
    return v_res_2160_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f(
    mut v_00_u03b1_2161_: *mut crate::leanh::LeanObject,
    mut v_cmp_2162_: *mut crate::leanh::LeanObject,
    mut v_t_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2164_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x3f___boxed(
    mut v_00_u03b1_2165_: *mut crate::leanh::LeanObject,
    mut v_cmp_2166_: *mut crate::leanh::LeanObject,
    mut v_t_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Std_TreeSet_Raw_max_x3f(v_00_u03b1_2165_, v_cmp_2166_, v_t_2167_);
    crate::leanh::lean_dec(v_t_2167_);
    crate::leanh::lean_dec_ref(v_cmp_2166_);
    return v_res_2168_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21___redArg(
    mut v_inst_2169_: *mut crate::leanh::LeanObject,
    mut v_t_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2171_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2169_, v_t_2170_);
    return v___x_2171_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21___redArg___boxed(
    mut v_inst_2172_: *mut crate::leanh::LeanObject,
    mut v_t_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_Std_TreeSet_Raw_max_x21___redArg(v_inst_2172_, v_t_2173_);
    crate::leanh::lean_dec(v_t_2173_);
    crate::leanh::lean_dec(v_inst_2172_);
    return v_res_2174_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21(
    mut v_00_u03b1_2175_: *mut crate::leanh::LeanObject,
    mut v_cmp_2176_: *mut crate::leanh::LeanObject,
    mut v_inst_2177_: *mut crate::leanh::LeanObject,
    mut v_t_2178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2179_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2177_, v_t_2178_);
    return v___x_2179_;
}
pub unsafe fn l_Std_TreeSet_Raw_max_x21___boxed(
    mut v_00_u03b1_2180_: *mut crate::leanh::LeanObject,
    mut v_cmp_2181_: *mut crate::leanh::LeanObject,
    mut v_inst_2182_: *mut crate::leanh::LeanObject,
    mut v_t_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Std_TreeSet_Raw_max_x21(v_00_u03b1_2180_, v_cmp_2181_, v_inst_2182_, v_t_2183_);
    crate::leanh::lean_dec(v_t_2183_);
    crate::leanh::lean_dec(v_inst_2182_);
    crate::leanh::lean_dec_ref(v_cmp_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD___redArg(
    mut v_t_2185_: *mut crate::leanh::LeanObject,
    mut v_fallback_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2185_, v_fallback_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD___redArg___boxed(
    mut v_t_2188_: *mut crate::leanh::LeanObject,
    mut v_fallback_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Std_TreeSet_Raw_maxD___redArg(v_t_2188_, v_fallback_2189_);
    crate::leanh::lean_dec(v_fallback_2189_);
    crate::leanh::lean_dec(v_t_2188_);
    return v_res_2190_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD(
    mut v_00_u03b1_2191_: *mut crate::leanh::LeanObject,
    mut v_cmp_2192_: *mut crate::leanh::LeanObject,
    mut v_t_2193_: *mut crate::leanh::LeanObject,
    mut v_fallback_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2193_, v_fallback_2194_);
    return v___x_2195_;
}
pub unsafe fn l_Std_TreeSet_Raw_maxD___boxed(
    mut v_00_u03b1_2196_: *mut crate::leanh::LeanObject,
    mut v_cmp_2197_: *mut crate::leanh::LeanObject,
    mut v_t_2198_: *mut crate::leanh::LeanObject,
    mut v_fallback_2199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2200_ =
        l_Std_TreeSet_Raw_maxD(v_00_u03b1_2196_, v_cmp_2197_, v_t_2198_, v_fallback_2199_);
    crate::leanh::lean_dec(v_fallback_2199_);
    crate::leanh::lean_dec(v_t_2198_);
    crate::leanh::lean_dec_ref(v_cmp_2197_);
    return v_res_2200_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f___redArg(
    mut v_t_2201_: *mut crate::leanh::LeanObject,
    mut v_n_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2201_, v_n_2202_);
    return v___x_2203_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f___redArg___boxed(
    mut v_t_2204_: *mut crate::leanh::LeanObject,
    mut v_n_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Std_TreeSet_Raw_atIdx_x3f___redArg(v_t_2204_, v_n_2205_);
    crate::leanh::lean_dec(v_t_2204_);
    return v_res_2206_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f(
    mut v_00_u03b1_2207_: *mut crate::leanh::LeanObject,
    mut v_cmp_2208_: *mut crate::leanh::LeanObject,
    mut v_t_2209_: *mut crate::leanh::LeanObject,
    mut v_n_2210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2211_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2209_, v_n_2210_);
    return v___x_2211_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x3f___boxed(
    mut v_00_u03b1_2212_: *mut crate::leanh::LeanObject,
    mut v_cmp_2213_: *mut crate::leanh::LeanObject,
    mut v_t_2214_: *mut crate::leanh::LeanObject,
    mut v_n_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2216_ = l_Std_TreeSet_Raw_atIdx_x3f(v_00_u03b1_2212_, v_cmp_2213_, v_t_2214_, v_n_2215_);
    crate::leanh::lean_dec(v_t_2214_);
    crate::leanh::lean_dec_ref(v_cmp_2213_);
    return v_res_2216_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21___redArg(
    mut v_inst_2217_: *mut crate::leanh::LeanObject,
    mut v_t_2218_: *mut crate::leanh::LeanObject,
    mut v_n_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2217_, v_t_2218_, v_n_2219_);
    return v___x_2220_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21___redArg___boxed(
    mut v_inst_2221_: *mut crate::leanh::LeanObject,
    mut v_t_2222_: *mut crate::leanh::LeanObject,
    mut v_n_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Std_TreeSet_Raw_atIdx_x21___redArg(v_inst_2221_, v_t_2222_, v_n_2223_);
    crate::leanh::lean_dec(v_t_2222_);
    crate::leanh::lean_dec(v_inst_2221_);
    return v_res_2224_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21(
    mut v_00_u03b1_2225_: *mut crate::leanh::LeanObject,
    mut v_cmp_2226_: *mut crate::leanh::LeanObject,
    mut v_inst_2227_: *mut crate::leanh::LeanObject,
    mut v_t_2228_: *mut crate::leanh::LeanObject,
    mut v_n_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2227_, v_t_2228_, v_n_2229_);
    return v___x_2230_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdx_x21___boxed(
    mut v_00_u03b1_2231_: *mut crate::leanh::LeanObject,
    mut v_cmp_2232_: *mut crate::leanh::LeanObject,
    mut v_inst_2233_: *mut crate::leanh::LeanObject,
    mut v_t_2234_: *mut crate::leanh::LeanObject,
    mut v_n_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2236_ = l_Std_TreeSet_Raw_atIdx_x21(
        v_00_u03b1_2231_,
        v_cmp_2232_,
        v_inst_2233_,
        v_t_2234_,
        v_n_2235_,
    );
    crate::leanh::lean_dec(v_t_2234_);
    crate::leanh::lean_dec(v_inst_2233_);
    crate::leanh::lean_dec_ref(v_cmp_2232_);
    return v_res_2236_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD___redArg(
    mut v_t_2237_: *mut crate::leanh::LeanObject,
    mut v_n_2238_: *mut crate::leanh::LeanObject,
    mut v_fallback_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2237_, v_n_2238_, v_fallback_2239_);
    return v___x_2240_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD___redArg___boxed(
    mut v_t_2241_: *mut crate::leanh::LeanObject,
    mut v_n_2242_: *mut crate::leanh::LeanObject,
    mut v_fallback_2243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2244_ = l_Std_TreeSet_Raw_atIdxD___redArg(v_t_2241_, v_n_2242_, v_fallback_2243_);
    crate::leanh::lean_dec(v_fallback_2243_);
    crate::leanh::lean_dec(v_t_2241_);
    return v_res_2244_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD(
    mut v_00_u03b1_2245_: *mut crate::leanh::LeanObject,
    mut v_cmp_2246_: *mut crate::leanh::LeanObject,
    mut v_t_2247_: *mut crate::leanh::LeanObject,
    mut v_n_2248_: *mut crate::leanh::LeanObject,
    mut v_fallback_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2250_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2247_, v_n_2248_, v_fallback_2249_);
    return v___x_2250_;
}
pub unsafe fn l_Std_TreeSet_Raw_atIdxD___boxed(
    mut v_00_u03b1_2251_: *mut crate::leanh::LeanObject,
    mut v_cmp_2252_: *mut crate::leanh::LeanObject,
    mut v_t_2253_: *mut crate::leanh::LeanObject,
    mut v_n_2254_: *mut crate::leanh::LeanObject,
    mut v_fallback_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Std_TreeSet_Raw_atIdxD(
        v_00_u03b1_2251_,
        v_cmp_2252_,
        v_t_2253_,
        v_n_2254_,
        v_fallback_2255_,
    );
    crate::leanh::lean_dec(v_fallback_2255_);
    crate::leanh::lean_dec(v_t_2253_);
    crate::leanh::lean_dec_ref(v_cmp_2252_);
    return v_res_2256_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x3f___redArg(
    mut v_cmp_2257_: *mut crate::leanh::LeanObject,
    mut v_t_2258_: *mut crate::leanh::LeanObject,
    mut v_k_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = crate::leanh::lean_box(0);
    v___x_2261_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2257_,
        v_k_2259_,
        v___x_2260_,
        v_t_2258_,
    );
    return v___x_2261_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x3f(
    mut v_00_u03b1_2262_: *mut crate::leanh::LeanObject,
    mut v_cmp_2263_: *mut crate::leanh::LeanObject,
    mut v_t_2264_: *mut crate::leanh::LeanObject,
    mut v_k_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = crate::leanh::lean_box(0);
    v___x_2267_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2263_,
        v_k_2265_,
        v___x_2266_,
        v_t_2264_,
    );
    return v___x_2267_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x3f___redArg(
    mut v_cmp_2268_: *mut crate::leanh::LeanObject,
    mut v_t_2269_: *mut crate::leanh::LeanObject,
    mut v_k_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2271_ = crate::leanh::lean_box(0);
    v___x_2272_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2268_,
        v_k_2270_,
        v___x_2271_,
        v_t_2269_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x3f(
    mut v_00_u03b1_2273_: *mut crate::leanh::LeanObject,
    mut v_cmp_2274_: *mut crate::leanh::LeanObject,
    mut v_t_2275_: *mut crate::leanh::LeanObject,
    mut v_k_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2277_ = crate::leanh::lean_box(0);
    v___x_2278_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2274_,
        v_k_2276_,
        v___x_2277_,
        v_t_2275_,
    );
    return v___x_2278_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x3f___redArg(
    mut v_cmp_2279_: *mut crate::leanh::LeanObject,
    mut v_t_2280_: *mut crate::leanh::LeanObject,
    mut v_k_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = crate::leanh::lean_box(0);
    v___x_2283_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2279_,
        v_k_2281_,
        v___x_2282_,
        v_t_2280_,
    );
    return v___x_2283_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x3f(
    mut v_00_u03b1_2284_: *mut crate::leanh::LeanObject,
    mut v_cmp_2285_: *mut crate::leanh::LeanObject,
    mut v_t_2286_: *mut crate::leanh::LeanObject,
    mut v_k_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2288_ = crate::leanh::lean_box(0);
    v___x_2289_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2285_,
        v_k_2287_,
        v___x_2288_,
        v_t_2286_,
    );
    return v___x_2289_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x3f___redArg(
    mut v_cmp_2290_: *mut crate::leanh::LeanObject,
    mut v_t_2291_: *mut crate::leanh::LeanObject,
    mut v_k_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = crate::leanh::lean_box(0);
    v___x_2294_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2290_,
        v_k_2292_,
        v___x_2293_,
        v_t_2291_,
    );
    return v___x_2294_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x3f(
    mut v_00_u03b1_2295_: *mut crate::leanh::LeanObject,
    mut v_cmp_2296_: *mut crate::leanh::LeanObject,
    mut v_t_2297_: *mut crate::leanh::LeanObject,
    mut v_k_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = crate::leanh::lean_box(0);
    v___x_2300_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2296_,
        v_k_2298_,
        v___x_2299_,
        v_t_2297_,
    );
    return v___x_2300_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = l_Std_TreeSet_Raw_getGE_x21___redArg___closed__2;
    v___x_2305_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2306_ = crate::leanh::lean_unsigned_to_nat(22);
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
    mut v_cmp_2310_: *mut crate::leanh::LeanObject,
    mut v_inst_2311_: *mut crate::leanh::LeanObject,
    mut v_t_2312_: *mut crate::leanh::LeanObject,
    mut v_k_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = crate::leanh::lean_box(0);
    v___x_2315_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2310_,
        v_k_2313_,
        v___x_2314_,
        v_t_2312_,
    );
    if crate::leanh::lean_obj_tag(v___x_2315_) == 0 {
        let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2316_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2317_ = l_panic___redArg(v_inst_2311_, v___x_2316_);
        return v___x_2317_;
    } else {
        let mut v_val_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2318_ = crate::leanh::lean_ctor_get(v___x_2315_, 0);
        crate::leanh::lean_inc(v_val_2318_);
        crate::leanh::lean_dec_ref_known(v___x_2315_, 1);
        return v_val_2318_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x21___redArg___boxed(
    mut v_cmp_2319_: *mut crate::leanh::LeanObject,
    mut v_inst_2320_: *mut crate::leanh::LeanObject,
    mut v_t_2321_: *mut crate::leanh::LeanObject,
    mut v_k_2322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2323_ =
        l_Std_TreeSet_Raw_getGE_x21___redArg(v_cmp_2319_, v_inst_2320_, v_t_2321_, v_k_2322_);
    crate::leanh::lean_dec(v_inst_2320_);
    return v_res_2323_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x21(
    mut v_00_u03b1_2324_: *mut crate::leanh::LeanObject,
    mut v_cmp_2325_: *mut crate::leanh::LeanObject,
    mut v_inst_2326_: *mut crate::leanh::LeanObject,
    mut v_t_2327_: *mut crate::leanh::LeanObject,
    mut v_k_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = crate::leanh::lean_box(0);
    v___x_2330_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2325_,
        v_k_2328_,
        v___x_2329_,
        v_t_2327_,
    );
    if crate::leanh::lean_obj_tag(v___x_2330_) == 0 {
        let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2331_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2332_ = l_panic___redArg(v_inst_2326_, v___x_2331_);
        return v___x_2332_;
    } else {
        let mut v_val_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2333_ = crate::leanh::lean_ctor_get(v___x_2330_, 0);
        crate::leanh::lean_inc(v_val_2333_);
        crate::leanh::lean_dec_ref_known(v___x_2330_, 1);
        return v_val_2333_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGE_x21___boxed(
    mut v_00_u03b1_2334_: *mut crate::leanh::LeanObject,
    mut v_cmp_2335_: *mut crate::leanh::LeanObject,
    mut v_inst_2336_: *mut crate::leanh::LeanObject,
    mut v_t_2337_: *mut crate::leanh::LeanObject,
    mut v_k_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2339_ = l_Std_TreeSet_Raw_getGE_x21(
        v_00_u03b1_2334_,
        v_cmp_2335_,
        v_inst_2336_,
        v_t_2337_,
        v_k_2338_,
    );
    crate::leanh::lean_dec(v_inst_2336_);
    return v_res_2339_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21___redArg(
    mut v_cmp_2340_: *mut crate::leanh::LeanObject,
    mut v_inst_2341_: *mut crate::leanh::LeanObject,
    mut v_t_2342_: *mut crate::leanh::LeanObject,
    mut v_k_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = crate::leanh::lean_box(0);
    v___x_2345_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2340_,
        v_k_2343_,
        v___x_2344_,
        v_t_2342_,
    );
    if crate::leanh::lean_obj_tag(v___x_2345_) == 0 {
        let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2346_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2347_ = l_panic___redArg(v_inst_2341_, v___x_2346_);
        return v___x_2347_;
    } else {
        let mut v_val_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2348_ = crate::leanh::lean_ctor_get(v___x_2345_, 0);
        crate::leanh::lean_inc(v_val_2348_);
        crate::leanh::lean_dec_ref_known(v___x_2345_, 1);
        return v_val_2348_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21___redArg___boxed(
    mut v_cmp_2349_: *mut crate::leanh::LeanObject,
    mut v_inst_2350_: *mut crate::leanh::LeanObject,
    mut v_t_2351_: *mut crate::leanh::LeanObject,
    mut v_k_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ =
        l_Std_TreeSet_Raw_getGT_x21___redArg(v_cmp_2349_, v_inst_2350_, v_t_2351_, v_k_2352_);
    crate::leanh::lean_dec(v_inst_2350_);
    return v_res_2353_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21(
    mut v_00_u03b1_2354_: *mut crate::leanh::LeanObject,
    mut v_cmp_2355_: *mut crate::leanh::LeanObject,
    mut v_inst_2356_: *mut crate::leanh::LeanObject,
    mut v_t_2357_: *mut crate::leanh::LeanObject,
    mut v_k_2358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2359_ = crate::leanh::lean_box(0);
    v___x_2360_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2355_,
        v_k_2358_,
        v___x_2359_,
        v_t_2357_,
    );
    if crate::leanh::lean_obj_tag(v___x_2360_) == 0 {
        let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2361_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2362_ = l_panic___redArg(v_inst_2356_, v___x_2361_);
        return v___x_2362_;
    } else {
        let mut v_val_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2363_ = crate::leanh::lean_ctor_get(v___x_2360_, 0);
        crate::leanh::lean_inc(v_val_2363_);
        crate::leanh::lean_dec_ref_known(v___x_2360_, 1);
        return v_val_2363_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGT_x21___boxed(
    mut v_00_u03b1_2364_: *mut crate::leanh::LeanObject,
    mut v_cmp_2365_: *mut crate::leanh::LeanObject,
    mut v_inst_2366_: *mut crate::leanh::LeanObject,
    mut v_t_2367_: *mut crate::leanh::LeanObject,
    mut v_k_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Std_TreeSet_Raw_getGT_x21(
        v_00_u03b1_2364_,
        v_cmp_2365_,
        v_inst_2366_,
        v_t_2367_,
        v_k_2368_,
    );
    crate::leanh::lean_dec(v_inst_2366_);
    return v_res_2369_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21___redArg(
    mut v_cmp_2370_: *mut crate::leanh::LeanObject,
    mut v_inst_2371_: *mut crate::leanh::LeanObject,
    mut v_t_2372_: *mut crate::leanh::LeanObject,
    mut v_k_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ = crate::leanh::lean_box(0);
    v___x_2375_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2370_,
        v_k_2373_,
        v___x_2374_,
        v_t_2372_,
    );
    if crate::leanh::lean_obj_tag(v___x_2375_) == 0 {
        let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2376_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2377_ = l_panic___redArg(v_inst_2371_, v___x_2376_);
        return v___x_2377_;
    } else {
        let mut v_val_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2378_ = crate::leanh::lean_ctor_get(v___x_2375_, 0);
        crate::leanh::lean_inc(v_val_2378_);
        crate::leanh::lean_dec_ref_known(v___x_2375_, 1);
        return v_val_2378_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21___redArg___boxed(
    mut v_cmp_2379_: *mut crate::leanh::LeanObject,
    mut v_inst_2380_: *mut crate::leanh::LeanObject,
    mut v_t_2381_: *mut crate::leanh::LeanObject,
    mut v_k_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2383_ =
        l_Std_TreeSet_Raw_getLE_x21___redArg(v_cmp_2379_, v_inst_2380_, v_t_2381_, v_k_2382_);
    crate::leanh::lean_dec(v_inst_2380_);
    return v_res_2383_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21(
    mut v_00_u03b1_2384_: *mut crate::leanh::LeanObject,
    mut v_cmp_2385_: *mut crate::leanh::LeanObject,
    mut v_inst_2386_: *mut crate::leanh::LeanObject,
    mut v_t_2387_: *mut crate::leanh::LeanObject,
    mut v_k_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ = crate::leanh::lean_box(0);
    v___x_2390_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2385_,
        v_k_2388_,
        v___x_2389_,
        v_t_2387_,
    );
    if crate::leanh::lean_obj_tag(v___x_2390_) == 0 {
        let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2391_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2392_ = l_panic___redArg(v_inst_2386_, v___x_2391_);
        return v___x_2392_;
    } else {
        let mut v_val_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2393_ = crate::leanh::lean_ctor_get(v___x_2390_, 0);
        crate::leanh::lean_inc(v_val_2393_);
        crate::leanh::lean_dec_ref_known(v___x_2390_, 1);
        return v_val_2393_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLE_x21___boxed(
    mut v_00_u03b1_2394_: *mut crate::leanh::LeanObject,
    mut v_cmp_2395_: *mut crate::leanh::LeanObject,
    mut v_inst_2396_: *mut crate::leanh::LeanObject,
    mut v_t_2397_: *mut crate::leanh::LeanObject,
    mut v_k_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Std_TreeSet_Raw_getLE_x21(
        v_00_u03b1_2394_,
        v_cmp_2395_,
        v_inst_2396_,
        v_t_2397_,
        v_k_2398_,
    );
    crate::leanh::lean_dec(v_inst_2396_);
    return v_res_2399_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21___redArg(
    mut v_cmp_2400_: *mut crate::leanh::LeanObject,
    mut v_inst_2401_: *mut crate::leanh::LeanObject,
    mut v_t_2402_: *mut crate::leanh::LeanObject,
    mut v_k_2403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2404_ = crate::leanh::lean_box(0);
    v___x_2405_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2400_,
        v_k_2403_,
        v___x_2404_,
        v_t_2402_,
    );
    if crate::leanh::lean_obj_tag(v___x_2405_) == 0 {
        let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2406_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2407_ = l_panic___redArg(v_inst_2401_, v___x_2406_);
        return v___x_2407_;
    } else {
        let mut v_val_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2408_ = crate::leanh::lean_ctor_get(v___x_2405_, 0);
        crate::leanh::lean_inc(v_val_2408_);
        crate::leanh::lean_dec_ref_known(v___x_2405_, 1);
        return v_val_2408_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21___redArg___boxed(
    mut v_cmp_2409_: *mut crate::leanh::LeanObject,
    mut v_inst_2410_: *mut crate::leanh::LeanObject,
    mut v_t_2411_: *mut crate::leanh::LeanObject,
    mut v_k_2412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ =
        l_Std_TreeSet_Raw_getLT_x21___redArg(v_cmp_2409_, v_inst_2410_, v_t_2411_, v_k_2412_);
    crate::leanh::lean_dec(v_inst_2410_);
    return v_res_2413_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21(
    mut v_00_u03b1_2414_: *mut crate::leanh::LeanObject,
    mut v_cmp_2415_: *mut crate::leanh::LeanObject,
    mut v_inst_2416_: *mut crate::leanh::LeanObject,
    mut v_t_2417_: *mut crate::leanh::LeanObject,
    mut v_k_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2419_ = crate::leanh::lean_box(0);
    v___x_2420_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2415_,
        v_k_2418_,
        v___x_2419_,
        v_t_2417_,
    );
    if crate::leanh::lean_obj_tag(v___x_2420_) == 0 {
        let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2421_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_Raw_getGE_x21___redArg___closed__3,
        );
        v___x_2422_ = l_panic___redArg(v_inst_2416_, v___x_2421_);
        return v___x_2422_;
    } else {
        let mut v_val_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2423_ = crate::leanh::lean_ctor_get(v___x_2420_, 0);
        crate::leanh::lean_inc(v_val_2423_);
        crate::leanh::lean_dec_ref_known(v___x_2420_, 1);
        return v_val_2423_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLT_x21___boxed(
    mut v_00_u03b1_2424_: *mut crate::leanh::LeanObject,
    mut v_cmp_2425_: *mut crate::leanh::LeanObject,
    mut v_inst_2426_: *mut crate::leanh::LeanObject,
    mut v_t_2427_: *mut crate::leanh::LeanObject,
    mut v_k_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Std_TreeSet_Raw_getLT_x21(
        v_00_u03b1_2424_,
        v_cmp_2425_,
        v_inst_2426_,
        v_t_2427_,
        v_k_2428_,
    );
    crate::leanh::lean_dec(v_inst_2426_);
    return v_res_2429_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGED___redArg(
    mut v_cmp_2430_: *mut crate::leanh::LeanObject,
    mut v_t_2431_: *mut crate::leanh::LeanObject,
    mut v_k_2432_: *mut crate::leanh::LeanObject,
    mut v_fallback_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2434_ = crate::leanh::lean_box(0);
    v___x_2435_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2430_,
        v_k_2432_,
        v___x_2434_,
        v_t_2431_,
    );
    if crate::leanh::lean_obj_tag(v___x_2435_) == 0 {
        crate::leanh::lean_inc(v_fallback_2433_);
        return v_fallback_2433_;
    } else {
        let mut v_val_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2436_ = crate::leanh::lean_ctor_get(v___x_2435_, 0);
        crate::leanh::lean_inc(v_val_2436_);
        crate::leanh::lean_dec_ref_known(v___x_2435_, 1);
        return v_val_2436_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGED___redArg___boxed(
    mut v_cmp_2437_: *mut crate::leanh::LeanObject,
    mut v_t_2438_: *mut crate::leanh::LeanObject,
    mut v_k_2439_: *mut crate::leanh::LeanObject,
    mut v_fallback_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ =
        l_Std_TreeSet_Raw_getGED___redArg(v_cmp_2437_, v_t_2438_, v_k_2439_, v_fallback_2440_);
    crate::leanh::lean_dec(v_fallback_2440_);
    return v_res_2441_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGED(
    mut v_00_u03b1_2442_: *mut crate::leanh::LeanObject,
    mut v_cmp_2443_: *mut crate::leanh::LeanObject,
    mut v_t_2444_: *mut crate::leanh::LeanObject,
    mut v_k_2445_: *mut crate::leanh::LeanObject,
    mut v_fallback_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = crate::leanh::lean_box(0);
    v___x_2448_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2443_,
        v_k_2445_,
        v___x_2447_,
        v_t_2444_,
    );
    if crate::leanh::lean_obj_tag(v___x_2448_) == 0 {
        crate::leanh::lean_inc(v_fallback_2446_);
        return v_fallback_2446_;
    } else {
        let mut v_val_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2449_ = crate::leanh::lean_ctor_get(v___x_2448_, 0);
        crate::leanh::lean_inc(v_val_2449_);
        crate::leanh::lean_dec_ref_known(v___x_2448_, 1);
        return v_val_2449_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGED___boxed(
    mut v_00_u03b1_2450_: *mut crate::leanh::LeanObject,
    mut v_cmp_2451_: *mut crate::leanh::LeanObject,
    mut v_t_2452_: *mut crate::leanh::LeanObject,
    mut v_k_2453_: *mut crate::leanh::LeanObject,
    mut v_fallback_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Std_TreeSet_Raw_getGED(
        v_00_u03b1_2450_,
        v_cmp_2451_,
        v_t_2452_,
        v_k_2453_,
        v_fallback_2454_,
    );
    crate::leanh::lean_dec(v_fallback_2454_);
    return v_res_2455_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD___redArg(
    mut v_cmp_2456_: *mut crate::leanh::LeanObject,
    mut v_t_2457_: *mut crate::leanh::LeanObject,
    mut v_k_2458_: *mut crate::leanh::LeanObject,
    mut v_fallback_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = crate::leanh::lean_box(0);
    v___x_2461_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2456_,
        v_k_2458_,
        v___x_2460_,
        v_t_2457_,
    );
    if crate::leanh::lean_obj_tag(v___x_2461_) == 0 {
        crate::leanh::lean_inc(v_fallback_2459_);
        return v_fallback_2459_;
    } else {
        let mut v_val_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2462_ = crate::leanh::lean_ctor_get(v___x_2461_, 0);
        crate::leanh::lean_inc(v_val_2462_);
        crate::leanh::lean_dec_ref_known(v___x_2461_, 1);
        return v_val_2462_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD___redArg___boxed(
    mut v_cmp_2463_: *mut crate::leanh::LeanObject,
    mut v_t_2464_: *mut crate::leanh::LeanObject,
    mut v_k_2465_: *mut crate::leanh::LeanObject,
    mut v_fallback_2466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2467_ =
        l_Std_TreeSet_Raw_getGTD___redArg(v_cmp_2463_, v_t_2464_, v_k_2465_, v_fallback_2466_);
    crate::leanh::lean_dec(v_fallback_2466_);
    return v_res_2467_;
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD(
    mut v_00_u03b1_2468_: *mut crate::leanh::LeanObject,
    mut v_cmp_2469_: *mut crate::leanh::LeanObject,
    mut v_t_2470_: *mut crate::leanh::LeanObject,
    mut v_k_2471_: *mut crate::leanh::LeanObject,
    mut v_fallback_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = crate::leanh::lean_box(0);
    v___x_2474_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2469_,
        v_k_2471_,
        v___x_2473_,
        v_t_2470_,
    );
    if crate::leanh::lean_obj_tag(v___x_2474_) == 0 {
        crate::leanh::lean_inc(v_fallback_2472_);
        return v_fallback_2472_;
    } else {
        let mut v_val_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2475_ = crate::leanh::lean_ctor_get(v___x_2474_, 0);
        crate::leanh::lean_inc(v_val_2475_);
        crate::leanh::lean_dec_ref_known(v___x_2474_, 1);
        return v_val_2475_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getGTD___boxed(
    mut v_00_u03b1_2476_: *mut crate::leanh::LeanObject,
    mut v_cmp_2477_: *mut crate::leanh::LeanObject,
    mut v_t_2478_: *mut crate::leanh::LeanObject,
    mut v_k_2479_: *mut crate::leanh::LeanObject,
    mut v_fallback_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Std_TreeSet_Raw_getGTD(
        v_00_u03b1_2476_,
        v_cmp_2477_,
        v_t_2478_,
        v_k_2479_,
        v_fallback_2480_,
    );
    crate::leanh::lean_dec(v_fallback_2480_);
    return v_res_2481_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLED___redArg(
    mut v_cmp_2482_: *mut crate::leanh::LeanObject,
    mut v_t_2483_: *mut crate::leanh::LeanObject,
    mut v_k_2484_: *mut crate::leanh::LeanObject,
    mut v_fallback_2485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = crate::leanh::lean_box(0);
    v___x_2487_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2482_,
        v_k_2484_,
        v___x_2486_,
        v_t_2483_,
    );
    if crate::leanh::lean_obj_tag(v___x_2487_) == 0 {
        crate::leanh::lean_inc(v_fallback_2485_);
        return v_fallback_2485_;
    } else {
        let mut v_val_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2488_ = crate::leanh::lean_ctor_get(v___x_2487_, 0);
        crate::leanh::lean_inc(v_val_2488_);
        crate::leanh::lean_dec_ref_known(v___x_2487_, 1);
        return v_val_2488_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLED___redArg___boxed(
    mut v_cmp_2489_: *mut crate::leanh::LeanObject,
    mut v_t_2490_: *mut crate::leanh::LeanObject,
    mut v_k_2491_: *mut crate::leanh::LeanObject,
    mut v_fallback_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ =
        l_Std_TreeSet_Raw_getLED___redArg(v_cmp_2489_, v_t_2490_, v_k_2491_, v_fallback_2492_);
    crate::leanh::lean_dec(v_fallback_2492_);
    return v_res_2493_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLED(
    mut v_00_u03b1_2494_: *mut crate::leanh::LeanObject,
    mut v_cmp_2495_: *mut crate::leanh::LeanObject,
    mut v_t_2496_: *mut crate::leanh::LeanObject,
    mut v_k_2497_: *mut crate::leanh::LeanObject,
    mut v_fallback_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ = crate::leanh::lean_box(0);
    v___x_2500_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2495_,
        v_k_2497_,
        v___x_2499_,
        v_t_2496_,
    );
    if crate::leanh::lean_obj_tag(v___x_2500_) == 0 {
        crate::leanh::lean_inc(v_fallback_2498_);
        return v_fallback_2498_;
    } else {
        let mut v_val_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2501_ = crate::leanh::lean_ctor_get(v___x_2500_, 0);
        crate::leanh::lean_inc(v_val_2501_);
        crate::leanh::lean_dec_ref_known(v___x_2500_, 1);
        return v_val_2501_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLED___boxed(
    mut v_00_u03b1_2502_: *mut crate::leanh::LeanObject,
    mut v_cmp_2503_: *mut crate::leanh::LeanObject,
    mut v_t_2504_: *mut crate::leanh::LeanObject,
    mut v_k_2505_: *mut crate::leanh::LeanObject,
    mut v_fallback_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2507_ = l_Std_TreeSet_Raw_getLED(
        v_00_u03b1_2502_,
        v_cmp_2503_,
        v_t_2504_,
        v_k_2505_,
        v_fallback_2506_,
    );
    crate::leanh::lean_dec(v_fallback_2506_);
    return v_res_2507_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD___redArg(
    mut v_cmp_2508_: *mut crate::leanh::LeanObject,
    mut v_t_2509_: *mut crate::leanh::LeanObject,
    mut v_k_2510_: *mut crate::leanh::LeanObject,
    mut v_fallback_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2512_ = crate::leanh::lean_box(0);
    v___x_2513_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2508_,
        v_k_2510_,
        v___x_2512_,
        v_t_2509_,
    );
    if crate::leanh::lean_obj_tag(v___x_2513_) == 0 {
        crate::leanh::lean_inc(v_fallback_2511_);
        return v_fallback_2511_;
    } else {
        let mut v_val_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2514_ = crate::leanh::lean_ctor_get(v___x_2513_, 0);
        crate::leanh::lean_inc(v_val_2514_);
        crate::leanh::lean_dec_ref_known(v___x_2513_, 1);
        return v_val_2514_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD___redArg___boxed(
    mut v_cmp_2515_: *mut crate::leanh::LeanObject,
    mut v_t_2516_: *mut crate::leanh::LeanObject,
    mut v_k_2517_: *mut crate::leanh::LeanObject,
    mut v_fallback_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2519_ =
        l_Std_TreeSet_Raw_getLTD___redArg(v_cmp_2515_, v_t_2516_, v_k_2517_, v_fallback_2518_);
    crate::leanh::lean_dec(v_fallback_2518_);
    return v_res_2519_;
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD(
    mut v_00_u03b1_2520_: *mut crate::leanh::LeanObject,
    mut v_cmp_2521_: *mut crate::leanh::LeanObject,
    mut v_t_2522_: *mut crate::leanh::LeanObject,
    mut v_k_2523_: *mut crate::leanh::LeanObject,
    mut v_fallback_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ = crate::leanh::lean_box(0);
    v___x_2526_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2521_,
        v_k_2523_,
        v___x_2525_,
        v_t_2522_,
    );
    if crate::leanh::lean_obj_tag(v___x_2526_) == 0 {
        crate::leanh::lean_inc(v_fallback_2524_);
        return v_fallback_2524_;
    } else {
        let mut v_val_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2527_ = crate::leanh::lean_ctor_get(v___x_2526_, 0);
        crate::leanh::lean_inc(v_val_2527_);
        crate::leanh::lean_dec_ref_known(v___x_2526_, 1);
        return v_val_2527_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_getLTD___boxed(
    mut v_00_u03b1_2528_: *mut crate::leanh::LeanObject,
    mut v_cmp_2529_: *mut crate::leanh::LeanObject,
    mut v_t_2530_: *mut crate::leanh::LeanObject,
    mut v_k_2531_: *mut crate::leanh::LeanObject,
    mut v_fallback_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Std_TreeSet_Raw_getLTD(
        v_00_u03b1_2528_,
        v_cmp_2529_,
        v_t_2530_,
        v_k_2531_,
        v_fallback_2532_,
    );
    crate::leanh::lean_dec(v_fallback_2532_);
    return v_res_2533_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___redArg___lam__0(
    mut v_f_2534_: *mut crate::leanh::LeanObject,
    mut v_a_2535_: *mut crate::leanh::LeanObject,
    mut v_x_2536_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    v___x_2537_ = crate::leanh::lean_apply_1(v_f_2534_, v_a_2535_);
    v___x_2538_ = (crate::leanh::lean_unbox(v___x_2537_) as u8);
    return v___x_2538_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed(
    mut v_f_2539_: *mut crate::leanh::LeanObject,
    mut v_a_2540_: *mut crate::leanh::LeanObject,
    mut v_x_2541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2542_: u8 = 0;
    let mut v_r_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2542_ = l_Std_TreeSet_Raw_filter___redArg___lam__0(v_f_2539_, v_a_2540_, v_x_2541_);
    v_r_2543_ = crate::leanh::lean_box((v_res_2542_) as usize);
    return v_r_2543_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___redArg(
    mut v_f_2544_: *mut crate::leanh::LeanObject,
    mut v_t_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2546_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2546_, 0, v_f_2544_);
    v___x_2547_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_2546_, v_t_2545_);
    return v___x_2547_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter(
    mut v_00_u03b1_2548_: *mut crate::leanh::LeanObject,
    mut v_cmp_2549_: *mut crate::leanh::LeanObject,
    mut v_f_2550_: *mut crate::leanh::LeanObject,
    mut v_t_2551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2552_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2552_, 0, v_f_2550_);
    v___x_2553_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v___f_2552_, v_t_2551_);
    return v___x_2553_;
}
pub unsafe fn l_Std_TreeSet_Raw_filter___boxed(
    mut v_00_u03b1_2554_: *mut crate::leanh::LeanObject,
    mut v_cmp_2555_: *mut crate::leanh::LeanObject,
    mut v_f_2556_: *mut crate::leanh::LeanObject,
    mut v_t_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2558_ = l_Std_TreeSet_Raw_filter(v_00_u03b1_2554_, v_cmp_2555_, v_f_2556_, v_t_2557_);
    crate::leanh::lean_dec_ref(v_cmp_2555_);
    return v_res_2558_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM___redArg___lam__0(
    mut v_f_2559_: *mut crate::leanh::LeanObject,
    mut v_c_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
    mut v_x_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2563_ = crate::leanh::lean_apply_2(v_f_2559_, v_c_2560_, v_a_2561_);
    return v___x_2563_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM___redArg(
    mut v_inst_2564_: *mut crate::leanh::LeanObject,
    mut v_f_2565_: *mut crate::leanh::LeanObject,
    mut v_init_2566_: *mut crate::leanh::LeanObject,
    mut v_t_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2568_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2568_, 0, v_f_2565_);
    v___x_2569_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2564_,
        v___f_2568_,
        v_init_2566_,
        v_t_2567_,
    );
    return v___x_2569_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM(
    mut v_00_u03b1_2570_: *mut crate::leanh::LeanObject,
    mut v_cmp_2571_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2572_: *mut crate::leanh::LeanObject,
    mut v_m_2573_: *mut crate::leanh::LeanObject,
    mut v_inst_2574_: *mut crate::leanh::LeanObject,
    mut v_f_2575_: *mut crate::leanh::LeanObject,
    mut v_init_2576_: *mut crate::leanh::LeanObject,
    mut v_t_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2578_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2578_, 0, v_f_2575_);
    v___x_2579_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2574_,
        v___f_2578_,
        v_init_2576_,
        v_t_2577_,
    );
    return v___x_2579_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldlM___boxed(
    mut v_00_u03b1_2580_: *mut crate::leanh::LeanObject,
    mut v_cmp_2581_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2582_: *mut crate::leanh::LeanObject,
    mut v_m_2583_: *mut crate::leanh::LeanObject,
    mut v_inst_2584_: *mut crate::leanh::LeanObject,
    mut v_f_2585_: *mut crate::leanh::LeanObject,
    mut v_init_2586_: *mut crate::leanh::LeanObject,
    mut v_t_2587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_2581_);
    return v_res_2588_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldl___redArg(
    mut v_f_2589_: *mut crate::leanh::LeanObject,
    mut v_init_2590_: *mut crate::leanh::LeanObject,
    mut v_t_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2592_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2592_, 0, v_f_2589_);
    v___x_2593_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2592_, v_init_2590_, v_t_2591_);
    return v___x_2593_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldl(
    mut v_00_u03b1_2594_: *mut crate::leanh::LeanObject,
    mut v_cmp_2595_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2596_: *mut crate::leanh::LeanObject,
    mut v_f_2597_: *mut crate::leanh::LeanObject,
    mut v_init_2598_: *mut crate::leanh::LeanObject,
    mut v_t_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2600_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2600_, 0, v_f_2597_);
    v___x_2601_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2600_, v_init_2598_, v_t_2599_);
    return v___x_2601_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldl___boxed(
    mut v_00_u03b1_2602_: *mut crate::leanh::LeanObject,
    mut v_cmp_2603_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2604_: *mut crate::leanh::LeanObject,
    mut v_f_2605_: *mut crate::leanh::LeanObject,
    mut v_init_2606_: *mut crate::leanh::LeanObject,
    mut v_t_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2608_ = l_Std_TreeSet_Raw_foldl(
        v_00_u03b1_2602_,
        v_cmp_2603_,
        v_00_u03b4_2604_,
        v_f_2605_,
        v_init_2606_,
        v_t_2607_,
    );
    crate::leanh::lean_dec_ref(v_cmp_2603_);
    return v_res_2608_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM___redArg___lam__0(
    mut v_f_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_x_2611_: *mut crate::leanh::LeanObject,
    mut v_acc_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = crate::leanh::lean_apply_2(v_f_2609_, v_a_2610_, v_acc_2612_);
    return v___x_2613_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM___redArg(
    mut v_inst_2614_: *mut crate::leanh::LeanObject,
    mut v_f_2615_: *mut crate::leanh::LeanObject,
    mut v_init_2616_: *mut crate::leanh::LeanObject,
    mut v_t_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2618_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2618_, 0, v_f_2615_);
    v___x_2619_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2614_,
        v___f_2618_,
        v_init_2616_,
        v_t_2617_,
    );
    return v___x_2619_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM(
    mut v_00_u03b1_2620_: *mut crate::leanh::LeanObject,
    mut v_cmp_2621_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2622_: *mut crate::leanh::LeanObject,
    mut v_m_2623_: *mut crate::leanh::LeanObject,
    mut v_inst_2624_: *mut crate::leanh::LeanObject,
    mut v_f_2625_: *mut crate::leanh::LeanObject,
    mut v_init_2626_: *mut crate::leanh::LeanObject,
    mut v_t_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2628_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2628_, 0, v_f_2625_);
    v___x_2629_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_2624_,
        v___f_2628_,
        v_init_2626_,
        v_t_2627_,
    );
    return v___x_2629_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldrM___boxed(
    mut v_00_u03b1_2630_: *mut crate::leanh::LeanObject,
    mut v_cmp_2631_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2632_: *mut crate::leanh::LeanObject,
    mut v_m_2633_: *mut crate::leanh::LeanObject,
    mut v_inst_2634_: *mut crate::leanh::LeanObject,
    mut v_f_2635_: *mut crate::leanh::LeanObject,
    mut v_init_2636_: *mut crate::leanh::LeanObject,
    mut v_t_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_2631_);
    return v_res_2638_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldr___redArg___lam__0(
    mut v_f_2639_: *mut crate::leanh::LeanObject,
    mut v_x1_2640_: *mut crate::leanh::LeanObject,
    mut v_x2_2641_: *mut crate::leanh::LeanObject,
    mut v_x3_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2643_ = crate::leanh::lean_apply_2(v_f_2639_, v_x1_2640_, v_x3_2642_);
    return v___x_2643_;
}
pub unsafe fn l_Std_TreeSet_Raw_foldr___redArg(
    mut v_f_2663_: *mut crate::leanh::LeanObject,
    mut v_init_2664_: *mut crate::leanh::LeanObject,
    mut v_t_2665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2666_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2666_, 0, v_f_2663_);
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
    mut v_00_u03b1_2669_: *mut crate::leanh::LeanObject,
    mut v_cmp_2670_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2671_: *mut crate::leanh::LeanObject,
    mut v_f_2672_: *mut crate::leanh::LeanObject,
    mut v_init_2673_: *mut crate::leanh::LeanObject,
    mut v_t_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2675_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2675_, 0, v_f_2672_);
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
    mut v_00_u03b1_2678_: *mut crate::leanh::LeanObject,
    mut v_cmp_2679_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2680_: *mut crate::leanh::LeanObject,
    mut v_f_2681_: *mut crate::leanh::LeanObject,
    mut v_init_2682_: *mut crate::leanh::LeanObject,
    mut v_t_2683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2684_ = l_Std_TreeSet_Raw_foldr(
        v_00_u03b1_2678_,
        v_cmp_2679_,
        v_00_u03b4_2680_,
        v_f_2681_,
        v_init_2682_,
        v_t_2683_,
    );
    crate::leanh::lean_dec_ref(v_cmp_2679_);
    return v_res_2684_;
}
pub unsafe fn l_Std_TreeSet_Raw_partition___redArg___lam__0(
    mut v_f_2685_: *mut crate::leanh::LeanObject,
    mut v_cmp_2686_: *mut crate::leanh::LeanObject,
    mut v_x_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_b_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2690_ = crate::leanh::lean_ctor_get(v_x_2687_, 0);
                v_snd_2691_ = crate::leanh::lean_ctor_get(v_x_2687_, 1);
                v_isSharedCheck_2705_ = (!crate::leanh::lean_is_exclusive(v_x_2687_)) as u8;
                if v_isSharedCheck_2705_ == 0 {
                    v___x_2693_ = v_x_2687_;
                    v_isShared_2694_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2691_);
                    crate::leanh::lean_inc(v_fst_2690_);
                    crate::leanh::lean_dec(v_x_2687_);
                    v___x_2693_ = crate::leanh::lean_box(0);
                    v_isShared_2694_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2688_);
                v___x_2695_ = crate::leanh::lean_apply_1(v_f_2685_, v_a_2688_);
                v___x_2696_ = (crate::leanh::lean_unbox(v___x_2695_) as u8);
                if v___x_2696_ == 0 {
                    v___x_2697_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                        v_cmp_2686_,
                        v_a_2688_,
                        v_b_2689_,
                        v_snd_2691_,
                    );
                    if v_isShared_2694_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2693_, 1, v___x_2697_);
                        v___x_2699_ = v___x_2693_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_fst_2690_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2697_);
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
                        crate::leanh::lean_ctor_set(v___x_2693_, 0, v___x_2701_);
                        v___x_2703_ = v___x_2693_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2704_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_snd_2691_);
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
    mut v_cmp_2708_: *mut crate::leanh::LeanObject,
    mut v_f_2709_: *mut crate::leanh::LeanObject,
    mut v_t_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2711_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_Raw_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2711_, 0, v_f_2709_);
                crate::leanh::lean_closure_set(v___f_2711_, 1, v_cmp_2708_);
                v___x_2712_ = l_Std_TreeSet_Raw_partition___redArg___closed__0;
                v_p_2713_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_2711_,
                    v___x_2712_,
                    v_t_2710_,
                );
                v_fst_2714_ = crate::leanh::lean_ctor_get(v_p_2713_, 0);
                v_snd_2715_ = crate::leanh::lean_ctor_get(v_p_2713_, 1);
                v_isSharedCheck_2722_ = (!crate::leanh::lean_is_exclusive(v_p_2713_)) as u8;
                if v_isSharedCheck_2722_ == 0 {
                    v___x_2717_ = v_p_2713_;
                    v_isShared_2718_ = v_isSharedCheck_2722_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2715_);
                    crate::leanh::lean_inc(v_fst_2714_);
                    crate::leanh::lean_dec(v_p_2713_);
                    v___x_2717_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2721_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_fst_2714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_snd_2715_);
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
    mut v_00_u03b1_2723_: *mut crate::leanh::LeanObject,
    mut v_cmp_2724_: *mut crate::leanh::LeanObject,
    mut v_f_2725_: *mut crate::leanh::LeanObject,
    mut v_t_2726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2727_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_Raw_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2727_, 0, v_f_2725_);
                crate::leanh::lean_closure_set(v___f_2727_, 1, v_cmp_2724_);
                v___x_2728_ = l_Std_TreeSet_Raw_partition___redArg___closed__0;
                v_p_2729_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_2727_,
                    v___x_2728_,
                    v_t_2726_,
                );
                v_fst_2730_ = crate::leanh::lean_ctor_get(v_p_2729_, 0);
                v_snd_2731_ = crate::leanh::lean_ctor_get(v_p_2729_, 1);
                v_isSharedCheck_2738_ = (!crate::leanh::lean_is_exclusive(v_p_2729_)) as u8;
                if v_isSharedCheck_2738_ == 0 {
                    v___x_2733_ = v_p_2729_;
                    v_isShared_2734_ = v_isSharedCheck_2738_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2731_);
                    crate::leanh::lean_inc(v_fst_2730_);
                    crate::leanh::lean_dec(v_p_2729_);
                    v___x_2733_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2737_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_fst_2730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_snd_2731_);
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
    mut v_f_2739_: *mut crate::leanh::LeanObject,
    mut v_x_2740_: *mut crate::leanh::LeanObject,
    mut v_k_2741_: *mut crate::leanh::LeanObject,
    mut v_v_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2743_ = crate::leanh::lean_apply_1(v_f_2739_, v_k_2741_);
    return v___x_2743_;
}
pub unsafe fn l_Std_TreeSet_Raw_forM___redArg(
    mut v_inst_2744_: *mut crate::leanh::LeanObject,
    mut v_f_2745_: *mut crate::leanh::LeanObject,
    mut v_t_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2747_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2747_, 0, v_f_2745_);
    v___x_2748_ = crate::leanh::lean_box(0);
    v___x_2749_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2744_,
        v___f_2747_,
        v___x_2748_,
        v_t_2746_,
    );
    return v___x_2749_;
}
pub unsafe fn l_Std_TreeSet_Raw_forM(
    mut v_00_u03b1_2750_: *mut crate::leanh::LeanObject,
    mut v_cmp_2751_: *mut crate::leanh::LeanObject,
    mut v_m_2752_: *mut crate::leanh::LeanObject,
    mut v_inst_2753_: *mut crate::leanh::LeanObject,
    mut v_f_2754_: *mut crate::leanh::LeanObject,
    mut v_t_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2756_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2756_, 0, v_f_2754_);
    v___x_2757_ = crate::leanh::lean_box(0);
    v___x_2758_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2753_,
        v___f_2756_,
        v___x_2757_,
        v_t_2755_,
    );
    return v___x_2758_;
}
pub unsafe fn l_Std_TreeSet_Raw_forM___boxed(
    mut v_00_u03b1_2759_: *mut crate::leanh::LeanObject,
    mut v_cmp_2760_: *mut crate::leanh::LeanObject,
    mut v_m_2761_: *mut crate::leanh::LeanObject,
    mut v_inst_2762_: *mut crate::leanh::LeanObject,
    mut v_f_2763_: *mut crate::leanh::LeanObject,
    mut v_t_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2765_ = l_Std_TreeSet_Raw_forM(
        v_00_u03b1_2759_,
        v_cmp_2760_,
        v_m_2761_,
        v_inst_2762_,
        v_f_2763_,
        v_t_2764_,
    );
    crate::leanh::lean_dec_ref(v_cmp_2760_);
    return v_res_2765_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___redArg___lam__0(
    mut v_f_2766_: *mut crate::leanh::LeanObject,
    mut v_a_2767_: *mut crate::leanh::LeanObject,
    mut v_b_2768_: *mut crate::leanh::LeanObject,
    mut v_c_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = crate::leanh::lean_apply_2(v_f_2766_, v_a_2767_, v_c_2769_);
    return v___x_2770_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___redArg___lam__1(
    mut v_toPure_2771_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_2773_ = crate::leanh::lean_ctor_get(v_____do__lift_2772_, 0);
    crate::leanh::lean_inc(v_a_2773_);
    crate::leanh::lean_dec_ref(v_____do__lift_2772_);
    v___x_2774_ = crate::leanh::lean_apply_2(v_toPure_2771_, crate::leanh::lean_box(0), v_a_2773_);
    return v___x_2774_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___redArg(
    mut v_inst_2775_: *mut crate::leanh::LeanObject,
    mut v_f_2776_: *mut crate::leanh::LeanObject,
    mut v_init_2777_: *mut crate::leanh::LeanObject,
    mut v_t_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2779_ = crate::leanh::lean_ctor_get(v_inst_2775_, 0);
    v_toBind_2780_ = crate::leanh::lean_ctor_get(v_inst_2775_, 1);
    crate::leanh::lean_inc(v_toBind_2780_);
    v_toPure_2781_ = crate::leanh::lean_ctor_get(v_toApplicative_2779_, 1);
    crate::leanh::lean_inc(v_toPure_2781_);
    v___f_2782_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2782_, 0, v_f_2776_);
    v___x_2783_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2775_,
        v___f_2782_,
        v_init_2777_,
        v_t_2778_,
    );
    v___f_2784_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2784_, 0, v_toPure_2781_);
    v___x_2785_ = crate::leanh::lean_apply_4(
        v_toBind_2780_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2783_,
        v___f_2784_,
    );
    return v___x_2785_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn(
    mut v_00_u03b1_2786_: *mut crate::leanh::LeanObject,
    mut v_cmp_2787_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2788_: *mut crate::leanh::LeanObject,
    mut v_m_2789_: *mut crate::leanh::LeanObject,
    mut v_inst_2790_: *mut crate::leanh::LeanObject,
    mut v_f_2791_: *mut crate::leanh::LeanObject,
    mut v_init_2792_: *mut crate::leanh::LeanObject,
    mut v_t_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2794_ = crate::leanh::lean_ctor_get(v_inst_2790_, 0);
    v_toBind_2795_ = crate::leanh::lean_ctor_get(v_inst_2790_, 1);
    crate::leanh::lean_inc(v_toBind_2795_);
    v_toPure_2796_ = crate::leanh::lean_ctor_get(v_toApplicative_2794_, 1);
    crate::leanh::lean_inc(v_toPure_2796_);
    v___f_2797_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2797_, 0, v_f_2791_);
    v___x_2798_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2790_,
        v___f_2797_,
        v_init_2792_,
        v_t_2793_,
    );
    v___f_2799_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2799_, 0, v_toPure_2796_);
    v___x_2800_ = crate::leanh::lean_apply_4(
        v_toBind_2795_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2798_,
        v___f_2799_,
    );
    return v___x_2800_;
}
pub unsafe fn l_Std_TreeSet_Raw_forIn___boxed(
    mut v_00_u03b1_2801_: *mut crate::leanh::LeanObject,
    mut v_cmp_2802_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2803_: *mut crate::leanh::LeanObject,
    mut v_m_2804_: *mut crate::leanh::LeanObject,
    mut v_inst_2805_: *mut crate::leanh::LeanObject,
    mut v_f_2806_: *mut crate::leanh::LeanObject,
    mut v_init_2807_: *mut crate::leanh::LeanObject,
    mut v_t_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_2802_);
    return v_res_2809_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1(
    mut v_inst_2810_: *mut crate::leanh::LeanObject,
    mut v_t_2811_: *mut crate::leanh::LeanObject,
    mut v_f_2812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2813_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2813_, 0, v_f_2812_);
    v___x_2814_ = crate::leanh::lean_box(0);
    v___x_2815_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_2810_,
        v___f_2813_,
        v___x_2814_,
        v_t_2811_,
    );
    return v___x_2815_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad___redArg(
    mut v_inst_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2817_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2817_, 0, v_inst_2816_);
    return v___f_2817_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad(
    mut v_00_u03b1_2818_: *mut crate::leanh::LeanObject,
    mut v_cmp_2819_: *mut crate::leanh::LeanObject,
    mut v_m_2820_: *mut crate::leanh::LeanObject,
    mut v_inst_2821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2822_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2822_, 0, v_inst_2821_);
    return v___f_2822_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForMOfMonad___boxed(
    mut v_00_u03b1_2823_: *mut crate::leanh::LeanObject,
    mut v_cmp_2824_: *mut crate::leanh::LeanObject,
    mut v_m_2825_: *mut crate::leanh::LeanObject,
    mut v_inst_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ =
        l_Std_TreeSet_Raw_instForMOfMonad(v_00_u03b1_2823_, v_cmp_2824_, v_m_2825_, v_inst_2826_);
    crate::leanh::lean_dec_ref(v_cmp_2824_);
    return v_res_2827_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2(
    mut v_inst_2828_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2829_: *mut crate::leanh::LeanObject,
    mut v_t_2830_: *mut crate::leanh::LeanObject,
    mut v_init_2831_: *mut crate::leanh::LeanObject,
    mut v_f_2832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2833_ = crate::leanh::lean_ctor_get(v_inst_2828_, 0);
    v_toBind_2834_ = crate::leanh::lean_ctor_get(v_inst_2828_, 1);
    crate::leanh::lean_inc(v_toBind_2834_);
    v_toPure_2835_ = crate::leanh::lean_ctor_get(v_toApplicative_2833_, 1);
    crate::leanh::lean_inc(v_toPure_2835_);
    v___f_2836_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2836_, 0, v_f_2832_);
    v___x_2837_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2828_,
        v___f_2836_,
        v_init_2831_,
        v_t_2830_,
    );
    v___f_2838_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2838_, 0, v_toPure_2835_);
    v___x_2839_ = crate::leanh::lean_apply_4(
        v_toBind_2834_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2837_,
        v___f_2838_,
    );
    return v___x_2839_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad___redArg(
    mut v_inst_2840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2841_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2841_, 0, v_inst_2840_);
    return v___f_2841_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad(
    mut v_00_u03b1_2842_: *mut crate::leanh::LeanObject,
    mut v_cmp_2843_: *mut crate::leanh::LeanObject,
    mut v_m_2844_: *mut crate::leanh::LeanObject,
    mut v_inst_2845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2846_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2846_, 0, v_inst_2845_);
    return v___f_2846_;
}
pub unsafe fn l_Std_TreeSet_Raw_instForInOfMonad___boxed(
    mut v_00_u03b1_2847_: *mut crate::leanh::LeanObject,
    mut v_cmp_2848_: *mut crate::leanh::LeanObject,
    mut v_m_2849_: *mut crate::leanh::LeanObject,
    mut v_inst_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2851_ =
        l_Std_TreeSet_Raw_instForInOfMonad(v_00_u03b1_2847_, v_cmp_2848_, v_m_2849_, v_inst_2850_);
    crate::leanh::lean_dec_ref(v_cmp_2848_);
    return v_res_2851_;
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg___lam__0(
    mut v_p_2852_: *mut crate::leanh::LeanObject,
    mut v___x_2853_: *mut crate::leanh::LeanObject,
    mut v___x_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: *mut crate::leanh::LeanObject,
    mut v_b_2856_: *mut crate::leanh::LeanObject,
    mut v_acc_2857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    v___x_2858_ = crate::leanh::lean_apply_1(v_p_2852_, v_a_2855_);
    v___x_2859_ = (crate::leanh::lean_unbox(v___x_2858_) as u8);
    if v___x_2859_ == 0 {
        let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2860_, 0, v___x_2853_);
        return v___x_2860_;
    } else {
        let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2853_);
        v___x_2861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2861_, 0, v___x_2858_);
        v___x_2862_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2862_, 0, v___x_2861_);
        crate::leanh::lean_ctor_set(v___x_2862_, 1, v___x_2854_);
        v___x_2863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2863_, 0, v___x_2862_);
        return v___x_2863_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg___lam__0___boxed(
    mut v_p_2864_: *mut crate::leanh::LeanObject,
    mut v___x_2865_: *mut crate::leanh::LeanObject,
    mut v___x_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_b_2868_: *mut crate::leanh::LeanObject,
    mut v_acc_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2870_ = l_Std_TreeSet_Raw_any___redArg___lam__0(
        v_p_2864_,
        v___x_2865_,
        v___x_2866_,
        v_a_2867_,
        v_b_2868_,
        v_acc_2869_,
    );
    crate::leanh::lean_dec_ref(v_acc_2869_);
    return v_res_2870_;
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg(
    mut v_t_2874_: *mut crate::leanh::LeanObject,
    mut v_p_2875_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: u8 = 0;
    let mut v_val_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2882_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2883_ = crate::leanh::lean_box(0);
                v___x_2884_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2885_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2885_, 0, v_p_2875_);
                crate::leanh::lean_closure_set(v___f_2885_, 1, v___x_2884_);
                crate::leanh::lean_closure_set(v___f_2885_, 2, v___x_2883_);
                v___x_2886_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2882_,
                    v___f_2885_,
                    v___x_2884_,
                    v_t_2874_,
                );
                v_a_2887_ = crate::leanh::lean_ctor_get(v___x_2886_, 0);
                crate::leanh::lean_inc(v_a_2887_);
                crate::leanh::lean_dec(v___x_2886_);
                v___y_2877_ = v_a_2887_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2878_ = crate::leanh::lean_ctor_get(v___y_2877_, 0);
                crate::leanh::lean_inc(v_fst_2878_);
                crate::leanh::lean_dec_ref(v___y_2877_);
                if crate::leanh::lean_obj_tag(v_fst_2878_) == 0 {
                    v___x_2879_ = 0;
                    return v___x_2879_;
                } else {
                    v_val_2880_ = crate::leanh::lean_ctor_get(v_fst_2878_, 0);
                    crate::leanh::lean_inc(v_val_2880_);
                    crate::leanh::lean_dec_ref_known(v_fst_2878_, 1);
                    v___x_2881_ = (crate::leanh::lean_unbox(v_val_2880_) as u8);
                    crate::leanh::lean_dec(v_val_2880_);
                    return v___x_2881_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_any___redArg___boxed(
    mut v_t_2888_: *mut crate::leanh::LeanObject,
    mut v_p_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2890_: u8 = 0;
    let mut v_r_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_Std_TreeSet_Raw_any___redArg(v_t_2888_, v_p_2889_);
    v_r_2891_ = crate::leanh::lean_box((v_res_2890_) as usize);
    return v_r_2891_;
}
pub unsafe fn l_Std_TreeSet_Raw_any(
    mut v_00_u03b1_2892_: *mut crate::leanh::LeanObject,
    mut v_cmp_2893_: *mut crate::leanh::LeanObject,
    mut v_t_2894_: *mut crate::leanh::LeanObject,
    mut v_p_2895_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u8 = 0;
    let mut v_val_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2902_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2903_ = crate::leanh::lean_box(0);
                v___x_2904_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2905_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2905_, 0, v_p_2895_);
                crate::leanh::lean_closure_set(v___f_2905_, 1, v___x_2904_);
                crate::leanh::lean_closure_set(v___f_2905_, 2, v___x_2903_);
                v___x_2906_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2902_,
                    v___f_2905_,
                    v___x_2904_,
                    v_t_2894_,
                );
                v_a_2907_ = crate::leanh::lean_ctor_get(v___x_2906_, 0);
                crate::leanh::lean_inc(v_a_2907_);
                crate::leanh::lean_dec(v___x_2906_);
                v___y_2897_ = v_a_2907_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2898_ = crate::leanh::lean_ctor_get(v___y_2897_, 0);
                crate::leanh::lean_inc(v_fst_2898_);
                crate::leanh::lean_dec_ref(v___y_2897_);
                if crate::leanh::lean_obj_tag(v_fst_2898_) == 0 {
                    v___x_2899_ = 0;
                    return v___x_2899_;
                } else {
                    v_val_2900_ = crate::leanh::lean_ctor_get(v_fst_2898_, 0);
                    crate::leanh::lean_inc(v_val_2900_);
                    crate::leanh::lean_dec_ref_known(v_fst_2898_, 1);
                    v___x_2901_ = (crate::leanh::lean_unbox(v_val_2900_) as u8);
                    crate::leanh::lean_dec(v_val_2900_);
                    return v___x_2901_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_any___boxed(
    mut v_00_u03b1_2908_: *mut crate::leanh::LeanObject,
    mut v_cmp_2909_: *mut crate::leanh::LeanObject,
    mut v_t_2910_: *mut crate::leanh::LeanObject,
    mut v_p_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2912_: u8 = 0;
    let mut v_r_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2912_ = l_Std_TreeSet_Raw_any(v_00_u03b1_2908_, v_cmp_2909_, v_t_2910_, v_p_2911_);
    crate::leanh::lean_dec_ref(v_cmp_2909_);
    v_r_2913_ = crate::leanh::lean_box((v_res_2912_) as usize);
    return v_r_2913_;
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg___lam__0(
    mut v_p_2914_: *mut crate::leanh::LeanObject,
    mut v___x_2915_: *mut crate::leanh::LeanObject,
    mut v___x_2916_: *mut crate::leanh::LeanObject,
    mut v_a_2917_: *mut crate::leanh::LeanObject,
    mut v_b_2918_: *mut crate::leanh::LeanObject,
    mut v_acc_2919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    v___x_2920_ = crate::leanh::lean_apply_1(v_p_2914_, v_a_2917_);
    v___x_2921_ = (crate::leanh::lean_unbox(v___x_2920_) as u8);
    if v___x_2921_ == 0 {
        let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2916_);
        v___x_2922_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2922_, 0, v___x_2920_);
        v___x_2923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2923_, 0, v___x_2922_);
        crate::leanh::lean_ctor_set(v___x_2923_, 1, v___x_2915_);
        v___x_2924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2924_, 0, v___x_2923_);
        return v___x_2924_;
    } else {
        let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2925_, 0, v___x_2916_);
        return v___x_2925_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg___lam__0___boxed(
    mut v_p_2926_: *mut crate::leanh::LeanObject,
    mut v___x_2927_: *mut crate::leanh::LeanObject,
    mut v___x_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_b_2930_: *mut crate::leanh::LeanObject,
    mut v_acc_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Std_TreeSet_Raw_all___redArg___lam__0(
        v_p_2926_,
        v___x_2927_,
        v___x_2928_,
        v_a_2929_,
        v_b_2930_,
        v_acc_2931_,
    );
    crate::leanh::lean_dec_ref(v_acc_2931_);
    return v_res_2932_;
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg(
    mut v_t_2933_: *mut crate::leanh::LeanObject,
    mut v_p_2934_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v_val_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2941_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2942_ = crate::leanh::lean_box(0);
                v___x_2943_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2944_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2944_, 0, v_p_2934_);
                crate::leanh::lean_closure_set(v___f_2944_, 1, v___x_2942_);
                crate::leanh::lean_closure_set(v___f_2944_, 2, v___x_2943_);
                v___x_2945_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2941_,
                    v___f_2944_,
                    v___x_2943_,
                    v_t_2933_,
                );
                v_a_2946_ = crate::leanh::lean_ctor_get(v___x_2945_, 0);
                crate::leanh::lean_inc(v_a_2946_);
                crate::leanh::lean_dec(v___x_2945_);
                v___y_2936_ = v_a_2946_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2937_ = crate::leanh::lean_ctor_get(v___y_2936_, 0);
                crate::leanh::lean_inc(v_fst_2937_);
                crate::leanh::lean_dec_ref(v___y_2936_);
                if crate::leanh::lean_obj_tag(v_fst_2937_) == 0 {
                    v___x_2938_ = 1;
                    return v___x_2938_;
                } else {
                    v_val_2939_ = crate::leanh::lean_ctor_get(v_fst_2937_, 0);
                    crate::leanh::lean_inc(v_val_2939_);
                    crate::leanh::lean_dec_ref_known(v_fst_2937_, 1);
                    v___x_2940_ = (crate::leanh::lean_unbox(v_val_2939_) as u8);
                    crate::leanh::lean_dec(v_val_2939_);
                    return v___x_2940_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_all___redArg___boxed(
    mut v_t_2947_: *mut crate::leanh::LeanObject,
    mut v_p_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2949_: u8 = 0;
    let mut v_r_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Std_TreeSet_Raw_all___redArg(v_t_2947_, v_p_2948_);
    v_r_2950_ = crate::leanh::lean_box((v_res_2949_) as usize);
    return v_r_2950_;
}
pub unsafe fn l_Std_TreeSet_Raw_all(
    mut v_00_u03b1_2951_: *mut crate::leanh::LeanObject,
    mut v_cmp_2952_: *mut crate::leanh::LeanObject,
    mut v_t_2953_: *mut crate::leanh::LeanObject,
    mut v_p_2954_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v_val_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2961_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
                v___x_2962_ = crate::leanh::lean_box(0);
                v___x_2963_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                v___f_2964_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2964_, 0, v_p_2954_);
                crate::leanh::lean_closure_set(v___f_2964_, 1, v___x_2962_);
                crate::leanh::lean_closure_set(v___f_2964_, 2, v___x_2963_);
                v___x_2965_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_2961_,
                    v___f_2964_,
                    v___x_2963_,
                    v_t_2953_,
                );
                v_a_2966_ = crate::leanh::lean_ctor_get(v___x_2965_, 0);
                crate::leanh::lean_inc(v_a_2966_);
                crate::leanh::lean_dec(v___x_2965_);
                v___y_2956_ = v_a_2966_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2957_ = crate::leanh::lean_ctor_get(v___y_2956_, 0);
                crate::leanh::lean_inc(v_fst_2957_);
                crate::leanh::lean_dec_ref(v___y_2956_);
                if crate::leanh::lean_obj_tag(v_fst_2957_) == 0 {
                    v___x_2958_ = 1;
                    return v___x_2958_;
                } else {
                    v_val_2959_ = crate::leanh::lean_ctor_get(v_fst_2957_, 0);
                    crate::leanh::lean_inc(v_val_2959_);
                    crate::leanh::lean_dec_ref_known(v_fst_2957_, 1);
                    v___x_2960_ = (crate::leanh::lean_unbox(v_val_2959_) as u8);
                    crate::leanh::lean_dec(v_val_2959_);
                    return v___x_2960_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_Raw_all___boxed(
    mut v_00_u03b1_2967_: *mut crate::leanh::LeanObject,
    mut v_cmp_2968_: *mut crate::leanh::LeanObject,
    mut v_t_2969_: *mut crate::leanh::LeanObject,
    mut v_p_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: u8 = 0;
    let mut v_r_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Std_TreeSet_Raw_all(v_00_u03b1_2967_, v_cmp_2968_, v_t_2969_, v_p_2970_);
    crate::leanh::lean_dec_ref(v_cmp_2968_);
    v_r_2972_ = crate::leanh::lean_box((v_res_2971_) as usize);
    return v_r_2972_;
}
pub unsafe fn l_Std_TreeSet_Raw_toList___redArg___lam__0(
    mut v_x1_2973_: *mut crate::leanh::LeanObject,
    mut v_x2_2974_: *mut crate::leanh::LeanObject,
    mut v_x3_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2976_, 0, v_x1_2973_);
    crate::leanh::lean_ctor_set(v___x_2976_, 1, v_x3_2975_);
    return v___x_2976_;
}
pub unsafe fn l_Std_TreeSet_Raw_toList___redArg(
    mut v_t_2978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2979_ = l_Std_TreeSet_Raw_toList___redArg___closed__0;
    v___x_2980_ = crate::leanh::lean_box(0);
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
    mut v_00_u03b1_2983_: *mut crate::leanh::LeanObject,
    mut v_cmp_2984_: *mut crate::leanh::LeanObject,
    mut v_t_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2986_ = l_Std_TreeSet_Raw_toList___redArg___closed__0;
    v___x_2987_ = crate::leanh::lean_box(0);
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
    mut v_00_u03b1_2990_: *mut crate::leanh::LeanObject,
    mut v_cmp_2991_: *mut crate::leanh::LeanObject,
    mut v_t_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Std_TreeSet_Raw_toList(v_00_u03b1_2990_, v_cmp_2991_, v_t_2992_);
    crate::leanh::lean_dec_ref(v_cmp_2991_);
    return v_res_2993_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw_ofList___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2994_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__26,
    );
    return v___x_2994_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___redArg___lam__0(
    mut v_cmp_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
    mut v_x_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2999_: u8 = 0;
    crate::leanh::lean_inc(v___y_2998_);
    crate::leanh::lean_inc(v_a_2996_);
    crate::leanh::lean_inc_ref(v_cmp_2995_);
    v___x_2999_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2995_, v_a_2996_, v___y_2998_);
    if v___x_2999_ == 0 {
        let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3000_ = crate::leanh::lean_box(0);
        v___x_3001_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2995_,
            v_a_2996_,
            v___x_3000_,
            v___y_2998_,
        );
        v___x_3002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3002_, 0, v___x_3001_);
        return v___x_3002_;
    } else {
        let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_2996_);
        crate::leanh::lean_dec_ref(v_cmp_2995_);
        v___x_3003_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3003_, 0, v___y_2998_);
        return v___x_3003_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___redArg(
    mut v_l_3004_: *mut crate::leanh::LeanObject,
    mut v_cmp_3005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3006_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3006_, 0, v_cmp_3005_);
    v___x_3007_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3008_ = crate::leanh::lean_box(1);
    v___x_3009_ = l_List_forIn_x27_loop___redArg(v___x_3007_, v___f_3006_, v_l_3004_, v_r_3008_);
    return v___x_3009_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___redArg___boxed(
    mut v_l_3010_: *mut crate::leanh::LeanObject,
    mut v_cmp_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3012_ = l_Std_TreeSet_Raw_ofList___redArg(v_l_3010_, v_cmp_3011_);
    crate::leanh::lean_dec(v_l_3010_);
    return v_res_3012_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList(
    mut v_00_u03b1_3013_: *mut crate::leanh::LeanObject,
    mut v_l_3014_: *mut crate::leanh::LeanObject,
    mut v_cmp_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3016_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3016_, 0, v_cmp_3015_);
    v___x_3017_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3018_ = crate::leanh::lean_box(1);
    v___x_3019_ = l_List_forIn_x27_loop___redArg(v___x_3017_, v___f_3016_, v_l_3014_, v_r_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofList___boxed(
    mut v_00_u03b1_3020_: *mut crate::leanh::LeanObject,
    mut v_l_3021_: *mut crate::leanh::LeanObject,
    mut v_cmp_3022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3023_ = l_Std_TreeSet_Raw_ofList(v_00_u03b1_3020_, v_l_3021_, v_cmp_3022_);
    crate::leanh::lean_dec(v_l_3021_);
    return v_res_3023_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray___redArg___lam__0(
    mut v_c_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
    mut v_x_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = lean_array_push(v_c_3024_, v_a_3025_);
    return v___x_3027_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray___redArg(
    mut v_t_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3032_ = l_Std_TreeSet_Raw_toArray___redArg___closed__0;
    v___x_3033_ = l_Std_TreeSet_Raw_toArray___redArg___closed__1;
    v___x_3034_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3032_, v___x_3033_, v_t_3031_);
    return v___x_3034_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray(
    mut v_00_u03b1_3035_: *mut crate::leanh::LeanObject,
    mut v_cmp_3036_: *mut crate::leanh::LeanObject,
    mut v_t_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3038_ = l_Std_TreeSet_Raw_toArray___redArg___closed__0;
    v___x_3039_ = l_Std_TreeSet_Raw_toArray___redArg___closed__1;
    v___x_3040_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3038_, v___x_3039_, v_t_3037_);
    return v___x_3040_;
}
pub unsafe fn l_Std_TreeSet_Raw_toArray___boxed(
    mut v_00_u03b1_3041_: *mut crate::leanh::LeanObject,
    mut v_cmp_3042_: *mut crate::leanh::LeanObject,
    mut v_t_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Std_TreeSet_Raw_toArray(v_00_u03b1_3041_, v_cmp_3042_, v_t_3043_);
    crate::leanh::lean_dec_ref(v_cmp_3042_);
    return v_res_3044_;
}
pub unsafe fn _init_l_Std_TreeSet_Raw_ofArray___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3045_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_Raw___auto__1___closed__26_once),
        _init_l_Std_TreeSet_Raw___auto__1___closed__26,
    );
    return v___x_3045_;
}
pub unsafe fn l_Std_TreeSet_Raw_ofArray___redArg(
    mut v_a_3046_: *mut crate::leanh::LeanObject,
    mut v_cmp_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3051_: usize = 0;
    let mut v___x_3052_: usize = 0;
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3048_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3048_, 0, v_cmp_3047_);
    v___x_3049_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3050_ = crate::leanh::lean_box(1);
    v_sz_3051_ = lean_array_size(v_a_3046_);
    v___x_3052_ = 0usize;
    v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3054_: *mut crate::leanh::LeanObject,
    mut v_a_3055_: *mut crate::leanh::LeanObject,
    mut v_cmp_3056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3060_: usize = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3057_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_ofList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3057_, 0, v_cmp_3056_);
    v___x_3058_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v_r_3059_ = crate::leanh::lean_box(1);
    v_sz_3060_ = lean_array_size(v_a_3055_);
    v___x_3061_ = 0usize;
    v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_b_u2082_3065_: *mut crate::leanh::LeanObject,
    mut v_x_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3066_) == 0 {
        let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3067_, 0, v_b_u2082_3065_);
        return v___x_3067_;
    } else {
        let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3068_ = l_Std_TreeSet_Raw_merge___redArg___lam__0___closed__0;
        return v___x_3068_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed(
    mut v_b_u2082_3069_: *mut crate::leanh::LeanObject,
    mut v_x_3070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3071_ = l_Std_TreeSet_Raw_merge___redArg___lam__0(v_b_u2082_3069_, v_x_3070_);
    crate::leanh::lean_dec(v_x_3070_);
    return v_res_3071_;
}
pub unsafe fn l_Std_TreeSet_Raw_merge___redArg___lam__1(
    mut v_cmp_3072_: *mut crate::leanh::LeanObject,
    mut v_t_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_3075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3076_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_merge___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3076_, 0, v_b_u2082_3075_);
    v___x_3077_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(
        v_cmp_3072_,
        v_a_3074_,
        v___f_3076_,
        v_t_3073_,
    );
    return v___x_3077_;
}
pub unsafe fn l_Std_TreeSet_Raw_merge___redArg(
    mut v_cmp_3078_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3079_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3081_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3081_, 0, v_cmp_3078_);
    v___x_3082_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3081_, v_t_u2081_3079_, v_t_u2082_3080_);
    return v___x_3082_;
}
pub unsafe fn l_Std_TreeSet_Raw_merge(
    mut v_00_u03b1_3083_: *mut crate::leanh::LeanObject,
    mut v_cmp_3084_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3085_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3087_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3087_, 0, v_cmp_3084_);
    v___x_3088_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3087_, v_t_u2081_3085_, v_t_u2082_3086_);
    return v___x_3088_;
}
pub unsafe fn l_Std_TreeSet_Raw_insertMany___redArg___lam__0(
    mut v_cmp_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
    mut v_____s_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3092_: u8 = 0;
    crate::leanh::lean_inc(v_____s_3091_);
    crate::leanh::lean_inc(v_a_3090_);
    crate::leanh::lean_inc_ref(v_cmp_3089_);
    v___x_3092_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3089_, v_a_3090_, v_____s_3091_);
    if v___x_3092_ == 0 {
        let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3093_ = crate::leanh::lean_box(0);
        v___x_3094_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
            v_cmp_3089_,
            v_a_3090_,
            v___x_3093_,
            v_____s_3091_,
        );
        v___x_3095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3095_, 0, v___x_3094_);
        return v___x_3095_;
    } else {
        let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3090_);
        crate::leanh::lean_dec_ref(v_cmp_3089_);
        v___x_3096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3096_, 0, v_____s_3091_);
        return v___x_3096_;
    }
}
pub unsafe fn l_Std_TreeSet_Raw_insertMany___redArg(
    mut v_cmp_3097_: *mut crate::leanh::LeanObject,
    mut v_inst_3098_: *mut crate::leanh::LeanObject,
    mut v_t_3099_: *mut crate::leanh::LeanObject,
    mut v_l_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3101_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3101_, 0, v_cmp_3097_);
    v___x_3102_ = crate::leanh::lean_apply_4(
        v_inst_3098_,
        crate::leanh::lean_box(0),
        v_l_3100_,
        v_t_3099_,
        v___f_3101_,
    );
    return v___x_3102_;
}
pub unsafe fn l_Std_TreeSet_Raw_insertMany(
    mut v_00_u03b1_3103_: *mut crate::leanh::LeanObject,
    mut v_cmp_3104_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3105_: *mut crate::leanh::LeanObject,
    mut v_inst_3106_: *mut crate::leanh::LeanObject,
    mut v_t_3107_: *mut crate::leanh::LeanObject,
    mut v_l_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3109_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3109_, 0, v_cmp_3104_);
    v___x_3110_ = crate::leanh::lean_apply_4(
        v_inst_3106_,
        crate::leanh::lean_box(0),
        v_l_3108_,
        v_t_3107_,
        v___f_3109_,
    );
    return v___x_3110_;
}
pub unsafe fn l_Std_TreeSet_Raw_union___redArg(
    mut v_cmp_3111_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3112_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ =
        l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(
            v_cmp_3111_,
            v_t_u2081_3112_,
            v_t_u2082_3113_,
        );
    return v___x_3114_;
}
pub unsafe fn l_Std_TreeSet_Raw_union(
    mut v_00_u03b1_3115_: *mut crate::leanh::LeanObject,
    mut v_cmp_3116_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3117_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3119_ =
        l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(
            v_cmp_3116_,
            v_t_u2081_3117_,
            v_t_u2082_3118_,
        );
    return v___x_3119_;
}
pub unsafe fn l_Std_TreeSet_Raw_instUnion___redArg(
    mut v_cmp_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3121_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_Raw_union as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3121_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3121_, 1, v_cmp_3120_);
    return v___x_3121_;
}
pub unsafe fn l_Std_TreeSet_Raw_instUnion(
    mut v_00_u03b1_3122_: *mut crate::leanh::LeanObject,
    mut v_cmp_3123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3124_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_Raw_union as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3124_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3124_, 1, v_cmp_3123_);
    return v___x_3124_;
}
pub unsafe fn l_Std_TreeSet_Raw_inter___redArg(
    mut v_cmp_3125_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3126_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3128_ =
        l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(
            v_cmp_3125_,
            v_t_u2081_3126_,
            v_t_u2082_3127_,
        );
    return v___x_3128_;
}
pub unsafe fn l_Std_TreeSet_Raw_inter(
    mut v_00_u03b1_3129_: *mut crate::leanh::LeanObject,
    mut v_cmp_3130_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3131_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3133_ =
        l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(
            v_cmp_3130_,
            v_t_u2081_3131_,
            v_t_u2082_3132_,
        );
    return v___x_3133_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInter___redArg(
    mut v_cmp_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3135_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_Raw_inter as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3135_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3135_, 1, v_cmp_3134_);
    return v___x_3135_;
}
pub unsafe fn l_Std_TreeSet_Raw_instInter(
    mut v_00_u03b1_3136_: *mut crate::leanh::LeanObject,
    mut v_cmp_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_Raw_inter as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3138_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3138_, 1, v_cmp_3137_);
    return v___x_3138_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(
    mut v_x_3139_: *mut crate::leanh::LeanObject,
    mut v_x_3140_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3139_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_3140_) == 0 {
            let mut v___x_3141_: u8 = 0;
            v___x_3141_ = 1;
            return v___x_3141_;
        } else {
            let mut v___x_3142_: u8 = 0;
            v___x_3142_ = 0;
            return v___x_3142_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_3140_) == 0 {
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
    mut v_x_3145_: *mut crate::leanh::LeanObject,
    mut v_x_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3147_: u8 = 0;
    let mut v_r_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v_x_3145_, v_x_3146_);
    crate::leanh::lean_dec(v_x_3146_);
    crate::leanh::lean_dec(v_x_3145_);
    v_r_3148_ = crate::leanh::lean_box((v_res_3147_) as usize);
    return v_r_3148_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_cmp_3149_: *mut crate::leanh::LeanObject,
    mut v_t_3150_: *mut crate::leanh::LeanObject,
    mut v_k_3151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: u8 = 0;
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3150_) == 0 {
                    v_k_3152_ = crate::leanh::lean_ctor_get(v_t_3150_, 1);
                    crate::leanh::lean_inc(v_k_3152_);
                    v_v_3153_ = crate::leanh::lean_ctor_get(v_t_3150_, 2);
                    crate::leanh::lean_inc(v_v_3153_);
                    v_l_3154_ = crate::leanh::lean_ctor_get(v_t_3150_, 3);
                    crate::leanh::lean_inc(v_l_3154_);
                    v_r_3155_ = crate::leanh::lean_ctor_get(v_t_3150_, 4);
                    crate::leanh::lean_inc(v_r_3155_);
                    crate::leanh::lean_dec_ref_known(v_t_3150_, 5);
                    crate::leanh::lean_inc_ref(v_cmp_3149_);
                    crate::leanh::lean_inc(v_k_3151_);
                    v___x_3156_ = crate::leanh::lean_apply_2(v_cmp_3149_, v_k_3151_, v_k_3152_);
                    v___x_3157_ = (crate::leanh::lean_unbox(v___x_3156_) as u8);
                    match v___x_3157_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_3155_);
                            crate::leanh::lean_dec(v_v_3153_);
                            v_t_3150_ = v_l_3154_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_3155_);
                            crate::leanh::lean_dec(v_l_3154_);
                            crate::leanh::lean_dec(v_k_3151_);
                            crate::leanh::lean_dec_ref(v_cmp_3149_);
                            v___x_3159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3159_, 0, v_v_3153_);
                            return v___x_3159_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_3154_);
                            crate::leanh::lean_dec(v_v_3153_);
                            v_t_3150_ = v_r_3155_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3151_);
                    crate::leanh::lean_dec_ref(v_cmp_3149_);
                    v___x_3161_ = crate::leanh::lean_box(0);
                    return v___x_3161_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_cmp_3162_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3163_: *mut crate::leanh::LeanObject,
    mut v_init_3164_: *mut crate::leanh::LeanObject,
    mut v_x_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_unused_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3165_) == 0 {
                    v_k_3166_ = crate::leanh::lean_ctor_get(v_x_3165_, 1);
                    crate::leanh::lean_inc(v_k_3166_);
                    v_v_3167_ = crate::leanh::lean_ctor_get(v_x_3165_, 2);
                    crate::leanh::lean_inc(v_v_3167_);
                    v_l_3168_ = crate::leanh::lean_ctor_get(v_x_3165_, 3);
                    crate::leanh::lean_inc(v_l_3168_);
                    v_r_3169_ = crate::leanh::lean_ctor_get(v_x_3165_, 4);
                    crate::leanh::lean_inc(v_r_3169_);
                    crate::leanh::lean_dec_ref_known(v_x_3165_, 5);
                    crate::leanh::lean_inc(v_t_u2082_3163_);
                    crate::leanh::lean_inc_ref(v_cmp_3162_);
                    v___x_3170_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_3162_, v_t_u2082_3163_, v_init_3164_, v_l_3168_);
                    if crate::leanh::lean_obj_tag(v___x_3170_) == 0 {
                        crate::leanh::lean_dec(v_r_3169_);
                        crate::leanh::lean_dec(v_v_3167_);
                        crate::leanh::lean_dec(v_k_3166_);
                        crate::leanh::lean_dec(v_t_u2082_3163_);
                        crate::leanh::lean_dec_ref(v_cmp_3162_);
                        return v___x_3170_;
                    } else {
                        v_isSharedCheck_3186_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3170_)) as u8;
                        if v_isSharedCheck_3186_ == 0 {
                            v_unused_3187_ = crate::leanh::lean_ctor_get(v___x_3170_, 0);
                            crate::leanh::lean_dec(v_unused_3187_);
                            v___x_3172_ = v___x_3170_;
                            v_isShared_3173_ = v_isSharedCheck_3186_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3170_);
                            v___x_3172_ = crate::leanh::lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3186_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_t_u2082_3163_);
                    crate::leanh::lean_dec_ref(v_cmp_3162_);
                    v___x_3188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3188_, 0, v_init_3164_);
                    return v___x_3188_;
                }
            }
            1 => {
                v___x_3174_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_t_u2082_3163_);
                crate::leanh::lean_inc_ref(v_cmp_3162_);
                v___x_3175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_3162_, v_t_u2082_3163_, v_k_3166_);
                v___x_3176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3176_, 0, v_v_3167_);
                v___x_3177_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__3(v___x_3175_, v___x_3176_);
                crate::leanh::lean_dec_ref_known(v___x_3176_, 1);
                crate::leanh::lean_dec(v___x_3175_);
                if v___x_3177_ == 0 {
                    crate::leanh::lean_dec(v_r_3169_);
                    crate::leanh::lean_dec(v_t_u2082_3163_);
                    crate::leanh::lean_dec_ref(v_cmp_3162_);
                    v___x_3178_ = crate::leanh::lean_box((v___x_3177_) as usize);
                    v___x_3179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3179_, 0, v___x_3178_);
                    v___x_3180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3180_, 0, v___x_3179_);
                    crate::leanh::lean_ctor_set(v___x_3180_, 1, v___x_3174_);
                    if v_isShared_3173_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3172_, 0);
                        crate::leanh::lean_ctor_set(v___x_3172_, 0, v___x_3180_);
                        v___x_3182_ = v___x_3172_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3183_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
                        v___x_3182_ = v_reuseFailAlloc_3183_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3172_);
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
    mut v_cmp_3189_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3190_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3191_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: u8 = 0;
    let mut v_val_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___y_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_u2081_3190_) == 0 {
                    v_size_3209_ = crate::leanh::lean_ctor_get(v_t_u2081_3190_, 0);
                    crate::leanh::lean_inc(v_size_3209_);
                    v___y_3206_ = v_size_3209_;
                    state = 3;
                    continue;
                } else {
                    v___x_3210_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3206_ = v___x_3210_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_fst_3194_ = crate::leanh::lean_ctor_get(v___y_3193_, 0);
                crate::leanh::lean_inc(v_fst_3194_);
                crate::leanh::lean_dec_ref(v___y_3193_);
                if crate::leanh::lean_obj_tag(v_fst_3194_) == 0 {
                    v___x_3195_ = 1;
                    return v___x_3195_;
                } else {
                    v_val_3196_ = crate::leanh::lean_ctor_get(v_fst_3194_, 0);
                    crate::leanh::lean_inc(v_val_3196_);
                    crate::leanh::lean_dec_ref_known(v_fst_3194_, 1);
                    v___x_3197_ = (crate::leanh::lean_unbox(v_val_3196_) as u8);
                    crate::leanh::lean_dec(v_val_3196_);
                    return v___x_3197_;
                }
            }
            2 => {
                v___x_3201_ = lean_nat_dec_eq(v___y_3199_, v___y_3200_);
                crate::leanh::lean_dec(v___y_3200_);
                crate::leanh::lean_dec(v___y_3199_);
                if v___x_3201_ == 0 {
                    crate::leanh::lean_dec(v_t_u2082_3191_);
                    crate::leanh::lean_dec(v_t_u2081_3190_);
                    crate::leanh::lean_dec_ref(v_cmp_3189_);
                    return v___x_3201_;
                } else {
                    v___x_3202_ = l_Std_TreeSet_Raw_any___redArg___closed__0;
                    v___x_3203_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_3189_, v_t_u2082_3191_, v___x_3202_, v_t_u2081_3190_);
                    v_a_3204_ = crate::leanh::lean_ctor_get(v___x_3203_, 0);
                    crate::leanh::lean_inc(v_a_3204_);
                    crate::leanh::lean_dec_ref(v___x_3203_);
                    v___y_3193_ = v_a_3204_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_t_u2082_3191_) == 0 {
                    v_size_3207_ = crate::leanh::lean_ctor_get(v_t_u2082_3191_, 0);
                    crate::leanh::lean_inc(v_size_3207_);
                    v___y_3199_ = v___y_3206_;
                    v___y_3200_ = v_size_3207_;
                    state = 2;
                    continue;
                } else {
                    v___x_3208_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_cmp_3211_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3212_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3214_: u8 = 0;
    let mut v_r_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3214_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3211_, v_t_u2081_3212_, v_t_u2082_3213_);
    v_r_3215_ = crate::leanh::lean_box((v_res_3214_) as usize);
    return v_r_3215_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq___redArg(
    mut v_cmp_3216_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3217_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3218_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3219_: u8 = 0;
    v___x_3219_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3216_, v_t_u2081_3217_, v_t_u2082_3218_);
    return v___x_3219_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq___redArg___boxed(
    mut v_cmp_3220_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3221_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: u8 = 0;
    let mut v_r_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Std_TreeSet_Raw_beq___redArg(v_cmp_3220_, v_t_u2081_3221_, v_t_u2082_3222_);
    v_r_3224_ = crate::leanh::lean_box((v_res_3223_) as usize);
    return v_r_3224_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq(
    mut v_00_u03b1_3225_: *mut crate::leanh::LeanObject,
    mut v_cmp_3226_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3227_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3228_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3229_: u8 = 0;
    v___x_3229_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3226_, v_t_u2081_3227_, v_t_u2082_3228_);
    return v___x_3229_;
}
pub unsafe fn l_Std_TreeSet_Raw_beq___boxed(
    mut v_00_u03b1_3230_: *mut crate::leanh::LeanObject,
    mut v_cmp_3231_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3232_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3234_: u8 = 0;
    let mut v_r_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3234_ = l_Std_TreeSet_Raw_beq(
        v_00_u03b1_3230_,
        v_cmp_3231_,
        v_t_u2081_3232_,
        v_t_u2082_3233_,
    );
    v_r_3235_ = crate::leanh::lean_box((v_res_3234_) as usize);
    return v_r_3235_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(
    mut v_cmp_3236_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3237_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3238_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3239_: u8 = 0;
    v___x_3239_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3236_, v_t_u2081_3237_, v_t_u2082_3238_);
    return v___x_3239_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg___boxed(
    mut v_cmp_3240_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3241_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3243_: u8 = 0;
    let mut v_r_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___redArg(
        v_cmp_3240_,
        v_t_u2081_3241_,
        v_t_u2082_3242_,
    );
    v_r_3244_ = crate::leanh::lean_box((v_res_3243_) as usize);
    return v_r_3244_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(
    mut v_00_u03b1_3245_: *mut crate::leanh::LeanObject,
    mut v_cmp_3246_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3247_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3248_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3249_: u8 = 0;
    v___x_3249_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3246_, v_t_u2081_3247_, v_t_u2082_3248_);
    return v___x_3249_;
}
pub unsafe fn l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0___boxed(
    mut v_00_u03b1_3250_: *mut crate::leanh::LeanObject,
    mut v_cmp_3251_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3252_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3254_: u8 = 0;
    let mut v_r_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3254_ = l_Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0(
        v_00_u03b1_3250_,
        v_cmp_3251_,
        v_t_u2081_3252_,
        v_t_u2082_3253_,
    );
    v_r_3255_ = crate::leanh::lean_box((v_res_3254_) as usize);
    return v_r_3255_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(
    mut v_cmp_3256_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3257_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3258_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3259_: u8 = 0;
    v___x_3259_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3256_, v_t_u2081_3257_, v_t_u2082_3258_);
    return v___x_3259_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg___boxed(
    mut v_cmp_3260_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3261_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3263_: u8 = 0;
    let mut v_r_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3263_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___redArg(v_cmp_3260_, v_t_u2081_3261_, v_t_u2082_3262_);
    v_r_3264_ = crate::leanh::lean_box((v_res_3263_) as usize);
    return v_r_3264_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(
    mut v_00_u03b1_3265_: *mut crate::leanh::LeanObject,
    mut v_cmp_3266_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3267_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3268_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3269_: u8 = 0;
    v___x_3269_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3266_, v_t_u2081_3267_, v_t_u2082_3268_);
    return v___x_3269_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0___boxed(
    mut v_00_u03b1_3270_: *mut crate::leanh::LeanObject,
    mut v_cmp_3271_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3272_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3274_: u8 = 0;
    let mut v_r_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0(v_00_u03b1_3270_, v_cmp_3271_, v_t_u2081_3272_, v_t_u2082_3273_);
    v_r_3275_ = crate::leanh::lean_box((v_res_3274_) as usize);
    return v_r_3275_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3276_: *mut crate::leanh::LeanObject,
    mut v_cmp_3277_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3278_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3279_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3280_: u8 = 0;
    v___x_3280_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___redArg(v_cmp_3277_, v_t_u2081_3278_, v_t_u2082_3279_);
    return v___x_3280_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3281_: *mut crate::leanh::LeanObject,
    mut v_cmp_3282_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3283_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3285_: u8 = 0;
    let mut v_r_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3285_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1(v_00_u03b1_3281_, v_cmp_3282_, v_t_u2081_3283_, v_t_u2082_3284_);
    v_r_3286_ = crate::leanh::lean_box((v_res_3285_) as usize);
    return v_r_3286_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3287_: *mut crate::leanh::LeanObject,
    mut v_cmp_3288_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3289_: *mut crate::leanh::LeanObject,
    mut v_t_3290_: *mut crate::leanh::LeanObject,
    mut v_k_3291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3292_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_3288_, v_t_3290_, v_k_3291_);
    return v___x_3292_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_3293_: *mut crate::leanh::LeanObject,
    mut v_cmp_3294_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3295_: *mut crate::leanh::LeanObject,
    mut v_init_3296_: *mut crate::leanh::LeanObject,
    mut v_x_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3298_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Raw_Const_beq___at___00Std_TreeMap_Raw_beq___at___00Std_TreeSet_Raw_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_3294_, v_t_u2082_3295_, v_init_3296_, v_x_3297_);
    return v___x_3298_;
}
pub unsafe fn l_Std_TreeSet_Raw_instBEq___redArg(
    mut v_cmp_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3300_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3300_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3300_, 1, v_cmp_3299_);
    return v___x_3300_;
}
pub unsafe fn l_Std_TreeSet_Raw_instBEq(
    mut v_00_u03b1_3301_: *mut crate::leanh::LeanObject,
    mut v_cmp_3302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3303_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3303_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3303_, 1, v_cmp_3302_);
    return v___x_3303_;
}
pub unsafe fn l_Std_TreeSet_Raw_diff___redArg(
    mut v_cmp_3304_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3305_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ =
        l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(
            v_cmp_3304_,
            v_t_u2081_3305_,
            v_t_u2082_3306_,
        );
    return v___x_3307_;
}
pub unsafe fn l_Std_TreeSet_Raw_diff(
    mut v_00_u03b1_3308_: *mut crate::leanh::LeanObject,
    mut v_cmp_3309_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3310_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ =
        l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(
            v_cmp_3309_,
            v_t_u2081_3310_,
            v_t_u2082_3311_,
        );
    return v___x_3312_;
}
pub unsafe fn l_Std_TreeSet_Raw_instSDiff___redArg(
    mut v_cmp_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_Raw_diff as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3314_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3314_, 1, v_cmp_3313_);
    return v___x_3314_;
}
pub unsafe fn l_Std_TreeSet_Raw_instSDiff(
    mut v_00_u03b1_3315_: *mut crate::leanh::LeanObject,
    mut v_cmp_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_Raw_diff as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3317_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3317_, 1, v_cmp_3316_);
    return v___x_3317_;
}
pub unsafe fn l_Std_TreeSet_Raw_eraseMany___redArg___lam__0(
    mut v_cmp_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
    mut v_____s_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_3321_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_3318_, v_a_3319_, v_____s_3320_);
    v___x_3322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3322_, 0, v_r_3321_);
    return v___x_3322_;
}
pub unsafe fn l_Std_TreeSet_Raw_eraseMany___redArg(
    mut v_cmp_3323_: *mut crate::leanh::LeanObject,
    mut v_inst_3324_: *mut crate::leanh::LeanObject,
    mut v_t_3325_: *mut crate::leanh::LeanObject,
    mut v_l_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3327_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3327_, 0, v_cmp_3323_);
    v___x_3328_ = crate::leanh::lean_apply_4(
        v_inst_3324_,
        crate::leanh::lean_box(0),
        v_l_3326_,
        v_t_3325_,
        v___f_3327_,
    );
    return v___x_3328_;
}
pub unsafe fn l_Std_TreeSet_Raw_eraseMany(
    mut v_00_u03b1_3329_: *mut crate::leanh::LeanObject,
    mut v_cmp_3330_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3331_: *mut crate::leanh::LeanObject,
    mut v_inst_3332_: *mut crate::leanh::LeanObject,
    mut v_t_3333_: *mut crate::leanh::LeanObject,
    mut v_l_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3335_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3335_, 0, v_cmp_3330_);
    v___x_3336_ = crate::leanh::lean_apply_4(
        v_inst_3332_,
        crate::leanh::lean_box(0),
        v_l_3334_,
        v_t_3333_,
        v___f_3335_,
    );
    return v___x_3336_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___redArg___lam__1(
    mut v___f_3340_: *mut crate::leanh::LeanObject,
    mut v_inst_3341_: *mut crate::leanh::LeanObject,
    mut v_m_3342_: *mut crate::leanh::LeanObject,
    mut v_prec_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1___closed__1;
    v___x_3345_ = crate::leanh::lean_box(0);
    v___x_3346_ = l_Std_TreeSet_Raw_foldr___redArg___closed__9;
    v___x_3347_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3346_,
        v___f_3340_,
        v___x_3345_,
        v_m_3342_,
    );
    v___x_3348_ = l_List_repr___redArg(v_inst_3341_, v___x_3347_);
    v___x_3349_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3349_, 0, v___x_3344_);
    crate::leanh::lean_ctor_set(v___x_3349_, 1, v___x_3348_);
    v___x_3350_ = l_Repr_addAppParen(v___x_3349_, v_prec_3343_);
    return v___x_3350_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed(
    mut v___f_3351_: *mut crate::leanh::LeanObject,
    mut v_inst_3352_: *mut crate::leanh::LeanObject,
    mut v_m_3353_: *mut crate::leanh::LeanObject,
    mut v_prec_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Std_TreeSet_Raw_instRepr___redArg___lam__1(
        v___f_3351_,
        v_inst_3352_,
        v_m_3353_,
        v_prec_3354_,
    );
    crate::leanh::lean_dec(v_prec_3354_);
    return v_res_3355_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___redArg(
    mut v_inst_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3357_ = l_Std_TreeSet_Raw_toList___redArg___closed__0;
    v___f_3358_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_Raw_instRepr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3358_, 0, v___f_3357_);
    crate::leanh::lean_closure_set(v___f_3358_, 1, v_inst_3356_);
    return v___f_3358_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr(
    mut v_00_u03b1_3359_: *mut crate::leanh::LeanObject,
    mut v_cmp_3360_: *mut crate::leanh::LeanObject,
    mut v_inst_3361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ = l_Std_TreeSet_Raw_instRepr___redArg(v_inst_3361_);
    return v___x_3362_;
}
pub unsafe fn l_Std_TreeSet_Raw_instRepr___boxed(
    mut v_00_u03b1_3363_: *mut crate::leanh::LeanObject,
    mut v_cmp_3364_: *mut crate::leanh::LeanObject,
    mut v_inst_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3366_ = l_Std_TreeSet_Raw_instRepr(v_00_u03b1_3363_, v_cmp_3364_, v_inst_3365_);
    crate::leanh::lean_dec_ref(v_cmp_3364_);
    return v_res_3366_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Raw_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Raw_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeSet_Raw___auto__1 = _init_l_Std_TreeSet_Raw___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_Raw___auto__1);
    l_Std_TreeSet_Raw_ofList___auto__1 = _init_l_Std_TreeSet_Raw_ofList___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_Raw_ofList___auto__1);
    l_Std_TreeSet_Raw_ofArray___auto__1 = _init_l_Std_TreeSet_Raw_ofArray___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_Raw_ofArray___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Raw_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Raw_Basic(builtin);
}
