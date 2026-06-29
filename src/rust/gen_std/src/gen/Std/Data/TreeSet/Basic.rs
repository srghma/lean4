// Lean compiler output
// Module: Std.Data.TreeSet.Basic
// Imports: Std.Data.TreeMap.Basic
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_string_utf8_byte_size,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_Lean_replaceRef, l_String_toRawSubstring_x27, l_panic___redArg,
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
pub static l_Std_TreeSet___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_TreeSet___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Std_TreeSet___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Std_TreeSet___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeSet___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Std_TreeSet___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_Std_TreeSet___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeSet___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Std_TreeSet___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet___auto__1___closed__14_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_TreeSet___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet___auto__1___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16710690322389477741 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_term___x7em___00__closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_TreeSet_term___x7em___00__closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            206985604220839926 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_TreeSet_term___x7em___00__closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            18267916200040923880 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__4_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__6_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_TreeSet_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,206985604220839926 as *mut crate::leanh::LeanObject] };
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,15083926597284366801 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_getGE_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Std_TreeSet_getGE_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_getGE_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_getGE_x21___redArg___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_TreeSet_getGE_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_getGE_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_getGE_x21___redArg___closed__2_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_TreeSet_getGE_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_getGE_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_getGE_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_getGE_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_foldr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_TreeSet_foldr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_foldr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_foldr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_foldr___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_TreeSet_foldr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_foldr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_partition___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_TreeSet_partition___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_partition___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_any___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_TreeSet_any___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_any___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_ofList___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_ofArray___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_merge___redArg___lam__0___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
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
static mut l_Std_TreeSet_merge___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_merge___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 114, 101, 101, 83, 101, 116, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Std_TreeSet_instRepr___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instRepr___redArg___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Std_TreeSet_instRepr___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeSet_instRepr___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instRepr___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = l_Std_TreeSet___auto__1___closed__10;
    v___x_2135_ = l_Lean_mkAtom(v___x_2134_);
    return v___x_2135_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__12_once),
        _init_l_Std_TreeSet___auto__1___closed__12,
    );
    v___x_2137_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2138_ = lean_array_push(v___x_2137_, v___x_2136_);
    return v___x_2138_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = l_Std_TreeSet___auto__1___closed__14;
    v___x_2141_ = lean_string_utf8_byte_size(v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2142_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__15_once),
        _init_l_Std_TreeSet___auto__1___closed__15,
    );
    v___x_2143_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2144_ = l_Std_TreeSet___auto__1___closed__14;
    v___x_2145_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2145_, 0, v___x_2144_);
    crate::leanh::lean_ctor_set(v___x_2145_, 1, v___x_2143_);
    crate::leanh::lean_ctor_set(v___x_2145_, 2, v___x_2142_);
    return v___x_2145_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = crate::leanh::lean_box(0);
    v___x_2149_ = l_Std_TreeSet___auto__1___closed__17;
    v___x_2150_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__16_once),
        _init_l_Std_TreeSet___auto__1___closed__16,
    );
    v___x_2151_ = crate::leanh::lean_box(2);
    v___x_2152_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2152_, 0, v___x_2151_);
    crate::leanh::lean_ctor_set(v___x_2152_, 1, v___x_2150_);
    crate::leanh::lean_ctor_set(v___x_2152_, 2, v___x_2149_);
    crate::leanh::lean_ctor_set(v___x_2152_, 3, v___x_2148_);
    return v___x_2152_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__18_once),
        _init_l_Std_TreeSet___auto__1___closed__18,
    );
    v___x_2154_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__13_once),
        _init_l_Std_TreeSet___auto__1___closed__13,
    );
    v___x_2155_ = lean_array_push(v___x_2154_, v___x_2153_);
    return v___x_2155_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2156_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__19_once),
        _init_l_Std_TreeSet___auto__1___closed__19,
    );
    v___x_2157_ = l_Std_TreeSet___auto__1___closed__11;
    v___x_2158_ = crate::leanh::lean_box(2);
    v___x_2159_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2159_, 0, v___x_2158_);
    crate::leanh::lean_ctor_set(v___x_2159_, 1, v___x_2157_);
    crate::leanh::lean_ctor_set(v___x_2159_, 2, v___x_2156_);
    return v___x_2159_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2160_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__20_once),
        _init_l_Std_TreeSet___auto__1___closed__20,
    );
    v___x_2161_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2162_ = lean_array_push(v___x_2161_, v___x_2160_);
    return v___x_2162_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2163_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__21_once),
        _init_l_Std_TreeSet___auto__1___closed__21,
    );
    v___x_2164_ = l_Std_TreeSet___auto__1___closed__9;
    v___x_2165_ = crate::leanh::lean_box(2);
    v___x_2166_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
    crate::leanh::lean_ctor_set(v___x_2166_, 1, v___x_2164_);
    crate::leanh::lean_ctor_set(v___x_2166_, 2, v___x_2163_);
    return v___x_2166_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2167_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__22_once),
        _init_l_Std_TreeSet___auto__1___closed__22,
    );
    v___x_2168_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2169_ = lean_array_push(v___x_2168_, v___x_2167_);
    return v___x_2169_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2170_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__23_once),
        _init_l_Std_TreeSet___auto__1___closed__23,
    );
    v___x_2171_ = l_Std_TreeSet___auto__1___closed__7;
    v___x_2172_ = crate::leanh::lean_box(2);
    v___x_2173_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
    crate::leanh::lean_ctor_set(v___x_2173_, 1, v___x_2171_);
    crate::leanh::lean_ctor_set(v___x_2173_, 2, v___x_2170_);
    return v___x_2173_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2174_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__24_once),
        _init_l_Std_TreeSet___auto__1___closed__24,
    );
    v___x_2175_ = l_Std_TreeSet___auto__1___closed__5;
    v___x_2176_ = lean_array_push(v___x_2175_, v___x_2174_);
    return v___x_2176_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__25_once),
        _init_l_Std_TreeSet___auto__1___closed__25,
    );
    v___x_2178_ = l_Std_TreeSet___auto__1___closed__4;
    v___x_2179_ = crate::leanh::lean_box(2);
    v___x_2180_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2179_);
    crate::leanh::lean_ctor_set(v___x_2180_, 1, v___x_2178_);
    crate::leanh::lean_ctor_set(v___x_2180_, 2, v___x_2177_);
    return v___x_2180_;
}
pub unsafe fn _init_l_Std_TreeSet___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2181_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26_once),
        _init_l_Std_TreeSet___auto__1___closed__26,
    );
    return v___x_2181_;
}
pub unsafe fn l_Std_TreeSet_empty(
    mut v_00_u03b1_2182_: *mut crate::leanh::LeanObject,
    mut v_cmp_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2184_ = crate::leanh::lean_box(1);
    return v___x_2184_;
}
pub unsafe fn l_Std_TreeSet_empty___boxed(
    mut v_00_u03b1_2185_: *mut crate::leanh::LeanObject,
    mut v_cmp_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Std_TreeSet_empty(v_00_u03b1_2185_, v_cmp_2186_);
    crate::leanh::lean_dec_ref(v_cmp_2186_);
    return v_res_2187_;
}
pub unsafe fn l_Std_TreeSet_instEmptyCollection(
    mut v_00_u03b1_2188_: *mut crate::leanh::LeanObject,
    mut v_cmp_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = crate::leanh::lean_box(1);
    return v___x_2190_;
}
pub unsafe fn l_Std_TreeSet_instEmptyCollection___boxed(
    mut v_00_u03b1_2191_: *mut crate::leanh::LeanObject,
    mut v_cmp_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Std_TreeSet_instEmptyCollection(v_00_u03b1_2191_, v_cmp_2192_);
    crate::leanh::lean_dec_ref(v_cmp_2192_);
    return v_res_2193_;
}
pub unsafe fn l_Std_TreeSet_instInhabited(
    mut v_00_u03b1_2194_: *mut crate::leanh::LeanObject,
    mut v_cmp_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = crate::leanh::lean_box(1);
    return v___x_2196_;
}
pub unsafe fn l_Std_TreeSet_instInhabited___boxed(
    mut v_00_u03b1_2197_: *mut crate::leanh::LeanObject,
    mut v_cmp_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2199_ = l_Std_TreeSet_instInhabited(v_00_u03b1_2197_, v_cmp_2198_);
    crate::leanh::lean_dec_ref(v_cmp_2198_);
    return v_res_2199_;
}
pub unsafe fn _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__3;
    v___x_2238_ = l_String_toRawSubstring_x27(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(
    mut v_x_2256_: *mut crate::leanh::LeanObject,
    mut v_a_2257_: *mut crate::leanh::LeanObject,
    mut v_a_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    v___x_2259_ = l_Std_TreeSet_term___x7em___00__closed__3;
    crate::leanh::lean_inc(v_x_2256_);
    v___x_2260_ = l_Lean_Syntax_isOfKind(v_x_2256_, v___x_2259_);
    if v___x_2260_ == 0 {
        let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2256_);
        v___x_2261_ = crate::leanh::lean_box(1);
        v___x_2262_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2262_, 0, v___x_2261_);
        crate::leanh::lean_ctor_set(v___x_2262_, 1, v_a_2258_);
        return v___x_2262_;
    } else {
        let mut v_quotContext_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2270_: u8 = 0;
        let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2263_ = crate::leanh::lean_ctor_get(v_a_2257_, 1);
        v_currMacroScope_2264_ = crate::leanh::lean_ctor_get(v_a_2257_, 2);
        v_ref_2265_ = crate::leanh::lean_ctor_get(v_a_2257_, 5);
        v___x_2266_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2267_ = l_Lean_Syntax_getArg(v_x_2256_, v___x_2266_);
        v___x_2268_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2269_ = l_Lean_Syntax_getArg(v_x_2256_, v___x_2268_);
        crate::leanh::lean_dec(v_x_2256_);
        v___x_2270_ = 0;
        v___x_2271_ = l_Lean_SourceInfo_fromRef(v_ref_2265_, v___x_2270_);
        v___x_2272_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2;
        v___x_2273_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4), core::ptr::addr_of_mut!(l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4_once), _init_l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__4);
        v___x_2274_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__5;
        crate::leanh::lean_inc(v_currMacroScope_2264_);
        crate::leanh::lean_inc(v_quotContext_2263_);
        v___x_2275_ =
            l_Lean_addMacroScope(v_quotContext_2263_, v___x_2274_, v_currMacroScope_2264_);
        v___x_2276_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__10;
        crate::leanh::lean_inc_n(v___x_2271_, 2);
        v___x_2277_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2277_, 0, v___x_2271_);
        crate::leanh::lean_ctor_set(v___x_2277_, 1, v___x_2273_);
        crate::leanh::lean_ctor_set(v___x_2277_, 2, v___x_2275_);
        crate::leanh::lean_ctor_set(v___x_2277_, 3, v___x_2276_);
        v___x_2278_ = l_Std_TreeSet___auto__1___closed__9;
        v___x_2279_ = l_Lean_Syntax_node2(v___x_2271_, v___x_2278_, v___x_2267_, v___x_2269_);
        v___x_2280_ = l_Lean_Syntax_node2(v___x_2271_, v___x_2272_, v___x_2277_, v___x_2279_);
        v___x_2281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2281_, 0, v___x_2280_);
        crate::leanh::lean_ctor_set(v___x_2281_, 1, v_a_2258_);
        return v___x_2281_;
    }
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___boxed(
    mut v_x_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2285_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1(v_x_2282_, v_a_2283_, v_a_2284_);
    crate::leanh::lean_dec_ref(v_a_2283_);
    return v_res_2285_;
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(
    mut v_x_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    v___x_2292_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______macroRules__Std__TreeSet__term___x7em____1___closed__2;
    crate::leanh::lean_inc(v_x_2289_);
    v___x_2293_ = l_Lean_Syntax_isOfKind(v_x_2289_, v___x_2292_);
    if v___x_2293_ == 0 {
        let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2289_);
        v___x_2294_ = crate::leanh::lean_box(0);
        v___x_2295_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2295_, 0, v___x_2294_);
        crate::leanh::lean_ctor_set(v___x_2295_, 1, v_a_2291_);
        return v___x_2295_;
    } else {
        let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: u8 = 0;
        v___x_2296_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2297_ = l_Lean_Syntax_getArg(v_x_2289_, v___x_2296_);
        v___x_2298_ = l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_2297_);
        v___x_2299_ = l_Lean_Syntax_isOfKind(v___x_2297_, v___x_2298_);
        if v___x_2299_ == 0 {
            let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2297_);
            crate::leanh::lean_dec(v_x_2289_);
            v___x_2300_ = crate::leanh::lean_box(0);
            v___x_2301_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2301_, 0, v___x_2300_);
            crate::leanh::lean_ctor_set(v___x_2301_, 1, v_a_2291_);
            return v___x_2301_;
        } else {
            let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2305_: u8 = 0;
            v___x_2302_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2303_ = l_Lean_Syntax_getArg(v_x_2289_, v___x_2302_);
            crate::leanh::lean_dec(v_x_2289_);
            v___x_2304_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_2303_);
            v___x_2305_ = l_Lean_Syntax_matchesNull(v___x_2303_, v___x_2304_);
            if v___x_2305_ == 0 {
                let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2303_);
                crate::leanh::lean_dec(v___x_2297_);
                v___x_2306_ = crate::leanh::lean_box(0);
                v___x_2307_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2307_, 0, v___x_2306_);
                crate::leanh::lean_ctor_set(v___x_2307_, 1, v_a_2291_);
                return v___x_2307_;
            } else {
                let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2311_: u8 = 0;
                let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2308_ = l_Lean_Syntax_getArg(v___x_2303_, v___x_2296_);
                v___x_2309_ = l_Lean_Syntax_getArg(v___x_2303_, v___x_2302_);
                crate::leanh::lean_dec(v___x_2303_);
                v_ref_2310_ = l_Lean_replaceRef(v___x_2297_, v_a_2290_);
                crate::leanh::lean_dec(v___x_2297_);
                v___x_2311_ = 0;
                v___x_2312_ = l_Lean_SourceInfo_fromRef(v_ref_2310_, v___x_2311_);
                crate::leanh::lean_dec(v_ref_2310_);
                v___x_2313_ = l_Std_TreeSet_term___x7em___00__closed__3;
                v___x_2314_ = l_Std_TreeSet_term___x7em___00__closed__6;
                crate::leanh::lean_inc(v___x_2312_);
                v___x_2315_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2312_);
                crate::leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                v___x_2316_ = l_Lean_Syntax_node3(
                    v___x_2312_,
                    v___x_2313_,
                    v___x_2308_,
                    v___x_2315_,
                    v___x_2309_,
                );
                v___x_2317_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2317_, 0, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2317_, 1, v_a_2291_);
                return v___x_2317_;
            }
        }
    }
}
pub unsafe fn l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1___boxed(
    mut v_x_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2321_ =
        l_Std_TreeSet___aux__Std__Data__TreeSet__Basic______unexpand__Std__TreeSet__Equiv__1(
            v_x_2318_, v_a_2319_, v_a_2320_,
        );
    crate::leanh::lean_dec(v_a_2319_);
    return v_res_2321_;
}
pub unsafe fn l_Std_TreeSet_insert___redArg(
    mut v_cmp_2322_: *mut crate::leanh::LeanObject,
    mut v_l_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: u8 = 0;
    crate::leanh::lean_inc(v_l_2323_);
    crate::leanh::lean_inc(v_a_2324_);
    crate::leanh::lean_inc_ref(v_cmp_2322_);
    v___x_2325_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2322_, v_a_2324_, v_l_2323_);
    if v___x_2325_ == 0 {
        let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2326_ = crate::leanh::lean_box(0);
        v___x_2327_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2322_,
            v_a_2324_,
            v___x_2326_,
            v_l_2323_,
        );
        return v___x_2327_;
    } else {
        crate::leanh::lean_dec(v_a_2324_);
        crate::leanh::lean_dec_ref(v_cmp_2322_);
        return v_l_2323_;
    }
}
pub unsafe fn l_Std_TreeSet_insert(
    mut v_00_u03b1_2328_: *mut crate::leanh::LeanObject,
    mut v_cmp_2329_: *mut crate::leanh::LeanObject,
    mut v_l_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: u8 = 0;
    crate::leanh::lean_inc(v_l_2330_);
    crate::leanh::lean_inc(v_a_2331_);
    crate::leanh::lean_inc_ref(v_cmp_2329_);
    v___x_2332_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2329_, v_a_2331_, v_l_2330_);
    if v___x_2332_ == 0 {
        let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2333_ = crate::leanh::lean_box(0);
        v___x_2334_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2329_,
            v_a_2331_,
            v___x_2333_,
            v_l_2330_,
        );
        return v___x_2334_;
    } else {
        crate::leanh::lean_dec(v_a_2331_);
        crate::leanh::lean_dec_ref(v_cmp_2329_);
        return v_l_2330_;
    }
}
pub unsafe fn l_Std_TreeSet_instSingleton___redArg___lam__0(
    mut v_cmp_2335_: *mut crate::leanh::LeanObject,
    mut v_e_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    v___x_2337_ = crate::leanh::lean_box(1);
    crate::leanh::lean_inc(v_e_2336_);
    crate::leanh::lean_inc_ref(v_cmp_2335_);
    v___x_2338_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2335_, v_e_2336_, v___x_2337_);
    if v___x_2338_ == 0 {
        let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2339_ = crate::leanh::lean_box(0);
        v___x_2340_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2335_,
            v_e_2336_,
            v___x_2339_,
            v___x_2337_,
        );
        return v___x_2340_;
    } else {
        crate::leanh::lean_dec(v_e_2336_);
        crate::leanh::lean_dec_ref(v_cmp_2335_);
        return v___x_2337_;
    }
}
pub unsafe fn l_Std_TreeSet_instSingleton___redArg(
    mut v_cmp_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2342_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2342_, 0, v_cmp_2341_);
    return v___f_2342_;
}
pub unsafe fn l_Std_TreeSet_instSingleton(
    mut v_00_u03b1_2343_: *mut crate::leanh::LeanObject,
    mut v_cmp_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2345_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2345_, 0, v_cmp_2344_);
    return v___f_2345_;
}
pub unsafe fn l_Std_TreeSet_instInsert___redArg___lam__0(
    mut v_cmp_2346_: *mut crate::leanh::LeanObject,
    mut v_e_2347_: *mut crate::leanh::LeanObject,
    mut v_s_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2349_: u8 = 0;
    crate::leanh::lean_inc(v_s_2348_);
    crate::leanh::lean_inc(v_e_2347_);
    crate::leanh::lean_inc_ref(v_cmp_2346_);
    v___x_2349_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2346_, v_e_2347_, v_s_2348_);
    if v___x_2349_ == 0 {
        let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2350_ = crate::leanh::lean_box(0);
        v___x_2351_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2346_,
            v_e_2347_,
            v___x_2350_,
            v_s_2348_,
        );
        return v___x_2351_;
    } else {
        crate::leanh::lean_dec(v_e_2347_);
        crate::leanh::lean_dec_ref(v_cmp_2346_);
        return v_s_2348_;
    }
}
pub unsafe fn l_Std_TreeSet_instInsert___redArg(
    mut v_cmp_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2353_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2353_, 0, v_cmp_2352_);
    return v___f_2353_;
}
pub unsafe fn l_Std_TreeSet_instInsert(
    mut v_00_u03b1_2354_: *mut crate::leanh::LeanObject,
    mut v_cmp_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2356_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2356_, 0, v_cmp_2355_);
    return v___f_2356_;
}
pub unsafe fn l_Std_TreeSet_containsThenInsert___redArg(
    mut v_cmp_2357_: *mut crate::leanh::LeanObject,
    mut v_t_2358_: *mut crate::leanh::LeanObject,
    mut v_a_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2360_: u8 = 0;
    crate::leanh::lean_inc(v_t_2358_);
    crate::leanh::lean_inc(v_a_2359_);
    crate::leanh::lean_inc_ref(v_cmp_2357_);
    v___x_2360_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2357_, v_a_2359_, v_t_2358_);
    if v___x_2360_ == 0 {
        let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2361_ = crate::leanh::lean_box(0);
        v___x_2362_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2357_,
            v_a_2359_,
            v___x_2361_,
            v_t_2358_,
        );
        v___x_2363_ = crate::leanh::lean_box((v___x_2360_) as usize);
        v___x_2364_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2364_, 0, v___x_2363_);
        crate::leanh::lean_ctor_set(v___x_2364_, 1, v___x_2362_);
        return v___x_2364_;
    } else {
        let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_2359_);
        crate::leanh::lean_dec_ref(v_cmp_2357_);
        v___x_2365_ = crate::leanh::lean_box((v___x_2360_) as usize);
        v___x_2366_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2366_, 0, v___x_2365_);
        crate::leanh::lean_ctor_set(v___x_2366_, 1, v_t_2358_);
        return v___x_2366_;
    }
}
pub unsafe fn l_Std_TreeSet_containsThenInsert(
    mut v_00_u03b1_2367_: *mut crate::leanh::LeanObject,
    mut v_cmp_2368_: *mut crate::leanh::LeanObject,
    mut v_t_2369_: *mut crate::leanh::LeanObject,
    mut v_a_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2371_: u8 = 0;
    crate::leanh::lean_inc(v_t_2369_);
    crate::leanh::lean_inc(v_a_2370_);
    crate::leanh::lean_inc_ref(v_cmp_2368_);
    v___x_2371_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2368_, v_a_2370_, v_t_2369_);
    if v___x_2371_ == 0 {
        let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2372_ = crate::leanh::lean_box(0);
        v___x_2373_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_2368_,
            v_a_2370_,
            v___x_2372_,
            v_t_2369_,
        );
        v___x_2374_ = crate::leanh::lean_box((v___x_2371_) as usize);
        v___x_2375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2375_, 0, v___x_2374_);
        crate::leanh::lean_ctor_set(v___x_2375_, 1, v___x_2373_);
        return v___x_2375_;
    } else {
        let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_2370_);
        crate::leanh::lean_dec_ref(v_cmp_2368_);
        v___x_2376_ = crate::leanh::lean_box((v___x_2371_) as usize);
        v___x_2377_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2377_, 0, v___x_2376_);
        crate::leanh::lean_ctor_set(v___x_2377_, 1, v_t_2369_);
        return v___x_2377_;
    }
}
pub unsafe fn l_Std_TreeSet_contains___redArg(
    mut v_cmp_2378_: *mut crate::leanh::LeanObject,
    mut v_l_2379_: *mut crate::leanh::LeanObject,
    mut v_a_2380_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2381_: u8 = 0;
    v___x_2381_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2378_, v_a_2380_, v_l_2379_);
    return v___x_2381_;
}
pub unsafe fn l_Std_TreeSet_contains___redArg___boxed(
    mut v_cmp_2382_: *mut crate::leanh::LeanObject,
    mut v_l_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2385_: u8 = 0;
    let mut v_r_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_Std_TreeSet_contains___redArg(v_cmp_2382_, v_l_2383_, v_a_2384_);
    v_r_2386_ = crate::leanh::lean_box((v_res_2385_) as usize);
    return v_r_2386_;
}
pub unsafe fn l_Std_TreeSet_contains(
    mut v_00_u03b1_2387_: *mut crate::leanh::LeanObject,
    mut v_cmp_2388_: *mut crate::leanh::LeanObject,
    mut v_l_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2391_: u8 = 0;
    v___x_2391_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2388_, v_a_2390_, v_l_2389_);
    return v___x_2391_;
}
pub unsafe fn l_Std_TreeSet_contains___boxed(
    mut v_00_u03b1_2392_: *mut crate::leanh::LeanObject,
    mut v_cmp_2393_: *mut crate::leanh::LeanObject,
    mut v_l_2394_: *mut crate::leanh::LeanObject,
    mut v_a_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2396_: u8 = 0;
    let mut v_r_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Std_TreeSet_contains(v_00_u03b1_2392_, v_cmp_2393_, v_l_2394_, v_a_2395_);
    v_r_2397_ = crate::leanh::lean_box((v_res_2396_) as usize);
    return v_r_2397_;
}
pub unsafe fn l_Std_TreeSet_instMembership(
    mut v_00_u03b1_2398_: *mut crate::leanh::LeanObject,
    mut v_cmp_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2400_ = crate::leanh::lean_box(0);
    return v___x_2400_;
}
pub unsafe fn l_Std_TreeSet_instMembership___boxed(
    mut v_00_u03b1_2401_: *mut crate::leanh::LeanObject,
    mut v_cmp_2402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2403_ = l_Std_TreeSet_instMembership(v_00_u03b1_2401_, v_cmp_2402_);
    crate::leanh::lean_dec_ref(v_cmp_2402_);
    return v_res_2403_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem___redArg(
    mut v_cmp_2404_: *mut crate::leanh::LeanObject,
    mut v_m_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2407_: u8 = 0;
    v___x_2407_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2404_, v_a_2406_, v_m_2405_);
    return v___x_2407_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem___redArg___boxed(
    mut v_cmp_2408_: *mut crate::leanh::LeanObject,
    mut v_m_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2411_: u8 = 0;
    let mut v_r_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Std_TreeSet_instDecidableMem___redArg(v_cmp_2408_, v_m_2409_, v_a_2410_);
    v_r_2412_ = crate::leanh::lean_box((v_res_2411_) as usize);
    return v_r_2412_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem(
    mut v_00_u03b1_2413_: *mut crate::leanh::LeanObject,
    mut v_cmp_2414_: *mut crate::leanh::LeanObject,
    mut v_m_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2417_: u8 = 0;
    v___x_2417_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2414_, v_a_2416_, v_m_2415_);
    return v___x_2417_;
}
pub unsafe fn l_Std_TreeSet_instDecidableMem___boxed(
    mut v_00_u03b1_2418_: *mut crate::leanh::LeanObject,
    mut v_cmp_2419_: *mut crate::leanh::LeanObject,
    mut v_m_2420_: *mut crate::leanh::LeanObject,
    mut v_a_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2422_: u8 = 0;
    let mut v_r_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2422_ =
        l_Std_TreeSet_instDecidableMem(v_00_u03b1_2418_, v_cmp_2419_, v_m_2420_, v_a_2421_);
    v_r_2423_ = crate::leanh::lean_box((v_res_2422_) as usize);
    return v_r_2423_;
}
pub unsafe fn l_Std_TreeSet_size___redArg(
    mut v_t_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2424_) == 0 {
        let mut v_size_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_2425_ = crate::leanh::lean_ctor_get(v_t_2424_, 0);
        crate::leanh::lean_inc(v_size_2425_);
        return v_size_2425_;
    } else {
        let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2426_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2426_;
    }
}
pub unsafe fn l_Std_TreeSet_size___redArg___boxed(
    mut v_t_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2428_ = l_Std_TreeSet_size___redArg(v_t_2427_);
    crate::leanh::lean_dec(v_t_2427_);
    return v_res_2428_;
}
pub unsafe fn l_Std_TreeSet_size(
    mut v_00_u03b1_2429_: *mut crate::leanh::LeanObject,
    mut v_cmp_2430_: *mut crate::leanh::LeanObject,
    mut v_t_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2431_) == 0 {
        let mut v_size_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_size_2432_ = crate::leanh::lean_ctor_get(v_t_2431_, 0);
        crate::leanh::lean_inc(v_size_2432_);
        return v_size_2432_;
    } else {
        let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2433_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2433_;
    }
}
pub unsafe fn l_Std_TreeSet_size___boxed(
    mut v_00_u03b1_2434_: *mut crate::leanh::LeanObject,
    mut v_cmp_2435_: *mut crate::leanh::LeanObject,
    mut v_t_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Std_TreeSet_size(v_00_u03b1_2434_, v_cmp_2435_, v_t_2436_);
    crate::leanh::lean_dec(v_t_2436_);
    crate::leanh::lean_dec_ref(v_cmp_2435_);
    return v_res_2437_;
}
pub unsafe fn l_Std_TreeSet_isEmpty___redArg(mut v_t_2438_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_2438_) == 0 {
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
    mut v_t_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2442_: u8 = 0;
    let mut v_r_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2442_ = l_Std_TreeSet_isEmpty___redArg(v_t_2441_);
    crate::leanh::lean_dec(v_t_2441_);
    v_r_2443_ = crate::leanh::lean_box((v_res_2442_) as usize);
    return v_r_2443_;
}
pub unsafe fn l_Std_TreeSet_isEmpty(
    mut v_00_u03b1_2444_: *mut crate::leanh::LeanObject,
    mut v_cmp_2445_: *mut crate::leanh::LeanObject,
    mut v_t_2446_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_2446_) == 0 {
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
    mut v_00_u03b1_2449_: *mut crate::leanh::LeanObject,
    mut v_cmp_2450_: *mut crate::leanh::LeanObject,
    mut v_t_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2452_: u8 = 0;
    let mut v_r_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2452_ = l_Std_TreeSet_isEmpty(v_00_u03b1_2449_, v_cmp_2450_, v_t_2451_);
    crate::leanh::lean_dec(v_t_2451_);
    crate::leanh::lean_dec_ref(v_cmp_2450_);
    v_r_2453_ = crate::leanh::lean_box((v_res_2452_) as usize);
    return v_r_2453_;
}
pub unsafe fn l_Std_TreeSet_erase___redArg(
    mut v_cmp_2454_: *mut crate::leanh::LeanObject,
    mut v_t_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2454_, v_a_2456_, v_t_2455_);
    return v___x_2457_;
}
pub unsafe fn l_Std_TreeSet_erase(
    mut v_00_u03b1_2458_: *mut crate::leanh::LeanObject,
    mut v_cmp_2459_: *mut crate::leanh::LeanObject,
    mut v_t_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_2459_, v_a_2461_, v_t_2460_);
    return v___x_2462_;
}
pub unsafe fn l_Std_TreeSet_get_x3f___redArg(
    mut v_cmp_2463_: *mut crate::leanh::LeanObject,
    mut v_t_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2463_, v_t_2464_, v_a_2465_);
    return v___x_2466_;
}
pub unsafe fn l_Std_TreeSet_get_x3f(
    mut v_00_u03b1_2467_: *mut crate::leanh::LeanObject,
    mut v_cmp_2468_: *mut crate::leanh::LeanObject,
    mut v_t_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_2468_, v_t_2469_, v_a_2470_);
    return v___x_2471_;
}
pub unsafe fn l_Std_TreeSet_get___redArg(
    mut v_cmp_2472_: *mut crate::leanh::LeanObject,
    mut v_t_2473_: *mut crate::leanh::LeanObject,
    mut v_a_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2472_, v_t_2473_, v_a_2474_);
    return v___x_2475_;
}
pub unsafe fn l_Std_TreeSet_get(
    mut v_00_u03b1_2476_: *mut crate::leanh::LeanObject,
    mut v_cmp_2477_: *mut crate::leanh::LeanObject,
    mut v_t_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_h_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_2477_, v_t_2478_, v_a_2479_);
    return v___x_2481_;
}
pub unsafe fn l_Std_TreeSet_get_x21___redArg(
    mut v_cmp_2482_: *mut crate::leanh::LeanObject,
    mut v_inst_2483_: *mut crate::leanh::LeanObject,
    mut v_t_2484_: *mut crate::leanh::LeanObject,
    mut v_a_2485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2482_,
        v_t_2484_,
        v_a_2485_,
        v_inst_2483_,
    );
    return v___x_2486_;
}
pub unsafe fn l_Std_TreeSet_get_x21___redArg___boxed(
    mut v_cmp_2487_: *mut crate::leanh::LeanObject,
    mut v_inst_2488_: *mut crate::leanh::LeanObject,
    mut v_t_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Std_TreeSet_get_x21___redArg(v_cmp_2487_, v_inst_2488_, v_t_2489_, v_a_2490_);
    crate::leanh::lean_dec(v_inst_2488_);
    return v_res_2491_;
}
pub unsafe fn l_Std_TreeSet_get_x21(
    mut v_00_u03b1_2492_: *mut crate::leanh::LeanObject,
    mut v_cmp_2493_: *mut crate::leanh::LeanObject,
    mut v_inst_2494_: *mut crate::leanh::LeanObject,
    mut v_t_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_cmp_2493_,
        v_t_2495_,
        v_a_2496_,
        v_inst_2494_,
    );
    return v___x_2497_;
}
pub unsafe fn l_Std_TreeSet_get_x21___boxed(
    mut v_00_u03b1_2498_: *mut crate::leanh::LeanObject,
    mut v_cmp_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
    mut v_t_2501_: *mut crate::leanh::LeanObject,
    mut v_a_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2503_ = l_Std_TreeSet_get_x21(
        v_00_u03b1_2498_,
        v_cmp_2499_,
        v_inst_2500_,
        v_t_2501_,
        v_a_2502_,
    );
    crate::leanh::lean_dec(v_inst_2500_);
    return v_res_2503_;
}
pub unsafe fn l_Std_TreeSet_getD___redArg(
    mut v_cmp_2504_: *mut crate::leanh::LeanObject,
    mut v_t_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_fallback_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2504_,
        v_t_2505_,
        v_a_2506_,
        v_fallback_2507_,
    );
    return v___x_2508_;
}
pub unsafe fn l_Std_TreeSet_getD___redArg___boxed(
    mut v_cmp_2509_: *mut crate::leanh::LeanObject,
    mut v_t_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_fallback_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Std_TreeSet_getD___redArg(v_cmp_2509_, v_t_2510_, v_a_2511_, v_fallback_2512_);
    crate::leanh::lean_dec(v_fallback_2512_);
    return v_res_2513_;
}
pub unsafe fn l_Std_TreeSet_getD(
    mut v_00_u03b1_2514_: *mut crate::leanh::LeanObject,
    mut v_cmp_2515_: *mut crate::leanh::LeanObject,
    mut v_t_2516_: *mut crate::leanh::LeanObject,
    mut v_a_2517_: *mut crate::leanh::LeanObject,
    mut v_fallback_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_cmp_2515_,
        v_t_2516_,
        v_a_2517_,
        v_fallback_2518_,
    );
    return v___x_2519_;
}
pub unsafe fn l_Std_TreeSet_getD___boxed(
    mut v_00_u03b1_2520_: *mut crate::leanh::LeanObject,
    mut v_cmp_2521_: *mut crate::leanh::LeanObject,
    mut v_t_2522_: *mut crate::leanh::LeanObject,
    mut v_a_2523_: *mut crate::leanh::LeanObject,
    mut v_fallback_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Std_TreeSet_getD(
        v_00_u03b1_2520_,
        v_cmp_2521_,
        v_t_2522_,
        v_a_2523_,
        v_fallback_2524_,
    );
    crate::leanh::lean_dec(v_fallback_2524_);
    return v_res_2525_;
}
pub unsafe fn l_Std_TreeSet_min_x3f___redArg(
    mut v_t_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2526_);
    return v___x_2527_;
}
pub unsafe fn l_Std_TreeSet_min_x3f___redArg___boxed(
    mut v_t_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_TreeSet_min_x3f___redArg(v_t_2528_);
    crate::leanh::lean_dec(v_t_2528_);
    return v_res_2529_;
}
pub unsafe fn l_Std_TreeSet_min_x3f(
    mut v_00_u03b1_2530_: *mut crate::leanh::LeanObject,
    mut v_cmp_2531_: *mut crate::leanh::LeanObject,
    mut v_t_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_2532_);
    return v___x_2533_;
}
pub unsafe fn l_Std_TreeSet_min_x3f___boxed(
    mut v_00_u03b1_2534_: *mut crate::leanh::LeanObject,
    mut v_cmp_2535_: *mut crate::leanh::LeanObject,
    mut v_t_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Std_TreeSet_min_x3f(v_00_u03b1_2534_, v_cmp_2535_, v_t_2536_);
    crate::leanh::lean_dec(v_t_2536_);
    crate::leanh::lean_dec_ref(v_cmp_2535_);
    return v_res_2537_;
}
pub unsafe fn l_Std_TreeSet_min___redArg(
    mut v_t_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2538_);
    return v___x_2539_;
}
pub unsafe fn l_Std_TreeSet_min___redArg___boxed(
    mut v_t_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2541_ = l_Std_TreeSet_min___redArg(v_t_2540_);
    crate::leanh::lean_dec(v_t_2540_);
    return v_res_2541_;
}
pub unsafe fn l_Std_TreeSet_min(
    mut v_00_u03b1_2542_: *mut crate::leanh::LeanObject,
    mut v_cmp_2543_: *mut crate::leanh::LeanObject,
    mut v_t_2544_: *mut crate::leanh::LeanObject,
    mut v_h_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_t_2544_);
    return v___x_2546_;
}
pub unsafe fn l_Std_TreeSet_min___boxed(
    mut v_00_u03b1_2547_: *mut crate::leanh::LeanObject,
    mut v_cmp_2548_: *mut crate::leanh::LeanObject,
    mut v_t_2549_: *mut crate::leanh::LeanObject,
    mut v_h_2550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_Std_TreeSet_min(v_00_u03b1_2547_, v_cmp_2548_, v_t_2549_, v_h_2550_);
    crate::leanh::lean_dec(v_t_2549_);
    crate::leanh::lean_dec_ref(v_cmp_2548_);
    return v_res_2551_;
}
pub unsafe fn l_Std_TreeSet_min_x21___redArg(
    mut v_inst_2552_: *mut crate::leanh::LeanObject,
    mut v_t_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2552_, v_t_2553_);
    return v___x_2554_;
}
pub unsafe fn l_Std_TreeSet_min_x21___redArg___boxed(
    mut v_inst_2555_: *mut crate::leanh::LeanObject,
    mut v_t_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Std_TreeSet_min_x21___redArg(v_inst_2555_, v_t_2556_);
    crate::leanh::lean_dec(v_t_2556_);
    crate::leanh::lean_dec(v_inst_2555_);
    return v_res_2557_;
}
pub unsafe fn l_Std_TreeSet_min_x21(
    mut v_00_u03b1_2558_: *mut crate::leanh::LeanObject,
    mut v_cmp_2559_: *mut crate::leanh::LeanObject,
    mut v_inst_2560_: *mut crate::leanh::LeanObject,
    mut v_t_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_2560_, v_t_2561_);
    return v___x_2562_;
}
pub unsafe fn l_Std_TreeSet_min_x21___boxed(
    mut v_00_u03b1_2563_: *mut crate::leanh::LeanObject,
    mut v_cmp_2564_: *mut crate::leanh::LeanObject,
    mut v_inst_2565_: *mut crate::leanh::LeanObject,
    mut v_t_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2567_ = l_Std_TreeSet_min_x21(v_00_u03b1_2563_, v_cmp_2564_, v_inst_2565_, v_t_2566_);
    crate::leanh::lean_dec(v_t_2566_);
    crate::leanh::lean_dec(v_inst_2565_);
    crate::leanh::lean_dec_ref(v_cmp_2564_);
    return v_res_2567_;
}
pub unsafe fn l_Std_TreeSet_minD___redArg(
    mut v_t_2568_: *mut crate::leanh::LeanObject,
    mut v_fallback_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2568_, v_fallback_2569_);
    return v___x_2570_;
}
pub unsafe fn l_Std_TreeSet_minD___redArg___boxed(
    mut v_t_2571_: *mut crate::leanh::LeanObject,
    mut v_fallback_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2573_ = l_Std_TreeSet_minD___redArg(v_t_2571_, v_fallback_2572_);
    crate::leanh::lean_dec(v_fallback_2572_);
    crate::leanh::lean_dec(v_t_2571_);
    return v_res_2573_;
}
pub unsafe fn l_Std_TreeSet_minD(
    mut v_00_u03b1_2574_: *mut crate::leanh::LeanObject,
    mut v_cmp_2575_: *mut crate::leanh::LeanObject,
    mut v_t_2576_: *mut crate::leanh::LeanObject,
    mut v_fallback_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_2576_, v_fallback_2577_);
    return v___x_2578_;
}
pub unsafe fn l_Std_TreeSet_minD___boxed(
    mut v_00_u03b1_2579_: *mut crate::leanh::LeanObject,
    mut v_cmp_2580_: *mut crate::leanh::LeanObject,
    mut v_t_2581_: *mut crate::leanh::LeanObject,
    mut v_fallback_2582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2583_ = l_Std_TreeSet_minD(v_00_u03b1_2579_, v_cmp_2580_, v_t_2581_, v_fallback_2582_);
    crate::leanh::lean_dec(v_fallback_2582_);
    crate::leanh::lean_dec(v_t_2581_);
    crate::leanh::lean_dec_ref(v_cmp_2580_);
    return v_res_2583_;
}
pub unsafe fn l_Std_TreeSet_max_x3f___redArg(
    mut v_t_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2585_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2584_);
    return v___x_2585_;
}
pub unsafe fn l_Std_TreeSet_max_x3f___redArg___boxed(
    mut v_t_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Std_TreeSet_max_x3f___redArg(v_t_2586_);
    crate::leanh::lean_dec(v_t_2586_);
    return v_res_2587_;
}
pub unsafe fn l_Std_TreeSet_max_x3f(
    mut v_00_u03b1_2588_: *mut crate::leanh::LeanObject,
    mut v_cmp_2589_: *mut crate::leanh::LeanObject,
    mut v_t_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_2590_);
    return v___x_2591_;
}
pub unsafe fn l_Std_TreeSet_max_x3f___boxed(
    mut v_00_u03b1_2592_: *mut crate::leanh::LeanObject,
    mut v_cmp_2593_: *mut crate::leanh::LeanObject,
    mut v_t_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_Std_TreeSet_max_x3f(v_00_u03b1_2592_, v_cmp_2593_, v_t_2594_);
    crate::leanh::lean_dec(v_t_2594_);
    crate::leanh::lean_dec_ref(v_cmp_2593_);
    return v_res_2595_;
}
pub unsafe fn l_Std_TreeSet_max___redArg(
    mut v_t_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2597_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2596_);
    return v___x_2597_;
}
pub unsafe fn l_Std_TreeSet_max___redArg___boxed(
    mut v_t_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2599_ = l_Std_TreeSet_max___redArg(v_t_2598_);
    crate::leanh::lean_dec(v_t_2598_);
    return v_res_2599_;
}
pub unsafe fn l_Std_TreeSet_max(
    mut v_00_u03b1_2600_: *mut crate::leanh::LeanObject,
    mut v_cmp_2601_: *mut crate::leanh::LeanObject,
    mut v_t_2602_: *mut crate::leanh::LeanObject,
    mut v_h_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_t_2602_);
    return v___x_2604_;
}
pub unsafe fn l_Std_TreeSet_max___boxed(
    mut v_00_u03b1_2605_: *mut crate::leanh::LeanObject,
    mut v_cmp_2606_: *mut crate::leanh::LeanObject,
    mut v_t_2607_: *mut crate::leanh::LeanObject,
    mut v_h_2608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2609_ = l_Std_TreeSet_max(v_00_u03b1_2605_, v_cmp_2606_, v_t_2607_, v_h_2608_);
    crate::leanh::lean_dec(v_t_2607_);
    crate::leanh::lean_dec_ref(v_cmp_2606_);
    return v_res_2609_;
}
pub unsafe fn l_Std_TreeSet_max_x21___redArg(
    mut v_inst_2610_: *mut crate::leanh::LeanObject,
    mut v_t_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2610_, v_t_2611_);
    return v___x_2612_;
}
pub unsafe fn l_Std_TreeSet_max_x21___redArg___boxed(
    mut v_inst_2613_: *mut crate::leanh::LeanObject,
    mut v_t_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2615_ = l_Std_TreeSet_max_x21___redArg(v_inst_2613_, v_t_2614_);
    crate::leanh::lean_dec(v_t_2614_);
    crate::leanh::lean_dec(v_inst_2613_);
    return v_res_2615_;
}
pub unsafe fn l_Std_TreeSet_max_x21(
    mut v_00_u03b1_2616_: *mut crate::leanh::LeanObject,
    mut v_cmp_2617_: *mut crate::leanh::LeanObject,
    mut v_inst_2618_: *mut crate::leanh::LeanObject,
    mut v_t_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2620_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_2618_, v_t_2619_);
    return v___x_2620_;
}
pub unsafe fn l_Std_TreeSet_max_x21___boxed(
    mut v_00_u03b1_2621_: *mut crate::leanh::LeanObject,
    mut v_cmp_2622_: *mut crate::leanh::LeanObject,
    mut v_inst_2623_: *mut crate::leanh::LeanObject,
    mut v_t_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Std_TreeSet_max_x21(v_00_u03b1_2621_, v_cmp_2622_, v_inst_2623_, v_t_2624_);
    crate::leanh::lean_dec(v_t_2624_);
    crate::leanh::lean_dec(v_inst_2623_);
    crate::leanh::lean_dec_ref(v_cmp_2622_);
    return v_res_2625_;
}
pub unsafe fn l_Std_TreeSet_maxD___redArg(
    mut v_t_2626_: *mut crate::leanh::LeanObject,
    mut v_fallback_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2628_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2626_, v_fallback_2627_);
    return v___x_2628_;
}
pub unsafe fn l_Std_TreeSet_maxD___redArg___boxed(
    mut v_t_2629_: *mut crate::leanh::LeanObject,
    mut v_fallback_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2631_ = l_Std_TreeSet_maxD___redArg(v_t_2629_, v_fallback_2630_);
    crate::leanh::lean_dec(v_fallback_2630_);
    crate::leanh::lean_dec(v_t_2629_);
    return v_res_2631_;
}
pub unsafe fn l_Std_TreeSet_maxD(
    mut v_00_u03b1_2632_: *mut crate::leanh::LeanObject,
    mut v_cmp_2633_: *mut crate::leanh::LeanObject,
    mut v_t_2634_: *mut crate::leanh::LeanObject,
    mut v_fallback_2635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_2634_, v_fallback_2635_);
    return v___x_2636_;
}
pub unsafe fn l_Std_TreeSet_maxD___boxed(
    mut v_00_u03b1_2637_: *mut crate::leanh::LeanObject,
    mut v_cmp_2638_: *mut crate::leanh::LeanObject,
    mut v_t_2639_: *mut crate::leanh::LeanObject,
    mut v_fallback_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2641_ = l_Std_TreeSet_maxD(v_00_u03b1_2637_, v_cmp_2638_, v_t_2639_, v_fallback_2640_);
    crate::leanh::lean_dec(v_fallback_2640_);
    crate::leanh::lean_dec(v_t_2639_);
    crate::leanh::lean_dec_ref(v_cmp_2638_);
    return v_res_2641_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f___redArg(
    mut v_t_2642_: *mut crate::leanh::LeanObject,
    mut v_n_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2642_, v_n_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f___redArg___boxed(
    mut v_t_2645_: *mut crate::leanh::LeanObject,
    mut v_n_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l_Std_TreeSet_atIdx_x3f___redArg(v_t_2645_, v_n_2646_);
    crate::leanh::lean_dec(v_t_2645_);
    return v_res_2647_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f(
    mut v_00_u03b1_2648_: *mut crate::leanh::LeanObject,
    mut v_cmp_2649_: *mut crate::leanh::LeanObject,
    mut v_t_2650_: *mut crate::leanh::LeanObject,
    mut v_n_2651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_2650_, v_n_2651_);
    return v___x_2652_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x3f___boxed(
    mut v_00_u03b1_2653_: *mut crate::leanh::LeanObject,
    mut v_cmp_2654_: *mut crate::leanh::LeanObject,
    mut v_t_2655_: *mut crate::leanh::LeanObject,
    mut v_n_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Std_TreeSet_atIdx_x3f(v_00_u03b1_2653_, v_cmp_2654_, v_t_2655_, v_n_2656_);
    crate::leanh::lean_dec(v_t_2655_);
    crate::leanh::lean_dec_ref(v_cmp_2654_);
    return v_res_2657_;
}
pub unsafe fn l_Std_TreeSet_atIdx___redArg(
    mut v_t_2658_: *mut crate::leanh::LeanObject,
    mut v_n_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2660_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2658_, v_n_2659_);
    return v___x_2660_;
}
pub unsafe fn l_Std_TreeSet_atIdx___redArg___boxed(
    mut v_t_2661_: *mut crate::leanh::LeanObject,
    mut v_n_2662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2663_ = l_Std_TreeSet_atIdx___redArg(v_t_2661_, v_n_2662_);
    crate::leanh::lean_dec(v_t_2661_);
    return v_res_2663_;
}
pub unsafe fn l_Std_TreeSet_atIdx(
    mut v_00_u03b1_2664_: *mut crate::leanh::LeanObject,
    mut v_cmp_2665_: *mut crate::leanh::LeanObject,
    mut v_t_2666_: *mut crate::leanh::LeanObject,
    mut v_n_2667_: *mut crate::leanh::LeanObject,
    mut v_h_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_t_2666_, v_n_2667_);
    return v___x_2669_;
}
pub unsafe fn l_Std_TreeSet_atIdx___boxed(
    mut v_00_u03b1_2670_: *mut crate::leanh::LeanObject,
    mut v_cmp_2671_: *mut crate::leanh::LeanObject,
    mut v_t_2672_: *mut crate::leanh::LeanObject,
    mut v_n_2673_: *mut crate::leanh::LeanObject,
    mut v_h_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2675_ = l_Std_TreeSet_atIdx(
        v_00_u03b1_2670_,
        v_cmp_2671_,
        v_t_2672_,
        v_n_2673_,
        v_h_2674_,
    );
    crate::leanh::lean_dec(v_t_2672_);
    crate::leanh::lean_dec_ref(v_cmp_2671_);
    return v_res_2675_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21___redArg(
    mut v_inst_2676_: *mut crate::leanh::LeanObject,
    mut v_t_2677_: *mut crate::leanh::LeanObject,
    mut v_n_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2679_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2676_, v_t_2677_, v_n_2678_);
    return v___x_2679_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21___redArg___boxed(
    mut v_inst_2680_: *mut crate::leanh::LeanObject,
    mut v_t_2681_: *mut crate::leanh::LeanObject,
    mut v_n_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2683_ = l_Std_TreeSet_atIdx_x21___redArg(v_inst_2680_, v_t_2681_, v_n_2682_);
    crate::leanh::lean_dec(v_t_2681_);
    crate::leanh::lean_dec(v_inst_2680_);
    return v_res_2683_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21(
    mut v_00_u03b1_2684_: *mut crate::leanh::LeanObject,
    mut v_cmp_2685_: *mut crate::leanh::LeanObject,
    mut v_inst_2686_: *mut crate::leanh::LeanObject,
    mut v_t_2687_: *mut crate::leanh::LeanObject,
    mut v_n_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2689_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2686_, v_t_2687_, v_n_2688_);
    return v___x_2689_;
}
pub unsafe fn l_Std_TreeSet_atIdx_x21___boxed(
    mut v_00_u03b1_2690_: *mut crate::leanh::LeanObject,
    mut v_cmp_2691_: *mut crate::leanh::LeanObject,
    mut v_inst_2692_: *mut crate::leanh::LeanObject,
    mut v_t_2693_: *mut crate::leanh::LeanObject,
    mut v_n_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_Std_TreeSet_atIdx_x21(
        v_00_u03b1_2690_,
        v_cmp_2691_,
        v_inst_2692_,
        v_t_2693_,
        v_n_2694_,
    );
    crate::leanh::lean_dec(v_t_2693_);
    crate::leanh::lean_dec(v_inst_2692_);
    crate::leanh::lean_dec_ref(v_cmp_2691_);
    return v_res_2695_;
}
pub unsafe fn l_Std_TreeSet_atIdxD___redArg(
    mut v_t_2696_: *mut crate::leanh::LeanObject,
    mut v_n_2697_: *mut crate::leanh::LeanObject,
    mut v_fallback_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2699_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2696_, v_n_2697_, v_fallback_2698_);
    return v___x_2699_;
}
pub unsafe fn l_Std_TreeSet_atIdxD___redArg___boxed(
    mut v_t_2700_: *mut crate::leanh::LeanObject,
    mut v_n_2701_: *mut crate::leanh::LeanObject,
    mut v_fallback_2702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2703_ = l_Std_TreeSet_atIdxD___redArg(v_t_2700_, v_n_2701_, v_fallback_2702_);
    crate::leanh::lean_dec(v_fallback_2702_);
    crate::leanh::lean_dec(v_t_2700_);
    return v_res_2703_;
}
pub unsafe fn l_Std_TreeSet_atIdxD(
    mut v_00_u03b1_2704_: *mut crate::leanh::LeanObject,
    mut v_cmp_2705_: *mut crate::leanh::LeanObject,
    mut v_t_2706_: *mut crate::leanh::LeanObject,
    mut v_n_2707_: *mut crate::leanh::LeanObject,
    mut v_fallback_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2709_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_2706_, v_n_2707_, v_fallback_2708_);
    return v___x_2709_;
}
pub unsafe fn l_Std_TreeSet_atIdxD___boxed(
    mut v_00_u03b1_2710_: *mut crate::leanh::LeanObject,
    mut v_cmp_2711_: *mut crate::leanh::LeanObject,
    mut v_t_2712_: *mut crate::leanh::LeanObject,
    mut v_n_2713_: *mut crate::leanh::LeanObject,
    mut v_fallback_2714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2715_ = l_Std_TreeSet_atIdxD(
        v_00_u03b1_2710_,
        v_cmp_2711_,
        v_t_2712_,
        v_n_2713_,
        v_fallback_2714_,
    );
    crate::leanh::lean_dec(v_fallback_2714_);
    crate::leanh::lean_dec(v_t_2712_);
    crate::leanh::lean_dec_ref(v_cmp_2711_);
    return v_res_2715_;
}
pub unsafe fn l_Std_TreeSet_getGE_x3f___redArg(
    mut v_cmp_2716_: *mut crate::leanh::LeanObject,
    mut v_t_2717_: *mut crate::leanh::LeanObject,
    mut v_k_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2719_ = crate::leanh::lean_box(0);
    v___x_2720_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2716_,
        v_k_2718_,
        v___x_2719_,
        v_t_2717_,
    );
    return v___x_2720_;
}
pub unsafe fn l_Std_TreeSet_getGE_x3f(
    mut v_00_u03b1_2721_: *mut crate::leanh::LeanObject,
    mut v_cmp_2722_: *mut crate::leanh::LeanObject,
    mut v_t_2723_: *mut crate::leanh::LeanObject,
    mut v_k_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = crate::leanh::lean_box(0);
    v___x_2726_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2722_,
        v_k_2724_,
        v___x_2725_,
        v_t_2723_,
    );
    return v___x_2726_;
}
pub unsafe fn l_Std_TreeSet_getGT_x3f___redArg(
    mut v_cmp_2727_: *mut crate::leanh::LeanObject,
    mut v_t_2728_: *mut crate::leanh::LeanObject,
    mut v_k_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = crate::leanh::lean_box(0);
    v___x_2731_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2727_,
        v_k_2729_,
        v___x_2730_,
        v_t_2728_,
    );
    return v___x_2731_;
}
pub unsafe fn l_Std_TreeSet_getGT_x3f(
    mut v_00_u03b1_2732_: *mut crate::leanh::LeanObject,
    mut v_cmp_2733_: *mut crate::leanh::LeanObject,
    mut v_t_2734_: *mut crate::leanh::LeanObject,
    mut v_k_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2736_ = crate::leanh::lean_box(0);
    v___x_2737_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2733_,
        v_k_2735_,
        v___x_2736_,
        v_t_2734_,
    );
    return v___x_2737_;
}
pub unsafe fn l_Std_TreeSet_getLE_x3f___redArg(
    mut v_cmp_2738_: *mut crate::leanh::LeanObject,
    mut v_t_2739_: *mut crate::leanh::LeanObject,
    mut v_k_2740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = crate::leanh::lean_box(0);
    v___x_2742_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2738_,
        v_k_2740_,
        v___x_2741_,
        v_t_2739_,
    );
    return v___x_2742_;
}
pub unsafe fn l_Std_TreeSet_getLE_x3f(
    mut v_00_u03b1_2743_: *mut crate::leanh::LeanObject,
    mut v_cmp_2744_: *mut crate::leanh::LeanObject,
    mut v_t_2745_: *mut crate::leanh::LeanObject,
    mut v_k_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2747_ = crate::leanh::lean_box(0);
    v___x_2748_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2744_,
        v_k_2746_,
        v___x_2747_,
        v_t_2745_,
    );
    return v___x_2748_;
}
pub unsafe fn l_Std_TreeSet_getLT_x3f___redArg(
    mut v_cmp_2749_: *mut crate::leanh::LeanObject,
    mut v_t_2750_: *mut crate::leanh::LeanObject,
    mut v_k_2751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = crate::leanh::lean_box(0);
    v___x_2753_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2749_,
        v_k_2751_,
        v___x_2752_,
        v_t_2750_,
    );
    return v___x_2753_;
}
pub unsafe fn l_Std_TreeSet_getLT_x3f(
    mut v_00_u03b1_2754_: *mut crate::leanh::LeanObject,
    mut v_cmp_2755_: *mut crate::leanh::LeanObject,
    mut v_t_2756_: *mut crate::leanh::LeanObject,
    mut v_k_2757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2758_ = crate::leanh::lean_box(0);
    v___x_2759_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2755_,
        v_k_2757_,
        v___x_2758_,
        v_t_2756_,
    );
    return v___x_2759_;
}
pub unsafe fn _init_l_Std_TreeSet_getGE_x21___redArg___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2763_ = l_Std_TreeSet_getGE_x21___redArg___closed__2;
    v___x_2764_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2765_ = crate::leanh::lean_unsigned_to_nat(22);
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
    mut v_cmp_2769_: *mut crate::leanh::LeanObject,
    mut v_inst_2770_: *mut crate::leanh::LeanObject,
    mut v_t_2771_: *mut crate::leanh::LeanObject,
    mut v_k_2772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2773_ = crate::leanh::lean_box(0);
    v___x_2774_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2769_,
        v_k_2772_,
        v___x_2773_,
        v_t_2771_,
    );
    if crate::leanh::lean_obj_tag(v___x_2774_) == 0 {
        let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2775_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2776_ = l_panic___redArg(v_inst_2770_, v___x_2775_);
        return v___x_2776_;
    } else {
        let mut v_val_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2777_ = crate::leanh::lean_ctor_get(v___x_2774_, 0);
        crate::leanh::lean_inc(v_val_2777_);
        crate::leanh::lean_dec_ref_known(v___x_2774_, 1);
        return v_val_2777_;
    }
}
pub unsafe fn l_Std_TreeSet_getGE_x21___redArg___boxed(
    mut v_cmp_2778_: *mut crate::leanh::LeanObject,
    mut v_inst_2779_: *mut crate::leanh::LeanObject,
    mut v_t_2780_: *mut crate::leanh::LeanObject,
    mut v_k_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2782_ = l_Std_TreeSet_getGE_x21___redArg(v_cmp_2778_, v_inst_2779_, v_t_2780_, v_k_2781_);
    crate::leanh::lean_dec(v_inst_2779_);
    return v_res_2782_;
}
pub unsafe fn l_Std_TreeSet_getGE_x21(
    mut v_00_u03b1_2783_: *mut crate::leanh::LeanObject,
    mut v_cmp_2784_: *mut crate::leanh::LeanObject,
    mut v_inst_2785_: *mut crate::leanh::LeanObject,
    mut v_t_2786_: *mut crate::leanh::LeanObject,
    mut v_k_2787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2788_ = crate::leanh::lean_box(0);
    v___x_2789_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2784_,
        v_k_2787_,
        v___x_2788_,
        v_t_2786_,
    );
    if crate::leanh::lean_obj_tag(v___x_2789_) == 0 {
        let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2790_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2791_ = l_panic___redArg(v_inst_2785_, v___x_2790_);
        return v___x_2791_;
    } else {
        let mut v_val_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2792_ = crate::leanh::lean_ctor_get(v___x_2789_, 0);
        crate::leanh::lean_inc(v_val_2792_);
        crate::leanh::lean_dec_ref_known(v___x_2789_, 1);
        return v_val_2792_;
    }
}
pub unsafe fn l_Std_TreeSet_getGE_x21___boxed(
    mut v_00_u03b1_2793_: *mut crate::leanh::LeanObject,
    mut v_cmp_2794_: *mut crate::leanh::LeanObject,
    mut v_inst_2795_: *mut crate::leanh::LeanObject,
    mut v_t_2796_: *mut crate::leanh::LeanObject,
    mut v_k_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Std_TreeSet_getGE_x21(
        v_00_u03b1_2793_,
        v_cmp_2794_,
        v_inst_2795_,
        v_t_2796_,
        v_k_2797_,
    );
    crate::leanh::lean_dec(v_inst_2795_);
    return v_res_2798_;
}
pub unsafe fn l_Std_TreeSet_getGT_x21___redArg(
    mut v_cmp_2799_: *mut crate::leanh::LeanObject,
    mut v_inst_2800_: *mut crate::leanh::LeanObject,
    mut v_t_2801_: *mut crate::leanh::LeanObject,
    mut v_k_2802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2803_ = crate::leanh::lean_box(0);
    v___x_2804_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2799_,
        v_k_2802_,
        v___x_2803_,
        v_t_2801_,
    );
    if crate::leanh::lean_obj_tag(v___x_2804_) == 0 {
        let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2805_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2806_ = l_panic___redArg(v_inst_2800_, v___x_2805_);
        return v___x_2806_;
    } else {
        let mut v_val_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2807_ = crate::leanh::lean_ctor_get(v___x_2804_, 0);
        crate::leanh::lean_inc(v_val_2807_);
        crate::leanh::lean_dec_ref_known(v___x_2804_, 1);
        return v_val_2807_;
    }
}
pub unsafe fn l_Std_TreeSet_getGT_x21___redArg___boxed(
    mut v_cmp_2808_: *mut crate::leanh::LeanObject,
    mut v_inst_2809_: *mut crate::leanh::LeanObject,
    mut v_t_2810_: *mut crate::leanh::LeanObject,
    mut v_k_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2812_ = l_Std_TreeSet_getGT_x21___redArg(v_cmp_2808_, v_inst_2809_, v_t_2810_, v_k_2811_);
    crate::leanh::lean_dec(v_inst_2809_);
    return v_res_2812_;
}
pub unsafe fn l_Std_TreeSet_getGT_x21(
    mut v_00_u03b1_2813_: *mut crate::leanh::LeanObject,
    mut v_cmp_2814_: *mut crate::leanh::LeanObject,
    mut v_inst_2815_: *mut crate::leanh::LeanObject,
    mut v_t_2816_: *mut crate::leanh::LeanObject,
    mut v_k_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2818_ = crate::leanh::lean_box(0);
    v___x_2819_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2814_,
        v_k_2817_,
        v___x_2818_,
        v_t_2816_,
    );
    if crate::leanh::lean_obj_tag(v___x_2819_) == 0 {
        let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2820_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2821_ = l_panic___redArg(v_inst_2815_, v___x_2820_);
        return v___x_2821_;
    } else {
        let mut v_val_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2822_ = crate::leanh::lean_ctor_get(v___x_2819_, 0);
        crate::leanh::lean_inc(v_val_2822_);
        crate::leanh::lean_dec_ref_known(v___x_2819_, 1);
        return v_val_2822_;
    }
}
pub unsafe fn l_Std_TreeSet_getGT_x21___boxed(
    mut v_00_u03b1_2823_: *mut crate::leanh::LeanObject,
    mut v_cmp_2824_: *mut crate::leanh::LeanObject,
    mut v_inst_2825_: *mut crate::leanh::LeanObject,
    mut v_t_2826_: *mut crate::leanh::LeanObject,
    mut v_k_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2828_ = l_Std_TreeSet_getGT_x21(
        v_00_u03b1_2823_,
        v_cmp_2824_,
        v_inst_2825_,
        v_t_2826_,
        v_k_2827_,
    );
    crate::leanh::lean_dec(v_inst_2825_);
    return v_res_2828_;
}
pub unsafe fn l_Std_TreeSet_getLE_x21___redArg(
    mut v_cmp_2829_: *mut crate::leanh::LeanObject,
    mut v_inst_2830_: *mut crate::leanh::LeanObject,
    mut v_t_2831_: *mut crate::leanh::LeanObject,
    mut v_k_2832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2833_ = crate::leanh::lean_box(0);
    v___x_2834_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2829_,
        v_k_2832_,
        v___x_2833_,
        v_t_2831_,
    );
    if crate::leanh::lean_obj_tag(v___x_2834_) == 0 {
        let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2835_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2836_ = l_panic___redArg(v_inst_2830_, v___x_2835_);
        return v___x_2836_;
    } else {
        let mut v_val_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2837_ = crate::leanh::lean_ctor_get(v___x_2834_, 0);
        crate::leanh::lean_inc(v_val_2837_);
        crate::leanh::lean_dec_ref_known(v___x_2834_, 1);
        return v_val_2837_;
    }
}
pub unsafe fn l_Std_TreeSet_getLE_x21___redArg___boxed(
    mut v_cmp_2838_: *mut crate::leanh::LeanObject,
    mut v_inst_2839_: *mut crate::leanh::LeanObject,
    mut v_t_2840_: *mut crate::leanh::LeanObject,
    mut v_k_2841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2842_ = l_Std_TreeSet_getLE_x21___redArg(v_cmp_2838_, v_inst_2839_, v_t_2840_, v_k_2841_);
    crate::leanh::lean_dec(v_inst_2839_);
    return v_res_2842_;
}
pub unsafe fn l_Std_TreeSet_getLE_x21(
    mut v_00_u03b1_2843_: *mut crate::leanh::LeanObject,
    mut v_cmp_2844_: *mut crate::leanh::LeanObject,
    mut v_inst_2845_: *mut crate::leanh::LeanObject,
    mut v_t_2846_: *mut crate::leanh::LeanObject,
    mut v_k_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = crate::leanh::lean_box(0);
    v___x_2849_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2844_,
        v_k_2847_,
        v___x_2848_,
        v_t_2846_,
    );
    if crate::leanh::lean_obj_tag(v___x_2849_) == 0 {
        let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2850_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2851_ = l_panic___redArg(v_inst_2845_, v___x_2850_);
        return v___x_2851_;
    } else {
        let mut v_val_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2852_ = crate::leanh::lean_ctor_get(v___x_2849_, 0);
        crate::leanh::lean_inc(v_val_2852_);
        crate::leanh::lean_dec_ref_known(v___x_2849_, 1);
        return v_val_2852_;
    }
}
pub unsafe fn l_Std_TreeSet_getLE_x21___boxed(
    mut v_00_u03b1_2853_: *mut crate::leanh::LeanObject,
    mut v_cmp_2854_: *mut crate::leanh::LeanObject,
    mut v_inst_2855_: *mut crate::leanh::LeanObject,
    mut v_t_2856_: *mut crate::leanh::LeanObject,
    mut v_k_2857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2858_ = l_Std_TreeSet_getLE_x21(
        v_00_u03b1_2853_,
        v_cmp_2854_,
        v_inst_2855_,
        v_t_2856_,
        v_k_2857_,
    );
    crate::leanh::lean_dec(v_inst_2855_);
    return v_res_2858_;
}
pub unsafe fn l_Std_TreeSet_getLT_x21___redArg(
    mut v_cmp_2859_: *mut crate::leanh::LeanObject,
    mut v_inst_2860_: *mut crate::leanh::LeanObject,
    mut v_t_2861_: *mut crate::leanh::LeanObject,
    mut v_k_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2863_ = crate::leanh::lean_box(0);
    v___x_2864_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2859_,
        v_k_2862_,
        v___x_2863_,
        v_t_2861_,
    );
    if crate::leanh::lean_obj_tag(v___x_2864_) == 0 {
        let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2865_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2866_ = l_panic___redArg(v_inst_2860_, v___x_2865_);
        return v___x_2866_;
    } else {
        let mut v_val_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2867_ = crate::leanh::lean_ctor_get(v___x_2864_, 0);
        crate::leanh::lean_inc(v_val_2867_);
        crate::leanh::lean_dec_ref_known(v___x_2864_, 1);
        return v_val_2867_;
    }
}
pub unsafe fn l_Std_TreeSet_getLT_x21___redArg___boxed(
    mut v_cmp_2868_: *mut crate::leanh::LeanObject,
    mut v_inst_2869_: *mut crate::leanh::LeanObject,
    mut v_t_2870_: *mut crate::leanh::LeanObject,
    mut v_k_2871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2872_ = l_Std_TreeSet_getLT_x21___redArg(v_cmp_2868_, v_inst_2869_, v_t_2870_, v_k_2871_);
    crate::leanh::lean_dec(v_inst_2869_);
    return v_res_2872_;
}
pub unsafe fn l_Std_TreeSet_getLT_x21(
    mut v_00_u03b1_2873_: *mut crate::leanh::LeanObject,
    mut v_cmp_2874_: *mut crate::leanh::LeanObject,
    mut v_inst_2875_: *mut crate::leanh::LeanObject,
    mut v_t_2876_: *mut crate::leanh::LeanObject,
    mut v_k_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ = crate::leanh::lean_box(0);
    v___x_2879_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2874_,
        v_k_2877_,
        v___x_2878_,
        v_t_2876_,
    );
    if crate::leanh::lean_obj_tag(v___x_2879_) == 0 {
        let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2880_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_TreeSet_getGE_x21___redArg___closed__3_once),
            _init_l_Std_TreeSet_getGE_x21___redArg___closed__3,
        );
        v___x_2881_ = l_panic___redArg(v_inst_2875_, v___x_2880_);
        return v___x_2881_;
    } else {
        let mut v_val_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2882_ = crate::leanh::lean_ctor_get(v___x_2879_, 0);
        crate::leanh::lean_inc(v_val_2882_);
        crate::leanh::lean_dec_ref_known(v___x_2879_, 1);
        return v_val_2882_;
    }
}
pub unsafe fn l_Std_TreeSet_getLT_x21___boxed(
    mut v_00_u03b1_2883_: *mut crate::leanh::LeanObject,
    mut v_cmp_2884_: *mut crate::leanh::LeanObject,
    mut v_inst_2885_: *mut crate::leanh::LeanObject,
    mut v_t_2886_: *mut crate::leanh::LeanObject,
    mut v_k_2887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_Std_TreeSet_getLT_x21(
        v_00_u03b1_2883_,
        v_cmp_2884_,
        v_inst_2885_,
        v_t_2886_,
        v_k_2887_,
    );
    crate::leanh::lean_dec(v_inst_2885_);
    return v_res_2888_;
}
pub unsafe fn l_Std_TreeSet_getGED___redArg(
    mut v_cmp_2889_: *mut crate::leanh::LeanObject,
    mut v_t_2890_: *mut crate::leanh::LeanObject,
    mut v_k_2891_: *mut crate::leanh::LeanObject,
    mut v_fallback_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2893_ = crate::leanh::lean_box(0);
    v___x_2894_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2889_,
        v_k_2891_,
        v___x_2893_,
        v_t_2890_,
    );
    if crate::leanh::lean_obj_tag(v___x_2894_) == 0 {
        crate::leanh::lean_inc(v_fallback_2892_);
        return v_fallback_2892_;
    } else {
        let mut v_val_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2895_ = crate::leanh::lean_ctor_get(v___x_2894_, 0);
        crate::leanh::lean_inc(v_val_2895_);
        crate::leanh::lean_dec_ref_known(v___x_2894_, 1);
        return v_val_2895_;
    }
}
pub unsafe fn l_Std_TreeSet_getGED___redArg___boxed(
    mut v_cmp_2896_: *mut crate::leanh::LeanObject,
    mut v_t_2897_: *mut crate::leanh::LeanObject,
    mut v_k_2898_: *mut crate::leanh::LeanObject,
    mut v_fallback_2899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2900_ =
        l_Std_TreeSet_getGED___redArg(v_cmp_2896_, v_t_2897_, v_k_2898_, v_fallback_2899_);
    crate::leanh::lean_dec(v_fallback_2899_);
    return v_res_2900_;
}
pub unsafe fn l_Std_TreeSet_getGED(
    mut v_00_u03b1_2901_: *mut crate::leanh::LeanObject,
    mut v_cmp_2902_: *mut crate::leanh::LeanObject,
    mut v_t_2903_: *mut crate::leanh::LeanObject,
    mut v_k_2904_: *mut crate::leanh::LeanObject,
    mut v_fallback_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2906_ = crate::leanh::lean_box(0);
    v___x_2907_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_cmp_2902_,
        v_k_2904_,
        v___x_2906_,
        v_t_2903_,
    );
    if crate::leanh::lean_obj_tag(v___x_2907_) == 0 {
        crate::leanh::lean_inc(v_fallback_2905_);
        return v_fallback_2905_;
    } else {
        let mut v_val_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2908_ = crate::leanh::lean_ctor_get(v___x_2907_, 0);
        crate::leanh::lean_inc(v_val_2908_);
        crate::leanh::lean_dec_ref_known(v___x_2907_, 1);
        return v_val_2908_;
    }
}
pub unsafe fn l_Std_TreeSet_getGED___boxed(
    mut v_00_u03b1_2909_: *mut crate::leanh::LeanObject,
    mut v_cmp_2910_: *mut crate::leanh::LeanObject,
    mut v_t_2911_: *mut crate::leanh::LeanObject,
    mut v_k_2912_: *mut crate::leanh::LeanObject,
    mut v_fallback_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2914_ = l_Std_TreeSet_getGED(
        v_00_u03b1_2909_,
        v_cmp_2910_,
        v_t_2911_,
        v_k_2912_,
        v_fallback_2913_,
    );
    crate::leanh::lean_dec(v_fallback_2913_);
    return v_res_2914_;
}
pub unsafe fn l_Std_TreeSet_getGTD___redArg(
    mut v_cmp_2915_: *mut crate::leanh::LeanObject,
    mut v_t_2916_: *mut crate::leanh::LeanObject,
    mut v_k_2917_: *mut crate::leanh::LeanObject,
    mut v_fallback_2918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = crate::leanh::lean_box(0);
    v___x_2920_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2915_,
        v_k_2917_,
        v___x_2919_,
        v_t_2916_,
    );
    if crate::leanh::lean_obj_tag(v___x_2920_) == 0 {
        crate::leanh::lean_inc(v_fallback_2918_);
        return v_fallback_2918_;
    } else {
        let mut v_val_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2921_ = crate::leanh::lean_ctor_get(v___x_2920_, 0);
        crate::leanh::lean_inc(v_val_2921_);
        crate::leanh::lean_dec_ref_known(v___x_2920_, 1);
        return v_val_2921_;
    }
}
pub unsafe fn l_Std_TreeSet_getGTD___redArg___boxed(
    mut v_cmp_2922_: *mut crate::leanh::LeanObject,
    mut v_t_2923_: *mut crate::leanh::LeanObject,
    mut v_k_2924_: *mut crate::leanh::LeanObject,
    mut v_fallback_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ =
        l_Std_TreeSet_getGTD___redArg(v_cmp_2922_, v_t_2923_, v_k_2924_, v_fallback_2925_);
    crate::leanh::lean_dec(v_fallback_2925_);
    return v_res_2926_;
}
pub unsafe fn l_Std_TreeSet_getGTD(
    mut v_00_u03b1_2927_: *mut crate::leanh::LeanObject,
    mut v_cmp_2928_: *mut crate::leanh::LeanObject,
    mut v_t_2929_: *mut crate::leanh::LeanObject,
    mut v_k_2930_: *mut crate::leanh::LeanObject,
    mut v_fallback_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = crate::leanh::lean_box(0);
    v___x_2933_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_cmp_2928_,
        v_k_2930_,
        v___x_2932_,
        v_t_2929_,
    );
    if crate::leanh::lean_obj_tag(v___x_2933_) == 0 {
        crate::leanh::lean_inc(v_fallback_2931_);
        return v_fallback_2931_;
    } else {
        let mut v_val_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2934_ = crate::leanh::lean_ctor_get(v___x_2933_, 0);
        crate::leanh::lean_inc(v_val_2934_);
        crate::leanh::lean_dec_ref_known(v___x_2933_, 1);
        return v_val_2934_;
    }
}
pub unsafe fn l_Std_TreeSet_getGTD___boxed(
    mut v_00_u03b1_2935_: *mut crate::leanh::LeanObject,
    mut v_cmp_2936_: *mut crate::leanh::LeanObject,
    mut v_t_2937_: *mut crate::leanh::LeanObject,
    mut v_k_2938_: *mut crate::leanh::LeanObject,
    mut v_fallback_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Std_TreeSet_getGTD(
        v_00_u03b1_2935_,
        v_cmp_2936_,
        v_t_2937_,
        v_k_2938_,
        v_fallback_2939_,
    );
    crate::leanh::lean_dec(v_fallback_2939_);
    return v_res_2940_;
}
pub unsafe fn l_Std_TreeSet_getLED___redArg(
    mut v_cmp_2941_: *mut crate::leanh::LeanObject,
    mut v_t_2942_: *mut crate::leanh::LeanObject,
    mut v_k_2943_: *mut crate::leanh::LeanObject,
    mut v_fallback_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2945_ = crate::leanh::lean_box(0);
    v___x_2946_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2941_,
        v_k_2943_,
        v___x_2945_,
        v_t_2942_,
    );
    if crate::leanh::lean_obj_tag(v___x_2946_) == 0 {
        crate::leanh::lean_inc(v_fallback_2944_);
        return v_fallback_2944_;
    } else {
        let mut v_val_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2947_ = crate::leanh::lean_ctor_get(v___x_2946_, 0);
        crate::leanh::lean_inc(v_val_2947_);
        crate::leanh::lean_dec_ref_known(v___x_2946_, 1);
        return v_val_2947_;
    }
}
pub unsafe fn l_Std_TreeSet_getLED___redArg___boxed(
    mut v_cmp_2948_: *mut crate::leanh::LeanObject,
    mut v_t_2949_: *mut crate::leanh::LeanObject,
    mut v_k_2950_: *mut crate::leanh::LeanObject,
    mut v_fallback_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ =
        l_Std_TreeSet_getLED___redArg(v_cmp_2948_, v_t_2949_, v_k_2950_, v_fallback_2951_);
    crate::leanh::lean_dec(v_fallback_2951_);
    return v_res_2952_;
}
pub unsafe fn l_Std_TreeSet_getLED(
    mut v_00_u03b1_2953_: *mut crate::leanh::LeanObject,
    mut v_cmp_2954_: *mut crate::leanh::LeanObject,
    mut v_t_2955_: *mut crate::leanh::LeanObject,
    mut v_k_2956_: *mut crate::leanh::LeanObject,
    mut v_fallback_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ = crate::leanh::lean_box(0);
    v___x_2959_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_cmp_2954_,
        v_k_2956_,
        v___x_2958_,
        v_t_2955_,
    );
    if crate::leanh::lean_obj_tag(v___x_2959_) == 0 {
        crate::leanh::lean_inc(v_fallback_2957_);
        return v_fallback_2957_;
    } else {
        let mut v_val_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2960_ = crate::leanh::lean_ctor_get(v___x_2959_, 0);
        crate::leanh::lean_inc(v_val_2960_);
        crate::leanh::lean_dec_ref_known(v___x_2959_, 1);
        return v_val_2960_;
    }
}
pub unsafe fn l_Std_TreeSet_getLED___boxed(
    mut v_00_u03b1_2961_: *mut crate::leanh::LeanObject,
    mut v_cmp_2962_: *mut crate::leanh::LeanObject,
    mut v_t_2963_: *mut crate::leanh::LeanObject,
    mut v_k_2964_: *mut crate::leanh::LeanObject,
    mut v_fallback_2965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Std_TreeSet_getLED(
        v_00_u03b1_2961_,
        v_cmp_2962_,
        v_t_2963_,
        v_k_2964_,
        v_fallback_2965_,
    );
    crate::leanh::lean_dec(v_fallback_2965_);
    return v_res_2966_;
}
pub unsafe fn l_Std_TreeSet_getLTD___redArg(
    mut v_cmp_2967_: *mut crate::leanh::LeanObject,
    mut v_t_2968_: *mut crate::leanh::LeanObject,
    mut v_k_2969_: *mut crate::leanh::LeanObject,
    mut v_fallback_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2971_ = crate::leanh::lean_box(0);
    v___x_2972_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2967_,
        v_k_2969_,
        v___x_2971_,
        v_t_2968_,
    );
    if crate::leanh::lean_obj_tag(v___x_2972_) == 0 {
        crate::leanh::lean_inc(v_fallback_2970_);
        return v_fallback_2970_;
    } else {
        let mut v_val_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2973_ = crate::leanh::lean_ctor_get(v___x_2972_, 0);
        crate::leanh::lean_inc(v_val_2973_);
        crate::leanh::lean_dec_ref_known(v___x_2972_, 1);
        return v_val_2973_;
    }
}
pub unsafe fn l_Std_TreeSet_getLTD___redArg___boxed(
    mut v_cmp_2974_: *mut crate::leanh::LeanObject,
    mut v_t_2975_: *mut crate::leanh::LeanObject,
    mut v_k_2976_: *mut crate::leanh::LeanObject,
    mut v_fallback_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ =
        l_Std_TreeSet_getLTD___redArg(v_cmp_2974_, v_t_2975_, v_k_2976_, v_fallback_2977_);
    crate::leanh::lean_dec(v_fallback_2977_);
    return v_res_2978_;
}
pub unsafe fn l_Std_TreeSet_getLTD(
    mut v_00_u03b1_2979_: *mut crate::leanh::LeanObject,
    mut v_cmp_2980_: *mut crate::leanh::LeanObject,
    mut v_t_2981_: *mut crate::leanh::LeanObject,
    mut v_k_2982_: *mut crate::leanh::LeanObject,
    mut v_fallback_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2984_ = crate::leanh::lean_box(0);
    v___x_2985_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_cmp_2980_,
        v_k_2982_,
        v___x_2984_,
        v_t_2981_,
    );
    if crate::leanh::lean_obj_tag(v___x_2985_) == 0 {
        crate::leanh::lean_inc(v_fallback_2983_);
        return v_fallback_2983_;
    } else {
        let mut v_val_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2986_ = crate::leanh::lean_ctor_get(v___x_2985_, 0);
        crate::leanh::lean_inc(v_val_2986_);
        crate::leanh::lean_dec_ref_known(v___x_2985_, 1);
        return v_val_2986_;
    }
}
pub unsafe fn l_Std_TreeSet_getLTD___boxed(
    mut v_00_u03b1_2987_: *mut crate::leanh::LeanObject,
    mut v_cmp_2988_: *mut crate::leanh::LeanObject,
    mut v_t_2989_: *mut crate::leanh::LeanObject,
    mut v_k_2990_: *mut crate::leanh::LeanObject,
    mut v_fallback_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2992_ = l_Std_TreeSet_getLTD(
        v_00_u03b1_2987_,
        v_cmp_2988_,
        v_t_2989_,
        v_k_2990_,
        v_fallback_2991_,
    );
    crate::leanh::lean_dec(v_fallback_2991_);
    return v_res_2992_;
}
pub unsafe fn l_Std_TreeSet_filter___redArg___lam__0(
    mut v_f_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
    mut v_x_2995_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    v___x_2996_ = crate::leanh::lean_apply_1(v_f_2993_, v_a_2994_);
    v___x_2997_ = (crate::leanh::lean_unbox(v___x_2996_) as u8);
    return v___x_2997_;
}
pub unsafe fn l_Std_TreeSet_filter___redArg___lam__0___boxed(
    mut v_f_2998_: *mut crate::leanh::LeanObject,
    mut v_a_2999_: *mut crate::leanh::LeanObject,
    mut v_x_3000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3001_: u8 = 0;
    let mut v_r_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3001_ = l_Std_TreeSet_filter___redArg___lam__0(v_f_2998_, v_a_2999_, v_x_3000_);
    v_r_3002_ = crate::leanh::lean_box((v_res_3001_) as usize);
    return v_r_3002_;
}
pub unsafe fn l_Std_TreeSet_filter___redArg(
    mut v_f_3003_: *mut crate::leanh::LeanObject,
    mut v_m_3004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3005_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3005_, 0, v_f_3003_);
    v___x_3006_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_3005_, v_m_3004_);
    return v___x_3006_;
}
pub unsafe fn l_Std_TreeSet_filter(
    mut v_00_u03b1_3007_: *mut crate::leanh::LeanObject,
    mut v_cmp_3008_: *mut crate::leanh::LeanObject,
    mut v_f_3009_: *mut crate::leanh::LeanObject,
    mut v_m_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3011_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3011_, 0, v_f_3009_);
    v___x_3012_ = l_Std_DTreeMap_Internal_Impl_filter___redArg(v___f_3011_, v_m_3010_);
    return v___x_3012_;
}
pub unsafe fn l_Std_TreeSet_filter___boxed(
    mut v_00_u03b1_3013_: *mut crate::leanh::LeanObject,
    mut v_cmp_3014_: *mut crate::leanh::LeanObject,
    mut v_f_3015_: *mut crate::leanh::LeanObject,
    mut v_m_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3017_ = l_Std_TreeSet_filter(v_00_u03b1_3013_, v_cmp_3014_, v_f_3015_, v_m_3016_);
    crate::leanh::lean_dec_ref(v_cmp_3014_);
    return v_res_3017_;
}
pub unsafe fn l_Std_TreeSet_foldlM___redArg___lam__0(
    mut v_f_3018_: *mut crate::leanh::LeanObject,
    mut v_c_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_x_3021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3022_ = crate::leanh::lean_apply_2(v_f_3018_, v_c_3019_, v_a_3020_);
    return v___x_3022_;
}
pub unsafe fn l_Std_TreeSet_foldlM___redArg(
    mut v_inst_3023_: *mut crate::leanh::LeanObject,
    mut v_f_3024_: *mut crate::leanh::LeanObject,
    mut v_init_3025_: *mut crate::leanh::LeanObject,
    mut v_t_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3027_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3027_, 0, v_f_3024_);
    v___x_3028_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3023_,
        v___f_3027_,
        v_init_3025_,
        v_t_3026_,
    );
    return v___x_3028_;
}
pub unsafe fn l_Std_TreeSet_foldlM(
    mut v_00_u03b1_3029_: *mut crate::leanh::LeanObject,
    mut v_cmp_3030_: *mut crate::leanh::LeanObject,
    mut v_m_3031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3032_: *mut crate::leanh::LeanObject,
    mut v_inst_3033_: *mut crate::leanh::LeanObject,
    mut v_f_3034_: *mut crate::leanh::LeanObject,
    mut v_init_3035_: *mut crate::leanh::LeanObject,
    mut v_t_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3037_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3037_, 0, v_f_3034_);
    v___x_3038_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3033_,
        v___f_3037_,
        v_init_3035_,
        v_t_3036_,
    );
    return v___x_3038_;
}
pub unsafe fn l_Std_TreeSet_foldlM___boxed(
    mut v_00_u03b1_3039_: *mut crate::leanh::LeanObject,
    mut v_cmp_3040_: *mut crate::leanh::LeanObject,
    mut v_m_3041_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3042_: *mut crate::leanh::LeanObject,
    mut v_inst_3043_: *mut crate::leanh::LeanObject,
    mut v_f_3044_: *mut crate::leanh::LeanObject,
    mut v_init_3045_: *mut crate::leanh::LeanObject,
    mut v_t_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_3040_);
    return v_res_3047_;
}
pub unsafe fn l_Std_TreeSet_foldl___redArg(
    mut v_f_3048_: *mut crate::leanh::LeanObject,
    mut v_init_3049_: *mut crate::leanh::LeanObject,
    mut v_t_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3051_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3051_, 0, v_f_3048_);
    v___x_3052_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3051_, v_init_3049_, v_t_3050_);
    return v___x_3052_;
}
pub unsafe fn l_Std_TreeSet_foldl(
    mut v_00_u03b1_3053_: *mut crate::leanh::LeanObject,
    mut v_cmp_3054_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3055_: *mut crate::leanh::LeanObject,
    mut v_f_3056_: *mut crate::leanh::LeanObject,
    mut v_init_3057_: *mut crate::leanh::LeanObject,
    mut v_t_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3059_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3059_, 0, v_f_3056_);
    v___x_3060_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3059_, v_init_3057_, v_t_3058_);
    return v___x_3060_;
}
pub unsafe fn l_Std_TreeSet_foldl___boxed(
    mut v_00_u03b1_3061_: *mut crate::leanh::LeanObject,
    mut v_cmp_3062_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3063_: *mut crate::leanh::LeanObject,
    mut v_f_3064_: *mut crate::leanh::LeanObject,
    mut v_init_3065_: *mut crate::leanh::LeanObject,
    mut v_t_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3067_ = l_Std_TreeSet_foldl(
        v_00_u03b1_3061_,
        v_cmp_3062_,
        v_00_u03b4_3063_,
        v_f_3064_,
        v_init_3065_,
        v_t_3066_,
    );
    crate::leanh::lean_dec_ref(v_cmp_3062_);
    return v_res_3067_;
}
pub unsafe fn l_Std_TreeSet_foldrM___redArg___lam__0(
    mut v_f_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
    mut v_x_3070_: *mut crate::leanh::LeanObject,
    mut v_acc_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = crate::leanh::lean_apply_2(v_f_3068_, v_a_3069_, v_acc_3071_);
    return v___x_3072_;
}
pub unsafe fn l_Std_TreeSet_foldrM___redArg(
    mut v_inst_3073_: *mut crate::leanh::LeanObject,
    mut v_f_3074_: *mut crate::leanh::LeanObject,
    mut v_init_3075_: *mut crate::leanh::LeanObject,
    mut v_t_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3077_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3077_, 0, v_f_3074_);
    v___x_3078_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_3073_,
        v___f_3077_,
        v_init_3075_,
        v_t_3076_,
    );
    return v___x_3078_;
}
pub unsafe fn l_Std_TreeSet_foldrM(
    mut v_00_u03b1_3079_: *mut crate::leanh::LeanObject,
    mut v_cmp_3080_: *mut crate::leanh::LeanObject,
    mut v_m_3081_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3082_: *mut crate::leanh::LeanObject,
    mut v_inst_3083_: *mut crate::leanh::LeanObject,
    mut v_f_3084_: *mut crate::leanh::LeanObject,
    mut v_init_3085_: *mut crate::leanh::LeanObject,
    mut v_t_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3087_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3087_, 0, v_f_3084_);
    v___x_3088_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_3083_,
        v___f_3087_,
        v_init_3085_,
        v_t_3086_,
    );
    return v___x_3088_;
}
pub unsafe fn l_Std_TreeSet_foldrM___boxed(
    mut v_00_u03b1_3089_: *mut crate::leanh::LeanObject,
    mut v_cmp_3090_: *mut crate::leanh::LeanObject,
    mut v_m_3091_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3092_: *mut crate::leanh::LeanObject,
    mut v_inst_3093_: *mut crate::leanh::LeanObject,
    mut v_f_3094_: *mut crate::leanh::LeanObject,
    mut v_init_3095_: *mut crate::leanh::LeanObject,
    mut v_t_3096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_3090_);
    return v_res_3097_;
}
pub unsafe fn l_Std_TreeSet_foldr___redArg___lam__0(
    mut v_f_3098_: *mut crate::leanh::LeanObject,
    mut v_x1_3099_: *mut crate::leanh::LeanObject,
    mut v_x2_3100_: *mut crate::leanh::LeanObject,
    mut v_x3_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = crate::leanh::lean_apply_2(v_f_3098_, v_x1_3099_, v_x3_3101_);
    return v___x_3102_;
}
pub unsafe fn l_Std_TreeSet_foldr___redArg(
    mut v_f_3122_: *mut crate::leanh::LeanObject,
    mut v_init_3123_: *mut crate::leanh::LeanObject,
    mut v_t_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3125_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3125_, 0, v_f_3122_);
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
    mut v_00_u03b1_3128_: *mut crate::leanh::LeanObject,
    mut v_cmp_3129_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3130_: *mut crate::leanh::LeanObject,
    mut v_f_3131_: *mut crate::leanh::LeanObject,
    mut v_init_3132_: *mut crate::leanh::LeanObject,
    mut v_t_3133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3134_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3134_, 0, v_f_3131_);
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
    mut v_00_u03b1_3137_: *mut crate::leanh::LeanObject,
    mut v_cmp_3138_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3139_: *mut crate::leanh::LeanObject,
    mut v_f_3140_: *mut crate::leanh::LeanObject,
    mut v_init_3141_: *mut crate::leanh::LeanObject,
    mut v_t_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Std_TreeSet_foldr(
        v_00_u03b1_3137_,
        v_cmp_3138_,
        v_00_u03b4_3139_,
        v_f_3140_,
        v_init_3141_,
        v_t_3142_,
    );
    crate::leanh::lean_dec_ref(v_cmp_3138_);
    return v_res_3143_;
}
pub unsafe fn l_Std_TreeSet_partition___redArg___lam__0(
    mut v_f_3144_: *mut crate::leanh::LeanObject,
    mut v_cmp_3145_: *mut crate::leanh::LeanObject,
    mut v_x_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
    mut v_b_3148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: u8 = 0;
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3149_ = crate::leanh::lean_ctor_get(v_x_3146_, 0);
                v_snd_3150_ = crate::leanh::lean_ctor_get(v_x_3146_, 1);
                v_isSharedCheck_3164_ = (!crate::leanh::lean_is_exclusive(v_x_3146_)) as u8;
                if v_isSharedCheck_3164_ == 0 {
                    v___x_3152_ = v_x_3146_;
                    v_isShared_3153_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3150_);
                    crate::leanh::lean_inc(v_fst_3149_);
                    crate::leanh::lean_dec(v_x_3146_);
                    v___x_3152_ = crate::leanh::lean_box(0);
                    v_isShared_3153_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_3147_);
                v___x_3154_ = crate::leanh::lean_apply_1(v_f_3144_, v_a_3147_);
                v___x_3155_ = (crate::leanh::lean_unbox(v___x_3154_) as u8);
                if v___x_3155_ == 0 {
                    v___x_3156_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_3145_,
                        v_a_3147_,
                        v_b_3148_,
                        v_snd_3150_,
                    );
                    if v_isShared_3153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3152_, 1, v___x_3156_);
                        v___x_3158_ = v___x_3152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_fst_3149_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3156_);
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
                        crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3160_);
                        v___x_3162_ = v___x_3152_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_snd_3150_);
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
    mut v_cmp_3167_: *mut crate::leanh::LeanObject,
    mut v_f_3168_: *mut crate::leanh::LeanObject,
    mut v_t_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3170_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3170_, 0, v_f_3168_);
                crate::leanh::lean_closure_set(v___f_3170_, 1, v_cmp_3167_);
                v___x_3171_ = l_Std_TreeSet_partition___redArg___closed__0;
                v_p_3172_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3170_,
                    v___x_3171_,
                    v_t_3169_,
                );
                v_fst_3173_ = crate::leanh::lean_ctor_get(v_p_3172_, 0);
                v_snd_3174_ = crate::leanh::lean_ctor_get(v_p_3172_, 1);
                v_isSharedCheck_3181_ = (!crate::leanh::lean_is_exclusive(v_p_3172_)) as u8;
                if v_isSharedCheck_3181_ == 0 {
                    v___x_3176_ = v_p_3172_;
                    v_isShared_3177_ = v_isSharedCheck_3181_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3174_);
                    crate::leanh::lean_inc(v_fst_3173_);
                    crate::leanh::lean_dec(v_p_3172_);
                    v___x_3176_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_fst_3173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_snd_3174_);
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
    mut v_00_u03b1_3182_: *mut crate::leanh::LeanObject,
    mut v_cmp_3183_: *mut crate::leanh::LeanObject,
    mut v_f_3184_: *mut crate::leanh::LeanObject,
    mut v_t_3185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3186_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3186_, 0, v_f_3184_);
                crate::leanh::lean_closure_set(v___f_3186_, 1, v_cmp_3183_);
                v___x_3187_ = l_Std_TreeSet_partition___redArg___closed__0;
                v_p_3188_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3186_,
                    v___x_3187_,
                    v_t_3185_,
                );
                v_fst_3189_ = crate::leanh::lean_ctor_get(v_p_3188_, 0);
                v_snd_3190_ = crate::leanh::lean_ctor_get(v_p_3188_, 1);
                v_isSharedCheck_3197_ = (!crate::leanh::lean_is_exclusive(v_p_3188_)) as u8;
                if v_isSharedCheck_3197_ == 0 {
                    v___x_3192_ = v_p_3188_;
                    v_isShared_3193_ = v_isSharedCheck_3197_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3190_);
                    crate::leanh::lean_inc(v_fst_3189_);
                    crate::leanh::lean_dec(v_p_3188_);
                    v___x_3192_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3196_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_fst_3189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_snd_3190_);
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
    mut v_f_3198_: *mut crate::leanh::LeanObject,
    mut v_x_3199_: *mut crate::leanh::LeanObject,
    mut v_k_3200_: *mut crate::leanh::LeanObject,
    mut v_v_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = crate::leanh::lean_apply_1(v_f_3198_, v_k_3200_);
    return v___x_3202_;
}
pub unsafe fn l_Std_TreeSet_forM___redArg(
    mut v_inst_3203_: *mut crate::leanh::LeanObject,
    mut v_f_3204_: *mut crate::leanh::LeanObject,
    mut v_t_3205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3206_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3206_, 0, v_f_3204_);
    v___x_3207_ = crate::leanh::lean_box(0);
    v___x_3208_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3203_,
        v___f_3206_,
        v___x_3207_,
        v_t_3205_,
    );
    return v___x_3208_;
}
pub unsafe fn l_Std_TreeSet_forM(
    mut v_00_u03b1_3209_: *mut crate::leanh::LeanObject,
    mut v_cmp_3210_: *mut crate::leanh::LeanObject,
    mut v_m_3211_: *mut crate::leanh::LeanObject,
    mut v_inst_3212_: *mut crate::leanh::LeanObject,
    mut v_f_3213_: *mut crate::leanh::LeanObject,
    mut v_t_3214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3215_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3215_, 0, v_f_3213_);
    v___x_3216_ = crate::leanh::lean_box(0);
    v___x_3217_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3212_,
        v___f_3215_,
        v___x_3216_,
        v_t_3214_,
    );
    return v___x_3217_;
}
pub unsafe fn l_Std_TreeSet_forM___boxed(
    mut v_00_u03b1_3218_: *mut crate::leanh::LeanObject,
    mut v_cmp_3219_: *mut crate::leanh::LeanObject,
    mut v_m_3220_: *mut crate::leanh::LeanObject,
    mut v_inst_3221_: *mut crate::leanh::LeanObject,
    mut v_f_3222_: *mut crate::leanh::LeanObject,
    mut v_t_3223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3224_ = l_Std_TreeSet_forM(
        v_00_u03b1_3218_,
        v_cmp_3219_,
        v_m_3220_,
        v_inst_3221_,
        v_f_3222_,
        v_t_3223_,
    );
    crate::leanh::lean_dec_ref(v_cmp_3219_);
    return v_res_3224_;
}
pub unsafe fn l_Std_TreeSet_forIn___redArg___lam__0(
    mut v_f_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_b_3227_: *mut crate::leanh::LeanObject,
    mut v_c_3228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3229_ = crate::leanh::lean_apply_2(v_f_3225_, v_a_3226_, v_c_3228_);
    return v___x_3229_;
}
pub unsafe fn l_Std_TreeSet_forIn___redArg___lam__1(
    mut v_toPure_3230_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_3232_ = crate::leanh::lean_ctor_get(v_____do__lift_3231_, 0);
    crate::leanh::lean_inc(v_a_3232_);
    crate::leanh::lean_dec_ref(v_____do__lift_3231_);
    v___x_3233_ = crate::leanh::lean_apply_2(v_toPure_3230_, crate::leanh::lean_box(0), v_a_3232_);
    return v___x_3233_;
}
pub unsafe fn l_Std_TreeSet_forIn___redArg(
    mut v_inst_3234_: *mut crate::leanh::LeanObject,
    mut v_f_3235_: *mut crate::leanh::LeanObject,
    mut v_init_3236_: *mut crate::leanh::LeanObject,
    mut v_t_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3238_ = crate::leanh::lean_ctor_get(v_inst_3234_, 0);
    v_toBind_3239_ = crate::leanh::lean_ctor_get(v_inst_3234_, 1);
    crate::leanh::lean_inc(v_toBind_3239_);
    v_toPure_3240_ = crate::leanh::lean_ctor_get(v_toApplicative_3238_, 1);
    crate::leanh::lean_inc(v_toPure_3240_);
    v___f_3241_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3241_, 0, v_f_3235_);
    v___x_3242_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3234_,
        v___f_3241_,
        v_init_3236_,
        v_t_3237_,
    );
    v___f_3243_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3243_, 0, v_toPure_3240_);
    v___x_3244_ = crate::leanh::lean_apply_4(
        v_toBind_3239_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3242_,
        v___f_3243_,
    );
    return v___x_3244_;
}
pub unsafe fn l_Std_TreeSet_forIn(
    mut v_00_u03b1_3245_: *mut crate::leanh::LeanObject,
    mut v_cmp_3246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3247_: *mut crate::leanh::LeanObject,
    mut v_m_3248_: *mut crate::leanh::LeanObject,
    mut v_inst_3249_: *mut crate::leanh::LeanObject,
    mut v_f_3250_: *mut crate::leanh::LeanObject,
    mut v_init_3251_: *mut crate::leanh::LeanObject,
    mut v_t_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3253_ = crate::leanh::lean_ctor_get(v_inst_3249_, 0);
    v_toBind_3254_ = crate::leanh::lean_ctor_get(v_inst_3249_, 1);
    crate::leanh::lean_inc(v_toBind_3254_);
    v_toPure_3255_ = crate::leanh::lean_ctor_get(v_toApplicative_3253_, 1);
    crate::leanh::lean_inc(v_toPure_3255_);
    v___f_3256_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3256_, 0, v_f_3250_);
    v___x_3257_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3249_,
        v___f_3256_,
        v_init_3251_,
        v_t_3252_,
    );
    v___f_3258_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3258_, 0, v_toPure_3255_);
    v___x_3259_ = crate::leanh::lean_apply_4(
        v_toBind_3254_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3257_,
        v___f_3258_,
    );
    return v___x_3259_;
}
pub unsafe fn l_Std_TreeSet_forIn___boxed(
    mut v_00_u03b1_3260_: *mut crate::leanh::LeanObject,
    mut v_cmp_3261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3262_: *mut crate::leanh::LeanObject,
    mut v_m_3263_: *mut crate::leanh::LeanObject,
    mut v_inst_3264_: *mut crate::leanh::LeanObject,
    mut v_f_3265_: *mut crate::leanh::LeanObject,
    mut v_init_3266_: *mut crate::leanh::LeanObject,
    mut v_t_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_cmp_3261_);
    return v_res_3268_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad___redArg___lam__1(
    mut v_inst_3269_: *mut crate::leanh::LeanObject,
    mut v_t_3270_: *mut crate::leanh::LeanObject,
    mut v_f_3271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3272_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3272_, 0, v_f_3271_);
    v___x_3273_ = crate::leanh::lean_box(0);
    v___x_3274_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_3269_,
        v___f_3272_,
        v___x_3273_,
        v_t_3270_,
    );
    return v___x_3274_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad___redArg(
    mut v_inst_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3276_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3276_, 0, v_inst_3275_);
    return v___f_3276_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad(
    mut v_00_u03b1_3277_: *mut crate::leanh::LeanObject,
    mut v_cmp_3278_: *mut crate::leanh::LeanObject,
    mut v_m_3279_: *mut crate::leanh::LeanObject,
    mut v_inst_3280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3281_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instForMOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3281_, 0, v_inst_3280_);
    return v___f_3281_;
}
pub unsafe fn l_Std_TreeSet_instForMOfMonad___boxed(
    mut v_00_u03b1_3282_: *mut crate::leanh::LeanObject,
    mut v_cmp_3283_: *mut crate::leanh::LeanObject,
    mut v_m_3284_: *mut crate::leanh::LeanObject,
    mut v_inst_3285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3286_ =
        l_Std_TreeSet_instForMOfMonad(v_00_u03b1_3282_, v_cmp_3283_, v_m_3284_, v_inst_3285_);
    crate::leanh::lean_dec_ref(v_cmp_3283_);
    return v_res_3286_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad___redArg___lam__2(
    mut v_inst_3287_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3288_: *mut crate::leanh::LeanObject,
    mut v_m_3289_: *mut crate::leanh::LeanObject,
    mut v_init_3290_: *mut crate::leanh::LeanObject,
    mut v_f_3291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3292_ = crate::leanh::lean_ctor_get(v_inst_3287_, 0);
    v_toBind_3293_ = crate::leanh::lean_ctor_get(v_inst_3287_, 1);
    crate::leanh::lean_inc(v_toBind_3293_);
    v_toPure_3294_ = crate::leanh::lean_ctor_get(v_toApplicative_3292_, 1);
    crate::leanh::lean_inc(v_toPure_3294_);
    v___f_3295_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3295_, 0, v_f_3291_);
    v___x_3296_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_3287_,
        v___f_3295_,
        v_init_3290_,
        v_m_3289_,
    );
    v___f_3297_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3297_, 0, v_toPure_3294_);
    v___x_3298_ = crate::leanh::lean_apply_4(
        v_toBind_3293_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3296_,
        v___f_3297_,
    );
    return v___x_3298_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad___redArg(
    mut v_inst_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3300_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3300_, 0, v_inst_3299_);
    return v___f_3300_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad(
    mut v_00_u03b1_3301_: *mut crate::leanh::LeanObject,
    mut v_cmp_3302_: *mut crate::leanh::LeanObject,
    mut v_m_3303_: *mut crate::leanh::LeanObject,
    mut v_inst_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3305_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3305_, 0, v_inst_3304_);
    return v___f_3305_;
}
pub unsafe fn l_Std_TreeSet_instForInOfMonad___boxed(
    mut v_00_u03b1_3306_: *mut crate::leanh::LeanObject,
    mut v_cmp_3307_: *mut crate::leanh::LeanObject,
    mut v_m_3308_: *mut crate::leanh::LeanObject,
    mut v_inst_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3310_ =
        l_Std_TreeSet_instForInOfMonad(v_00_u03b1_3306_, v_cmp_3307_, v_m_3308_, v_inst_3309_);
    crate::leanh::lean_dec_ref(v_cmp_3307_);
    return v_res_3310_;
}
pub unsafe fn l_Std_TreeSet_any___redArg___lam__0(
    mut v_p_3311_: *mut crate::leanh::LeanObject,
    mut v___x_3312_: *mut crate::leanh::LeanObject,
    mut v___x_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_b_3315_: *mut crate::leanh::LeanObject,
    mut v_acc_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    v___x_3317_ = crate::leanh::lean_apply_1(v_p_3311_, v_a_3314_);
    v___x_3318_ = (crate::leanh::lean_unbox(v___x_3317_) as u8);
    if v___x_3318_ == 0 {
        let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3319_, 0, v___x_3312_);
        return v___x_3319_;
    } else {
        let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3312_);
        v___x_3320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3317_);
        v___x_3321_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3321_, 0, v___x_3320_);
        crate::leanh::lean_ctor_set(v___x_3321_, 1, v___x_3313_);
        v___x_3322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3322_, 0, v___x_3321_);
        return v___x_3322_;
    }
}
pub unsafe fn l_Std_TreeSet_any___redArg___lam__0___boxed(
    mut v_p_3323_: *mut crate::leanh::LeanObject,
    mut v___x_3324_: *mut crate::leanh::LeanObject,
    mut v___x_3325_: *mut crate::leanh::LeanObject,
    mut v_a_3326_: *mut crate::leanh::LeanObject,
    mut v_b_3327_: *mut crate::leanh::LeanObject,
    mut v_acc_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_Std_TreeSet_any___redArg___lam__0(
        v_p_3323_,
        v___x_3324_,
        v___x_3325_,
        v_a_3326_,
        v_b_3327_,
        v_acc_3328_,
    );
    crate::leanh::lean_dec_ref(v_acc_3328_);
    return v_res_3329_;
}
pub unsafe fn l_Std_TreeSet_any___redArg(
    mut v_t_3333_: *mut crate::leanh::LeanObject,
    mut v_p_3334_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    let mut v_val_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3341_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3342_ = crate::leanh::lean_box(0);
                v___x_3343_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3344_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3344_, 0, v_p_3334_);
                crate::leanh::lean_closure_set(v___f_3344_, 1, v___x_3343_);
                crate::leanh::lean_closure_set(v___f_3344_, 2, v___x_3342_);
                v___x_3345_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3341_,
                    v___f_3344_,
                    v___x_3343_,
                    v_t_3333_,
                );
                v_a_3346_ = crate::leanh::lean_ctor_get(v___x_3345_, 0);
                crate::leanh::lean_inc(v_a_3346_);
                crate::leanh::lean_dec(v___x_3345_);
                v___y_3336_ = v_a_3346_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3337_ = crate::leanh::lean_ctor_get(v___y_3336_, 0);
                crate::leanh::lean_inc(v_fst_3337_);
                crate::leanh::lean_dec_ref(v___y_3336_);
                if crate::leanh::lean_obj_tag(v_fst_3337_) == 0 {
                    v___x_3338_ = 0;
                    return v___x_3338_;
                } else {
                    v_val_3339_ = crate::leanh::lean_ctor_get(v_fst_3337_, 0);
                    crate::leanh::lean_inc(v_val_3339_);
                    crate::leanh::lean_dec_ref_known(v_fst_3337_, 1);
                    v___x_3340_ = (crate::leanh::lean_unbox(v_val_3339_) as u8);
                    crate::leanh::lean_dec(v_val_3339_);
                    return v___x_3340_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_any___redArg___boxed(
    mut v_t_3347_: *mut crate::leanh::LeanObject,
    mut v_p_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3349_: u8 = 0;
    let mut v_r_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Std_TreeSet_any___redArg(v_t_3347_, v_p_3348_);
    v_r_3350_ = crate::leanh::lean_box((v_res_3349_) as usize);
    return v_r_3350_;
}
pub unsafe fn l_Std_TreeSet_any(
    mut v_00_u03b1_3351_: *mut crate::leanh::LeanObject,
    mut v_cmp_3352_: *mut crate::leanh::LeanObject,
    mut v_t_3353_: *mut crate::leanh::LeanObject,
    mut v_p_3354_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v_val_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3361_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3362_ = crate::leanh::lean_box(0);
                v___x_3363_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3364_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3364_, 0, v_p_3354_);
                crate::leanh::lean_closure_set(v___f_3364_, 1, v___x_3363_);
                crate::leanh::lean_closure_set(v___f_3364_, 2, v___x_3362_);
                v___x_3365_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3361_,
                    v___f_3364_,
                    v___x_3363_,
                    v_t_3353_,
                );
                v_a_3366_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                crate::leanh::lean_inc(v_a_3366_);
                crate::leanh::lean_dec(v___x_3365_);
                v___y_3356_ = v_a_3366_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3357_ = crate::leanh::lean_ctor_get(v___y_3356_, 0);
                crate::leanh::lean_inc(v_fst_3357_);
                crate::leanh::lean_dec_ref(v___y_3356_);
                if crate::leanh::lean_obj_tag(v_fst_3357_) == 0 {
                    v___x_3358_ = 0;
                    return v___x_3358_;
                } else {
                    v_val_3359_ = crate::leanh::lean_ctor_get(v_fst_3357_, 0);
                    crate::leanh::lean_inc(v_val_3359_);
                    crate::leanh::lean_dec_ref_known(v_fst_3357_, 1);
                    v___x_3360_ = (crate::leanh::lean_unbox(v_val_3359_) as u8);
                    crate::leanh::lean_dec(v_val_3359_);
                    return v___x_3360_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_any___boxed(
    mut v_00_u03b1_3367_: *mut crate::leanh::LeanObject,
    mut v_cmp_3368_: *mut crate::leanh::LeanObject,
    mut v_t_3369_: *mut crate::leanh::LeanObject,
    mut v_p_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3371_: u8 = 0;
    let mut v_r_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3371_ = l_Std_TreeSet_any(v_00_u03b1_3367_, v_cmp_3368_, v_t_3369_, v_p_3370_);
    crate::leanh::lean_dec_ref(v_cmp_3368_);
    v_r_3372_ = crate::leanh::lean_box((v_res_3371_) as usize);
    return v_r_3372_;
}
pub unsafe fn l_Std_TreeSet_all___redArg___lam__0(
    mut v_p_3373_: *mut crate::leanh::LeanObject,
    mut v___x_3374_: *mut crate::leanh::LeanObject,
    mut v___x_3375_: *mut crate::leanh::LeanObject,
    mut v_a_3376_: *mut crate::leanh::LeanObject,
    mut v_b_3377_: *mut crate::leanh::LeanObject,
    mut v_acc_3378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: u8 = 0;
    v___x_3379_ = crate::leanh::lean_apply_1(v_p_3373_, v_a_3376_);
    v___x_3380_ = (crate::leanh::lean_unbox(v___x_3379_) as u8);
    if v___x_3380_ == 0 {
        let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3375_);
        v___x_3381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3381_, 0, v___x_3379_);
        v___x_3382_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3382_, 0, v___x_3381_);
        crate::leanh::lean_ctor_set(v___x_3382_, 1, v___x_3374_);
        v___x_3383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3383_, 0, v___x_3382_);
        return v___x_3383_;
    } else {
        let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3384_, 0, v___x_3375_);
        return v___x_3384_;
    }
}
pub unsafe fn l_Std_TreeSet_all___redArg___lam__0___boxed(
    mut v_p_3385_: *mut crate::leanh::LeanObject,
    mut v___x_3386_: *mut crate::leanh::LeanObject,
    mut v___x_3387_: *mut crate::leanh::LeanObject,
    mut v_a_3388_: *mut crate::leanh::LeanObject,
    mut v_b_3389_: *mut crate::leanh::LeanObject,
    mut v_acc_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Std_TreeSet_all___redArg___lam__0(
        v_p_3385_,
        v___x_3386_,
        v___x_3387_,
        v_a_3388_,
        v_b_3389_,
        v_acc_3390_,
    );
    crate::leanh::lean_dec_ref(v_acc_3390_);
    return v_res_3391_;
}
pub unsafe fn l_Std_TreeSet_all___redArg(
    mut v_t_3392_: *mut crate::leanh::LeanObject,
    mut v_p_3393_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v_val_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3400_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3401_ = crate::leanh::lean_box(0);
                v___x_3402_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3403_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3403_, 0, v_p_3393_);
                crate::leanh::lean_closure_set(v___f_3403_, 1, v___x_3401_);
                crate::leanh::lean_closure_set(v___f_3403_, 2, v___x_3402_);
                v___x_3404_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3400_,
                    v___f_3403_,
                    v___x_3402_,
                    v_t_3392_,
                );
                v_a_3405_ = crate::leanh::lean_ctor_get(v___x_3404_, 0);
                crate::leanh::lean_inc(v_a_3405_);
                crate::leanh::lean_dec(v___x_3404_);
                v___y_3395_ = v_a_3405_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3396_ = crate::leanh::lean_ctor_get(v___y_3395_, 0);
                crate::leanh::lean_inc(v_fst_3396_);
                crate::leanh::lean_dec_ref(v___y_3395_);
                if crate::leanh::lean_obj_tag(v_fst_3396_) == 0 {
                    v___x_3397_ = 1;
                    return v___x_3397_;
                } else {
                    v_val_3398_ = crate::leanh::lean_ctor_get(v_fst_3396_, 0);
                    crate::leanh::lean_inc(v_val_3398_);
                    crate::leanh::lean_dec_ref_known(v_fst_3396_, 1);
                    v___x_3399_ = (crate::leanh::lean_unbox(v_val_3398_) as u8);
                    crate::leanh::lean_dec(v_val_3398_);
                    return v___x_3399_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_all___redArg___boxed(
    mut v_t_3406_: *mut crate::leanh::LeanObject,
    mut v_p_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3408_: u8 = 0;
    let mut v_r_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Std_TreeSet_all___redArg(v_t_3406_, v_p_3407_);
    v_r_3409_ = crate::leanh::lean_box((v_res_3408_) as usize);
    return v_r_3409_;
}
pub unsafe fn l_Std_TreeSet_all(
    mut v_00_u03b1_3410_: *mut crate::leanh::LeanObject,
    mut v_cmp_3411_: *mut crate::leanh::LeanObject,
    mut v_t_3412_: *mut crate::leanh::LeanObject,
    mut v_p_3413_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v_val_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: u8 = 0;
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3420_ = l_Std_TreeSet_foldr___redArg___closed__9;
                v___x_3421_ = crate::leanh::lean_box(0);
                v___x_3422_ = l_Std_TreeSet_any___redArg___closed__0;
                v___f_3423_ = crate::leanh::lean_alloc_closure(
                    l_Std_TreeSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3423_, 0, v_p_3413_);
                crate::leanh::lean_closure_set(v___f_3423_, 1, v___x_3421_);
                crate::leanh::lean_closure_set(v___f_3423_, 2, v___x_3422_);
                v___x_3424_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_3420_,
                    v___f_3423_,
                    v___x_3422_,
                    v_t_3412_,
                );
                v_a_3425_ = crate::leanh::lean_ctor_get(v___x_3424_, 0);
                crate::leanh::lean_inc(v_a_3425_);
                crate::leanh::lean_dec(v___x_3424_);
                v___y_3415_ = v_a_3425_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_3416_ = crate::leanh::lean_ctor_get(v___y_3415_, 0);
                crate::leanh::lean_inc(v_fst_3416_);
                crate::leanh::lean_dec_ref(v___y_3415_);
                if crate::leanh::lean_obj_tag(v_fst_3416_) == 0 {
                    v___x_3417_ = 1;
                    return v___x_3417_;
                } else {
                    v_val_3418_ = crate::leanh::lean_ctor_get(v_fst_3416_, 0);
                    crate::leanh::lean_inc(v_val_3418_);
                    crate::leanh::lean_dec_ref_known(v_fst_3416_, 1);
                    v___x_3419_ = (crate::leanh::lean_unbox(v_val_3418_) as u8);
                    crate::leanh::lean_dec(v_val_3418_);
                    return v___x_3419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_TreeSet_all___boxed(
    mut v_00_u03b1_3426_: *mut crate::leanh::LeanObject,
    mut v_cmp_3427_: *mut crate::leanh::LeanObject,
    mut v_t_3428_: *mut crate::leanh::LeanObject,
    mut v_p_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3430_: u8 = 0;
    let mut v_r_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3430_ = l_Std_TreeSet_all(v_00_u03b1_3426_, v_cmp_3427_, v_t_3428_, v_p_3429_);
    crate::leanh::lean_dec_ref(v_cmp_3427_);
    v_r_3431_ = crate::leanh::lean_box((v_res_3430_) as usize);
    return v_r_3431_;
}
pub unsafe fn l_Std_TreeSet_toList___redArg___lam__0(
    mut v_x1_3432_: *mut crate::leanh::LeanObject,
    mut v_x2_3433_: *mut crate::leanh::LeanObject,
    mut v_x3_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3435_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3435_, 0, v_x1_3432_);
    crate::leanh::lean_ctor_set(v___x_3435_, 1, v_x3_3434_);
    return v___x_3435_;
}
pub unsafe fn l_Std_TreeSet_toList___redArg(
    mut v_t_3437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3438_ = l_Std_TreeSet_toList___redArg___closed__0;
    v___x_3439_ = crate::leanh::lean_box(0);
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
    mut v_00_u03b1_3442_: *mut crate::leanh::LeanObject,
    mut v_cmp_3443_: *mut crate::leanh::LeanObject,
    mut v_t_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3445_ = l_Std_TreeSet_toList___redArg___closed__0;
    v___x_3446_ = crate::leanh::lean_box(0);
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
    mut v_00_u03b1_3449_: *mut crate::leanh::LeanObject,
    mut v_cmp_3450_: *mut crate::leanh::LeanObject,
    mut v_t_3451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3452_ = l_Std_TreeSet_toList(v_00_u03b1_3449_, v_cmp_3450_, v_t_3451_);
    crate::leanh::lean_dec_ref(v_cmp_3450_);
    return v_res_3452_;
}
pub unsafe fn _init_l_Std_TreeSet_ofList___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26_once),
        _init_l_Std_TreeSet___auto__1___closed__26,
    );
    return v___x_3453_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(
    mut v_cmp_3454_: *mut crate::leanh::LeanObject,
    mut v_k_3455_: *mut crate::leanh::LeanObject,
    mut v_v_3456_: *mut crate::leanh::LeanObject,
    mut v_t_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v_impl_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v_size_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_unused_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_unused_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3561_: u8 = 0;
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3569_: u8 = 0;
    let mut v_unused_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v_k_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3593_: u8 = 0;
    let mut v_unused_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3597_: u8 = 0;
    let mut v_unused_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v_size_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: u8 = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3680_: u8 = 0;
    let mut v_unused_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v_unused_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3699_: u8 = 0;
    let mut v_k_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut v_unused_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_unused_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_unused_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3457_) == 0 {
                    v_size_3458_ = crate::leanh::lean_ctor_get(v_t_3457_, 0);
                    v_k_3459_ = crate::leanh::lean_ctor_get(v_t_3457_, 1);
                    v_v_3460_ = crate::leanh::lean_ctor_get(v_t_3457_, 2);
                    v_l_3461_ = crate::leanh::lean_ctor_get(v_t_3457_, 3);
                    v_r_3462_ = crate::leanh::lean_ctor_get(v_t_3457_, 4);
                    v_isSharedCheck_3743_ = (!crate::leanh::lean_is_exclusive(v_t_3457_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3464_ = v_t_3457_;
                        v_isShared_3465_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3462_);
                        crate::leanh::lean_inc(v_l_3461_);
                        crate::leanh::lean_inc(v_v_3460_);
                        crate::leanh::lean_inc(v_k_3459_);
                        crate::leanh::lean_inc(v_size_3458_);
                        crate::leanh::lean_dec(v_t_3457_);
                        v___x_3464_ = crate::leanh::lean_box(0);
                        v_isShared_3465_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_3454_);
                    v___x_3744_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3745_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3745_, 0, v___x_3744_);
                    crate::leanh::lean_ctor_set(v___x_3745_, 1, v_k_3455_);
                    crate::leanh::lean_ctor_set(v___x_3745_, 2, v_v_3456_);
                    crate::leanh::lean_ctor_set(v___x_3745_, 3, v_t_3457_);
                    crate::leanh::lean_ctor_set(v___x_3745_, 4, v_t_3457_);
                    return v___x_3745_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_cmp_3454_);
                crate::leanh::lean_inc(v_k_3459_);
                crate::leanh::lean_inc(v_k_3455_);
                v___x_3466_ = crate::leanh::lean_apply_2(v_cmp_3454_, v_k_3455_, v_k_3459_);
                v___x_3467_ = (crate::leanh::lean_unbox(v___x_3466_) as u8);
                match v___x_3467_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_3458_);
                        v_impl_3468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_3454_, v_k_3455_, v_v_3456_, v_l_3461_);
                        v___x_3469_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_3462_) == 0 {
                            v_size_3470_ = crate::leanh::lean_ctor_get(v_r_3462_, 0);
                            v_size_3471_ = crate::leanh::lean_ctor_get(v_impl_3468_, 0);
                            crate::leanh::lean_inc(v_size_3471_);
                            v_k_3472_ = crate::leanh::lean_ctor_get(v_impl_3468_, 1);
                            crate::leanh::lean_inc(v_k_3472_);
                            v_v_3473_ = crate::leanh::lean_ctor_get(v_impl_3468_, 2);
                            crate::leanh::lean_inc(v_v_3473_);
                            v_l_3474_ = crate::leanh::lean_ctor_get(v_impl_3468_, 3);
                            crate::leanh::lean_inc(v_l_3474_);
                            v_r_3475_ = crate::leanh::lean_ctor_get(v_impl_3468_, 4);
                            crate::leanh::lean_inc(v_r_3475_);
                            v___x_3476_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_3477_ = lean_nat_mul(v___x_3476_, v_size_3470_);
                            v___x_3478_ = lean_nat_dec_lt(v___x_3477_, v_size_3471_);
                            crate::leanh::lean_dec(v___x_3477_);
                            if v___x_3478_ == 0 {
                                crate::leanh::lean_dec(v_r_3475_);
                                crate::leanh::lean_dec(v_l_3474_);
                                crate::leanh::lean_dec(v_v_3473_);
                                crate::leanh::lean_dec(v_k_3472_);
                                v___x_3479_ = lean_nat_add(v___x_3469_, v_size_3471_);
                                crate::leanh::lean_dec(v_size_3471_);
                                v___x_3480_ = lean_nat_add(v___x_3479_, v_size_3470_);
                                crate::leanh::lean_dec(v___x_3479_);
                                if v_isShared_3465_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3464_, 3, v_impl_3468_);
                                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3480_);
                                    v___x_3482_ = v___x_3464_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3483_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3483_,
                                        0,
                                        v___x_3480_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3483_,
                                        1,
                                        v_k_3459_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3483_,
                                        2,
                                        v_v_3460_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3483_,
                                        3,
                                        v_impl_3468_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3483_,
                                        4,
                                        v_r_3462_,
                                    );
                                    v___x_3482_ = v_reuseFailAlloc_3483_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3549_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3468_)) as u8;
                                if v_isSharedCheck_3549_ == 0 {
                                    v_unused_3550_ = crate::leanh::lean_ctor_get(v_impl_3468_, 4);
                                    crate::leanh::lean_dec(v_unused_3550_);
                                    v_unused_3551_ = crate::leanh::lean_ctor_get(v_impl_3468_, 3);
                                    crate::leanh::lean_dec(v_unused_3551_);
                                    v_unused_3552_ = crate::leanh::lean_ctor_get(v_impl_3468_, 2);
                                    crate::leanh::lean_dec(v_unused_3552_);
                                    v_unused_3553_ = crate::leanh::lean_ctor_get(v_impl_3468_, 1);
                                    crate::leanh::lean_dec(v_unused_3553_);
                                    v_unused_3554_ = crate::leanh::lean_ctor_get(v_impl_3468_, 0);
                                    crate::leanh::lean_dec(v_unused_3554_);
                                    v___x_3485_ = v_impl_3468_;
                                    v_isShared_3486_ = v_isSharedCheck_3549_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_3468_);
                                    v___x_3485_ = crate::leanh::lean_box(0);
                                    v_isShared_3486_ = v_isSharedCheck_3549_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3555_ = crate::leanh::lean_ctor_get(v_impl_3468_, 3);
                            crate::leanh::lean_inc(v_l_3555_);
                            if crate::leanh::lean_obj_tag(v_l_3555_) == 0 {
                                v_r_3556_ = crate::leanh::lean_ctor_get(v_impl_3468_, 4);
                                v_k_3557_ = crate::leanh::lean_ctor_get(v_impl_3468_, 1);
                                v_v_3558_ = crate::leanh::lean_ctor_get(v_impl_3468_, 2);
                                v_isSharedCheck_3569_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3468_)) as u8;
                                if v_isSharedCheck_3569_ == 0 {
                                    v_unused_3570_ = crate::leanh::lean_ctor_get(v_impl_3468_, 3);
                                    crate::leanh::lean_dec(v_unused_3570_);
                                    v_unused_3571_ = crate::leanh::lean_ctor_get(v_impl_3468_, 0);
                                    crate::leanh::lean_dec(v_unused_3571_);
                                    v___x_3560_ = v_impl_3468_;
                                    v_isShared_3561_ = v_isSharedCheck_3569_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_3556_);
                                    crate::leanh::lean_inc(v_v_3558_);
                                    crate::leanh::lean_inc(v_k_3557_);
                                    crate::leanh::lean_dec(v_impl_3468_);
                                    v___x_3560_ = crate::leanh::lean_box(0);
                                    v_isShared_3561_ = v_isSharedCheck_3569_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3572_ = crate::leanh::lean_ctor_get(v_impl_3468_, 4);
                                crate::leanh::lean_inc(v_r_3572_);
                                if crate::leanh::lean_obj_tag(v_r_3572_) == 0 {
                                    v_k_3573_ = crate::leanh::lean_ctor_get(v_impl_3468_, 1);
                                    v_v_3574_ = crate::leanh::lean_ctor_get(v_impl_3468_, 2);
                                    v_isSharedCheck_3597_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_3468_)) as u8;
                                    if v_isSharedCheck_3597_ == 0 {
                                        v_unused_3598_ =
                                            crate::leanh::lean_ctor_get(v_impl_3468_, 4);
                                        crate::leanh::lean_dec(v_unused_3598_);
                                        v_unused_3599_ =
                                            crate::leanh::lean_ctor_get(v_impl_3468_, 3);
                                        crate::leanh::lean_dec(v_unused_3599_);
                                        v_unused_3600_ =
                                            crate::leanh::lean_ctor_get(v_impl_3468_, 0);
                                        crate::leanh::lean_dec(v_unused_3600_);
                                        v___x_3576_ = v_impl_3468_;
                                        v_isShared_3577_ = v_isSharedCheck_3597_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3574_);
                                        crate::leanh::lean_inc(v_k_3573_);
                                        crate::leanh::lean_dec(v_impl_3468_);
                                        v___x_3576_ = crate::leanh::lean_box(0);
                                        v_isShared_3577_ = v_isSharedCheck_3597_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_3601_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_3465_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3464_, 4, v_r_3572_);
                                        crate::leanh::lean_ctor_set(v___x_3464_, 3, v_impl_3468_);
                                        crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3601_);
                                        v___x_3603_ = v___x_3464_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3604_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3604_,
                                            0,
                                            v___x_3601_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3604_,
                                            1,
                                            v_k_3459_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3604_,
                                            2,
                                            v_v_3460_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3604_,
                                            3,
                                            v_impl_3468_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3604_,
                                            4,
                                            v_r_3572_,
                                        );
                                        v___x_3603_ = v_reuseFailAlloc_3604_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_3460_);
                        crate::leanh::lean_dec(v_k_3459_);
                        crate::leanh::lean_dec_ref(v_cmp_3454_);
                        if v_isShared_3465_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3464_, 2, v_v_3456_);
                            crate::leanh::lean_ctor_set(v___x_3464_, 1, v_k_3455_);
                            v___x_3606_ = v___x_3464_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3607_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_size_3458_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_k_3455_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_v_3456_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_l_3461_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_r_3462_);
                            v___x_3606_ = v_reuseFailAlloc_3607_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_3458_);
                        v_impl_3608_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(v_cmp_3454_, v_k_3455_, v_v_3456_, v_r_3462_);
                        v___x_3609_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_3461_) == 0 {
                            v_size_3610_ = crate::leanh::lean_ctor_get(v_l_3461_, 0);
                            v_size_3611_ = crate::leanh::lean_ctor_get(v_impl_3608_, 0);
                            crate::leanh::lean_inc(v_size_3611_);
                            v_k_3612_ = crate::leanh::lean_ctor_get(v_impl_3608_, 1);
                            crate::leanh::lean_inc(v_k_3612_);
                            v_v_3613_ = crate::leanh::lean_ctor_get(v_impl_3608_, 2);
                            crate::leanh::lean_inc(v_v_3613_);
                            v_l_3614_ = crate::leanh::lean_ctor_get(v_impl_3608_, 3);
                            crate::leanh::lean_inc(v_l_3614_);
                            v_r_3615_ = crate::leanh::lean_ctor_get(v_impl_3608_, 4);
                            crate::leanh::lean_inc(v_r_3615_);
                            v___x_3616_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_3617_ = lean_nat_mul(v___x_3616_, v_size_3610_);
                            v___x_3618_ = lean_nat_dec_lt(v___x_3617_, v_size_3611_);
                            crate::leanh::lean_dec(v___x_3617_);
                            if v___x_3618_ == 0 {
                                crate::leanh::lean_dec(v_r_3615_);
                                crate::leanh::lean_dec(v_l_3614_);
                                crate::leanh::lean_dec(v_v_3613_);
                                crate::leanh::lean_dec(v_k_3612_);
                                v___x_3619_ = lean_nat_add(v___x_3609_, v_size_3610_);
                                v___x_3620_ = lean_nat_add(v___x_3619_, v_size_3611_);
                                crate::leanh::lean_dec(v_size_3611_);
                                crate::leanh::lean_dec(v___x_3619_);
                                if v_isShared_3465_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3464_, 4, v_impl_3608_);
                                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3620_);
                                    v___x_3622_ = v___x_3464_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3623_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3623_,
                                        0,
                                        v___x_3620_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3623_,
                                        1,
                                        v_k_3459_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3623_,
                                        2,
                                        v_v_3460_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3623_,
                                        3,
                                        v_l_3461_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3623_,
                                        4,
                                        v_impl_3608_,
                                    );
                                    v___x_3622_ = v_reuseFailAlloc_3623_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3687_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3608_)) as u8;
                                if v_isSharedCheck_3687_ == 0 {
                                    v_unused_3688_ = crate::leanh::lean_ctor_get(v_impl_3608_, 4);
                                    crate::leanh::lean_dec(v_unused_3688_);
                                    v_unused_3689_ = crate::leanh::lean_ctor_get(v_impl_3608_, 3);
                                    crate::leanh::lean_dec(v_unused_3689_);
                                    v_unused_3690_ = crate::leanh::lean_ctor_get(v_impl_3608_, 2);
                                    crate::leanh::lean_dec(v_unused_3690_);
                                    v_unused_3691_ = crate::leanh::lean_ctor_get(v_impl_3608_, 1);
                                    crate::leanh::lean_dec(v_unused_3691_);
                                    v_unused_3692_ = crate::leanh::lean_ctor_get(v_impl_3608_, 0);
                                    crate::leanh::lean_dec(v_unused_3692_);
                                    v___x_3625_ = v_impl_3608_;
                                    v_isShared_3626_ = v_isSharedCheck_3687_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_3608_);
                                    v___x_3625_ = crate::leanh::lean_box(0);
                                    v_isShared_3626_ = v_isSharedCheck_3687_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3693_ = crate::leanh::lean_ctor_get(v_impl_3608_, 3);
                            crate::leanh::lean_inc(v_l_3693_);
                            if crate::leanh::lean_obj_tag(v_l_3693_) == 0 {
                                v_r_3694_ = crate::leanh::lean_ctor_get(v_impl_3608_, 4);
                                v_k_3695_ = crate::leanh::lean_ctor_get(v_impl_3608_, 1);
                                v_v_3696_ = crate::leanh::lean_ctor_get(v_impl_3608_, 2);
                                v_isSharedCheck_3719_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3608_)) as u8;
                                if v_isSharedCheck_3719_ == 0 {
                                    v_unused_3720_ = crate::leanh::lean_ctor_get(v_impl_3608_, 3);
                                    crate::leanh::lean_dec(v_unused_3720_);
                                    v_unused_3721_ = crate::leanh::lean_ctor_get(v_impl_3608_, 0);
                                    crate::leanh::lean_dec(v_unused_3721_);
                                    v___x_3698_ = v_impl_3608_;
                                    v_isShared_3699_ = v_isSharedCheck_3719_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_3694_);
                                    crate::leanh::lean_inc(v_v_3696_);
                                    crate::leanh::lean_inc(v_k_3695_);
                                    crate::leanh::lean_dec(v_impl_3608_);
                                    v___x_3698_ = crate::leanh::lean_box(0);
                                    v_isShared_3699_ = v_isSharedCheck_3719_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3722_ = crate::leanh::lean_ctor_get(v_impl_3608_, 4);
                                crate::leanh::lean_inc(v_r_3722_);
                                if crate::leanh::lean_obj_tag(v_r_3722_) == 0 {
                                    v_k_3723_ = crate::leanh::lean_ctor_get(v_impl_3608_, 1);
                                    v_v_3724_ = crate::leanh::lean_ctor_get(v_impl_3608_, 2);
                                    v_isSharedCheck_3735_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_3608_)) as u8;
                                    if v_isSharedCheck_3735_ == 0 {
                                        v_unused_3736_ =
                                            crate::leanh::lean_ctor_get(v_impl_3608_, 4);
                                        crate::leanh::lean_dec(v_unused_3736_);
                                        v_unused_3737_ =
                                            crate::leanh::lean_ctor_get(v_impl_3608_, 3);
                                        crate::leanh::lean_dec(v_unused_3737_);
                                        v_unused_3738_ =
                                            crate::leanh::lean_ctor_get(v_impl_3608_, 0);
                                        crate::leanh::lean_dec(v_unused_3738_);
                                        v___x_3726_ = v_impl_3608_;
                                        v_isShared_3727_ = v_isSharedCheck_3735_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3724_);
                                        crate::leanh::lean_inc(v_k_3723_);
                                        crate::leanh::lean_dec(v_impl_3608_);
                                        v___x_3726_ = crate::leanh::lean_box(0);
                                        v_isShared_3727_ = v_isSharedCheck_3735_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3739_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_3465_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3464_, 4, v_impl_3608_);
                                        crate::leanh::lean_ctor_set(v___x_3464_, 3, v_r_3722_);
                                        crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3739_);
                                        v___x_3741_ = v___x_3464_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3742_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3742_,
                                            0,
                                            v___x_3739_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3742_,
                                            1,
                                            v_k_3459_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3742_,
                                            2,
                                            v_v_3460_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3742_,
                                            3,
                                            v_r_3722_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3742_,
                                            4,
                                            v_impl_3608_,
                                        );
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
                v_size_3487_ = crate::leanh::lean_ctor_get(v_l_3474_, 0);
                v_size_3488_ = crate::leanh::lean_ctor_get(v_r_3475_, 0);
                v_k_3489_ = crate::leanh::lean_ctor_get(v_r_3475_, 1);
                v_v_3490_ = crate::leanh::lean_ctor_get(v_r_3475_, 2);
                v_l_3491_ = crate::leanh::lean_ctor_get(v_r_3475_, 3);
                v_r_3492_ = crate::leanh::lean_ctor_get(v_r_3475_, 4);
                v___x_3493_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3494_ = lean_nat_mul(v___x_3493_, v_size_3487_);
                v___x_3495_ = lean_nat_dec_lt(v_size_3488_, v___x_3494_);
                crate::leanh::lean_dec(v___x_3494_);
                if v___x_3495_ == 0 {
                    crate::leanh::lean_inc(v_r_3492_);
                    crate::leanh::lean_inc(v_l_3491_);
                    crate::leanh::lean_inc(v_v_3490_);
                    crate::leanh::lean_inc(v_k_3489_);
                    v_isSharedCheck_3524_ = (!crate::leanh::lean_is_exclusive(v_r_3475_)) as u8;
                    if v_isSharedCheck_3524_ == 0 {
                        v_unused_3525_ = crate::leanh::lean_ctor_get(v_r_3475_, 4);
                        crate::leanh::lean_dec(v_unused_3525_);
                        v_unused_3526_ = crate::leanh::lean_ctor_get(v_r_3475_, 3);
                        crate::leanh::lean_dec(v_unused_3526_);
                        v_unused_3527_ = crate::leanh::lean_ctor_get(v_r_3475_, 2);
                        crate::leanh::lean_dec(v_unused_3527_);
                        v_unused_3528_ = crate::leanh::lean_ctor_get(v_r_3475_, 1);
                        crate::leanh::lean_dec(v_unused_3528_);
                        v_unused_3529_ = crate::leanh::lean_ctor_get(v_r_3475_, 0);
                        crate::leanh::lean_dec(v_unused_3529_);
                        v___x_3497_ = v_r_3475_;
                        v_isShared_3498_ = v_isSharedCheck_3524_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3475_);
                        v___x_3497_ = crate::leanh::lean_box(0);
                        v_isShared_3498_ = v_isSharedCheck_3524_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3464_);
                    v___x_3530_ = lean_nat_add(v___x_3469_, v_size_3471_);
                    crate::leanh::lean_dec(v_size_3471_);
                    v___x_3531_ = lean_nat_add(v___x_3530_, v_size_3470_);
                    crate::leanh::lean_dec(v___x_3530_);
                    v___x_3532_ = lean_nat_add(v___x_3469_, v_size_3470_);
                    v___x_3533_ = lean_nat_add(v___x_3532_, v_size_3488_);
                    crate::leanh::lean_dec(v___x_3532_);
                    crate::leanh::lean_inc_ref(v_r_3462_);
                    if v_isShared_3486_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3485_, 4, v_r_3462_);
                        crate::leanh::lean_ctor_set(v___x_3485_, 3, v_r_3475_);
                        crate::leanh::lean_ctor_set(v___x_3485_, 2, v_v_3460_);
                        crate::leanh::lean_ctor_set(v___x_3485_, 1, v_k_3459_);
                        crate::leanh::lean_ctor_set(v___x_3485_, 0, v___x_3533_);
                        v___x_3535_ = v___x_3485_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3548_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3533_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3459_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_v_3460_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_r_3475_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 4, v_r_3462_);
                        v___x_3535_ = v_reuseFailAlloc_3548_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3499_ = lean_nat_add(v___x_3469_, v_size_3471_);
                crate::leanh::lean_dec(v_size_3471_);
                v___x_3500_ = lean_nat_add(v___x_3499_, v_size_3470_);
                crate::leanh::lean_dec(v___x_3499_);
                v___x_3512_ = lean_nat_add(v___x_3469_, v_size_3487_);
                if crate::leanh::lean_obj_tag(v_l_3491_) == 0 {
                    v_size_3522_ = crate::leanh::lean_ctor_get(v_l_3491_, 0);
                    crate::leanh::lean_inc(v_size_3522_);
                    v___y_3514_ = v_size_3522_;
                    state = 8;
                    continue;
                } else {
                    v___x_3523_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3514_ = v___x_3523_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3505_ = lean_nat_add(v___y_3502_, v___y_3504_);
                crate::leanh::lean_dec(v___y_3504_);
                crate::leanh::lean_dec(v___y_3502_);
                if v_isShared_3498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3497_, 4, v_r_3462_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 3, v_r_3492_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 0, v___x_3505_);
                    v___x_3507_ = v___x_3497_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 3, v_r_3492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 4, v_r_3462_);
                    v___x_3507_ = v_reuseFailAlloc_3511_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3486_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3485_, 4, v___x_3507_);
                    crate::leanh::lean_ctor_set(v___x_3485_, 3, v___y_3503_);
                    crate::leanh::lean_ctor_set(v___x_3485_, 2, v_v_3490_);
                    crate::leanh::lean_ctor_set(v___x_3485_, 1, v_k_3489_);
                    crate::leanh::lean_ctor_set(v___x_3485_, 0, v___x_3500_);
                    v___x_3509_ = v___x_3485_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3510_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_k_3489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_v_3490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 3, v___y_3503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 4, v___x_3507_);
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
                crate::leanh::lean_dec(v___y_3514_);
                crate::leanh::lean_dec(v___x_3512_);
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 4, v_l_3491_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 3, v_l_3474_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 2, v_v_3473_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 1, v_k_3472_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3515_);
                    v___x_3517_ = v___x_3464_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_l_3474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_l_3491_);
                    v___x_3517_ = v_reuseFailAlloc_3521_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3518_ = lean_nat_add(v___x_3469_, v_size_3470_);
                if crate::leanh::lean_obj_tag(v_r_3492_) == 0 {
                    v_size_3519_ = crate::leanh::lean_ctor_get(v_r_3492_, 0);
                    crate::leanh::lean_inc(v_size_3519_);
                    v___y_3502_ = v___x_3518_;
                    v___y_3503_ = v___x_3517_;
                    v___y_3504_ = v_size_3519_;
                    state = 5;
                    continue;
                } else {
                    v___x_3520_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3502_ = v___x_3518_;
                    v___y_3503_ = v___x_3517_;
                    v___y_3504_ = v___x_3520_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3542_ = (!crate::leanh::lean_is_exclusive(v_r_3462_)) as u8;
                if v_isSharedCheck_3542_ == 0 {
                    v_unused_3543_ = crate::leanh::lean_ctor_get(v_r_3462_, 4);
                    crate::leanh::lean_dec(v_unused_3543_);
                    v_unused_3544_ = crate::leanh::lean_ctor_get(v_r_3462_, 3);
                    crate::leanh::lean_dec(v_unused_3544_);
                    v_unused_3545_ = crate::leanh::lean_ctor_get(v_r_3462_, 2);
                    crate::leanh::lean_dec(v_unused_3545_);
                    v_unused_3546_ = crate::leanh::lean_ctor_get(v_r_3462_, 1);
                    crate::leanh::lean_dec(v_unused_3546_);
                    v_unused_3547_ = crate::leanh::lean_ctor_get(v_r_3462_, 0);
                    crate::leanh::lean_dec(v_unused_3547_);
                    v___x_3537_ = v_r_3462_;
                    v_isShared_3538_ = v_isSharedCheck_3542_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_3462_);
                    v___x_3537_ = crate::leanh::lean_box(0);
                    v_isShared_3538_ = v_isSharedCheck_3542_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3538_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3537_, 4, v___x_3535_);
                    crate::leanh::lean_ctor_set(v___x_3537_, 3, v_l_3474_);
                    crate::leanh::lean_ctor_set(v___x_3537_, 2, v_v_3473_);
                    crate::leanh::lean_ctor_set(v___x_3537_, 1, v_k_3472_);
                    crate::leanh::lean_ctor_set(v___x_3537_, 0, v___x_3531_);
                    v___x_3540_ = v___x_3537_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_k_3472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_v_3473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 3, v_l_3474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 4, v___x_3535_);
                    v___x_3540_ = v_reuseFailAlloc_3541_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3540_;
            }
            13 => {
                v___x_3562_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_3556_);
                if v_isShared_3561_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3560_, 3, v_r_3556_);
                    crate::leanh::lean_ctor_set(v___x_3560_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v___x_3560_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v___x_3560_, 0, v___x_3469_);
                    v___x_3564_ = v___x_3560_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3568_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_r_3556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_r_3556_);
                    v___x_3564_ = v_reuseFailAlloc_3568_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 4, v___x_3564_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 3, v_l_3555_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 2, v_v_3558_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 1, v_k_3557_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3562_);
                    v___x_3566_ = v___x_3464_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3567_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_k_3557_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 2, v_v_3558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 3, v_l_3555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 4, v___x_3564_);
                    v___x_3566_ = v_reuseFailAlloc_3567_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3566_;
            }
            16 => {
                v_k_3578_ = crate::leanh::lean_ctor_get(v_r_3572_, 1);
                v_v_3579_ = crate::leanh::lean_ctor_get(v_r_3572_, 2);
                v_isSharedCheck_3593_ = (!crate::leanh::lean_is_exclusive(v_r_3572_)) as u8;
                if v_isSharedCheck_3593_ == 0 {
                    v_unused_3594_ = crate::leanh::lean_ctor_get(v_r_3572_, 4);
                    crate::leanh::lean_dec(v_unused_3594_);
                    v_unused_3595_ = crate::leanh::lean_ctor_get(v_r_3572_, 3);
                    crate::leanh::lean_dec(v_unused_3595_);
                    v_unused_3596_ = crate::leanh::lean_ctor_get(v_r_3572_, 0);
                    crate::leanh::lean_dec(v_unused_3596_);
                    v___x_3581_ = v_r_3572_;
                    v_isShared_3582_ = v_isSharedCheck_3593_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3579_);
                    crate::leanh::lean_inc(v_k_3578_);
                    crate::leanh::lean_dec(v_r_3572_);
                    v___x_3581_ = crate::leanh::lean_box(0);
                    v_isShared_3582_ = v_isSharedCheck_3593_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3583_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3581_, 4, v_l_3555_);
                    crate::leanh::lean_ctor_set(v___x_3581_, 3, v_l_3555_);
                    crate::leanh::lean_ctor_set(v___x_3581_, 2, v_v_3574_);
                    crate::leanh::lean_ctor_set(v___x_3581_, 1, v_k_3573_);
                    crate::leanh::lean_ctor_set(v___x_3581_, 0, v___x_3469_);
                    v___x_3585_ = v___x_3581_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3592_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_k_3573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_v_3574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 3, v_l_3555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 4, v_l_3555_);
                    v___x_3585_ = v_reuseFailAlloc_3592_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3576_, 4, v_l_3555_);
                    crate::leanh::lean_ctor_set(v___x_3576_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v___x_3576_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v___x_3576_, 0, v___x_3469_);
                    v___x_3587_ = v___x_3576_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3591_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 3, v_l_3555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 4, v_l_3555_);
                    v___x_3587_ = v_reuseFailAlloc_3591_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 4, v___x_3587_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 3, v___x_3585_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 2, v_v_3579_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 1, v_k_3578_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3583_);
                    v___x_3589_ = v___x_3464_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3590_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_k_3578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_v_3579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 3, v___x_3585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 4, v___x_3587_);
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
                v_size_3627_ = crate::leanh::lean_ctor_get(v_l_3614_, 0);
                v_k_3628_ = crate::leanh::lean_ctor_get(v_l_3614_, 1);
                v_v_3629_ = crate::leanh::lean_ctor_get(v_l_3614_, 2);
                v_l_3630_ = crate::leanh::lean_ctor_get(v_l_3614_, 3);
                v_r_3631_ = crate::leanh::lean_ctor_get(v_l_3614_, 4);
                v_size_3632_ = crate::leanh::lean_ctor_get(v_r_3615_, 0);
                v___x_3633_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3634_ = lean_nat_mul(v___x_3633_, v_size_3632_);
                v___x_3635_ = lean_nat_dec_lt(v_size_3627_, v___x_3634_);
                crate::leanh::lean_dec(v___x_3634_);
                if v___x_3635_ == 0 {
                    crate::leanh::lean_inc(v_r_3631_);
                    crate::leanh::lean_inc(v_l_3630_);
                    crate::leanh::lean_inc(v_v_3629_);
                    crate::leanh::lean_inc(v_k_3628_);
                    v_isSharedCheck_3663_ = (!crate::leanh::lean_is_exclusive(v_l_3614_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v_unused_3664_ = crate::leanh::lean_ctor_get(v_l_3614_, 4);
                        crate::leanh::lean_dec(v_unused_3664_);
                        v_unused_3665_ = crate::leanh::lean_ctor_get(v_l_3614_, 3);
                        crate::leanh::lean_dec(v_unused_3665_);
                        v_unused_3666_ = crate::leanh::lean_ctor_get(v_l_3614_, 2);
                        crate::leanh::lean_dec(v_unused_3666_);
                        v_unused_3667_ = crate::leanh::lean_ctor_get(v_l_3614_, 1);
                        crate::leanh::lean_dec(v_unused_3667_);
                        v_unused_3668_ = crate::leanh::lean_ctor_get(v_l_3614_, 0);
                        crate::leanh::lean_dec(v_unused_3668_);
                        v___x_3637_ = v_l_3614_;
                        v_isShared_3638_ = v_isSharedCheck_3663_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_3614_);
                        v___x_3637_ = crate::leanh::lean_box(0);
                        v_isShared_3638_ = v_isSharedCheck_3663_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3464_);
                    v___x_3669_ = lean_nat_add(v___x_3609_, v_size_3610_);
                    v___x_3670_ = lean_nat_add(v___x_3669_, v_size_3611_);
                    crate::leanh::lean_dec(v_size_3611_);
                    v___x_3671_ = lean_nat_add(v___x_3669_, v_size_3627_);
                    crate::leanh::lean_dec(v___x_3669_);
                    crate::leanh::lean_inc_ref(v_l_3461_);
                    if v_isShared_3626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3625_, 4, v_l_3614_);
                        crate::leanh::lean_ctor_set(v___x_3625_, 3, v_l_3461_);
                        crate::leanh::lean_ctor_set(v___x_3625_, 2, v_v_3460_);
                        crate::leanh::lean_ctor_set(v___x_3625_, 1, v_k_3459_);
                        crate::leanh::lean_ctor_set(v___x_3625_, 0, v___x_3671_);
                        v___x_3673_ = v___x_3625_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3686_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3671_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_k_3459_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_v_3460_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 3, v_l_3461_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 4, v_l_3614_);
                        v___x_3673_ = v_reuseFailAlloc_3686_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3639_ = lean_nat_add(v___x_3609_, v_size_3610_);
                v___x_3640_ = lean_nat_add(v___x_3639_, v_size_3611_);
                crate::leanh::lean_dec(v_size_3611_);
                if crate::leanh::lean_obj_tag(v_l_3630_) == 0 {
                    v_size_3661_ = crate::leanh::lean_ctor_get(v_l_3630_, 0);
                    crate::leanh::lean_inc(v_size_3661_);
                    v___y_3653_ = v_size_3661_;
                    state = 29;
                    continue;
                } else {
                    v___x_3662_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3653_ = v___x_3662_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3645_ = lean_nat_add(v___y_3643_, v___y_3644_);
                crate::leanh::lean_dec(v___y_3644_);
                crate::leanh::lean_dec(v___y_3643_);
                if v_isShared_3638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3637_, 4, v_r_3615_);
                    crate::leanh::lean_ctor_set(v___x_3637_, 3, v_r_3631_);
                    crate::leanh::lean_ctor_set(v___x_3637_, 2, v_v_3613_);
                    crate::leanh::lean_ctor_set(v___x_3637_, 1, v_k_3612_);
                    crate::leanh::lean_ctor_set(v___x_3637_, 0, v___x_3645_);
                    v___x_3647_ = v___x_3637_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_r_3631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_r_3615_);
                    v___x_3647_ = v_reuseFailAlloc_3651_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3625_, 4, v___x_3647_);
                    crate::leanh::lean_ctor_set(v___x_3625_, 3, v___y_3642_);
                    crate::leanh::lean_ctor_set(v___x_3625_, 2, v_v_3629_);
                    crate::leanh::lean_ctor_set(v___x_3625_, 1, v_k_3628_);
                    crate::leanh::lean_ctor_set(v___x_3625_, 0, v___x_3640_);
                    v___x_3649_ = v___x_3625_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_k_3628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_v_3629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 3, v___y_3642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 4, v___x_3647_);
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
                crate::leanh::lean_dec(v___y_3653_);
                crate::leanh::lean_dec(v___x_3639_);
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 4, v_l_3630_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3464_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_l_3461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_l_3630_);
                    v___x_3656_ = v_reuseFailAlloc_3660_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3657_ = lean_nat_add(v___x_3609_, v_size_3632_);
                if crate::leanh::lean_obj_tag(v_r_3631_) == 0 {
                    v_size_3658_ = crate::leanh::lean_ctor_get(v_r_3631_, 0);
                    crate::leanh::lean_inc(v_size_3658_);
                    v___y_3642_ = v___x_3656_;
                    v___y_3643_ = v___x_3657_;
                    v___y_3644_ = v_size_3658_;
                    state = 26;
                    continue;
                } else {
                    v___x_3659_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3642_ = v___x_3656_;
                    v___y_3643_ = v___x_3657_;
                    v___y_3644_ = v___x_3659_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3680_ = (!crate::leanh::lean_is_exclusive(v_l_3461_)) as u8;
                if v_isSharedCheck_3680_ == 0 {
                    v_unused_3681_ = crate::leanh::lean_ctor_get(v_l_3461_, 4);
                    crate::leanh::lean_dec(v_unused_3681_);
                    v_unused_3682_ = crate::leanh::lean_ctor_get(v_l_3461_, 3);
                    crate::leanh::lean_dec(v_unused_3682_);
                    v_unused_3683_ = crate::leanh::lean_ctor_get(v_l_3461_, 2);
                    crate::leanh::lean_dec(v_unused_3683_);
                    v_unused_3684_ = crate::leanh::lean_ctor_get(v_l_3461_, 1);
                    crate::leanh::lean_dec(v_unused_3684_);
                    v_unused_3685_ = crate::leanh::lean_ctor_get(v_l_3461_, 0);
                    crate::leanh::lean_dec(v_unused_3685_);
                    v___x_3675_ = v_l_3461_;
                    v_isShared_3676_ = v_isSharedCheck_3680_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_3461_);
                    v___x_3675_ = crate::leanh::lean_box(0);
                    v_isShared_3676_ = v_isSharedCheck_3680_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3675_, 4, v_r_3615_);
                    crate::leanh::lean_ctor_set(v___x_3675_, 3, v___x_3673_);
                    crate::leanh::lean_ctor_set(v___x_3675_, 2, v_v_3613_);
                    crate::leanh::lean_ctor_set(v___x_3675_, 1, v_k_3612_);
                    crate::leanh::lean_ctor_set(v___x_3675_, 0, v___x_3670_);
                    v___x_3678_ = v___x_3675_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_k_3612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_v_3613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 3, v___x_3673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 4, v_r_3615_);
                    v___x_3678_ = v_reuseFailAlloc_3679_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3678_;
            }
            34 => {
                v_k_3700_ = crate::leanh::lean_ctor_get(v_l_3693_, 1);
                v_v_3701_ = crate::leanh::lean_ctor_get(v_l_3693_, 2);
                v_isSharedCheck_3715_ = (!crate::leanh::lean_is_exclusive(v_l_3693_)) as u8;
                if v_isSharedCheck_3715_ == 0 {
                    v_unused_3716_ = crate::leanh::lean_ctor_get(v_l_3693_, 4);
                    crate::leanh::lean_dec(v_unused_3716_);
                    v_unused_3717_ = crate::leanh::lean_ctor_get(v_l_3693_, 3);
                    crate::leanh::lean_dec(v_unused_3717_);
                    v_unused_3718_ = crate::leanh::lean_ctor_get(v_l_3693_, 0);
                    crate::leanh::lean_dec(v_unused_3718_);
                    v___x_3703_ = v_l_3693_;
                    v_isShared_3704_ = v_isSharedCheck_3715_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3701_);
                    crate::leanh::lean_inc(v_k_3700_);
                    crate::leanh::lean_dec(v_l_3693_);
                    v___x_3703_ = crate::leanh::lean_box(0);
                    v_isShared_3704_ = v_isSharedCheck_3715_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3705_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_3694_, 2);
                if v_isShared_3704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3703_, 4, v_r_3694_);
                    crate::leanh::lean_ctor_set(v___x_3703_, 3, v_r_3694_);
                    crate::leanh::lean_ctor_set(v___x_3703_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v___x_3703_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v___x_3703_, 0, v___x_3609_);
                    v___x_3707_ = v___x_3703_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_r_3694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 4, v_r_3694_);
                    v___x_3707_ = v_reuseFailAlloc_3714_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_3694_);
                if v_isShared_3699_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3698_, 3, v_r_3694_);
                    crate::leanh::lean_ctor_set(v___x_3698_, 0, v___x_3609_);
                    v___x_3709_ = v___x_3698_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3713_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_r_3694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_r_3694_);
                    v___x_3709_ = v_reuseFailAlloc_3713_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 4, v___x_3709_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 3, v___x_3707_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 2, v_v_3701_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 1, v_k_3700_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3705_);
                    v___x_3711_ = v___x_3464_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3712_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_k_3700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3712_, 2, v_v_3701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3712_, 3, v___x_3707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3712_, 4, v___x_3709_);
                    v___x_3711_ = v_reuseFailAlloc_3712_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3711_;
            }
            39 => {
                v___x_3728_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3726_, 4, v_l_3693_);
                    crate::leanh::lean_ctor_set(v___x_3726_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v___x_3726_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v___x_3726_, 0, v___x_3609_);
                    v___x_3730_ = v___x_3726_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_k_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_v_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_l_3693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_l_3693_);
                    v___x_3730_ = v_reuseFailAlloc_3734_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 4, v_r_3722_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 3, v___x_3730_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 2, v_v_3724_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 1, v_k_3723_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3728_);
                    v___x_3732_ = v___x_3464_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 3, v___x_3730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_r_3722_);
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
    mut v_cmp_3746_: *mut crate::leanh::LeanObject,
    mut v_k_3747_: *mut crate::leanh::LeanObject,
    mut v_t_3748_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3748_) == 0 {
                    v_k_3749_ = crate::leanh::lean_ctor_get(v_t_3748_, 1);
                    crate::leanh::lean_inc(v_k_3749_);
                    v_l_3750_ = crate::leanh::lean_ctor_get(v_t_3748_, 3);
                    crate::leanh::lean_inc(v_l_3750_);
                    v_r_3751_ = crate::leanh::lean_ctor_get(v_t_3748_, 4);
                    crate::leanh::lean_inc(v_r_3751_);
                    crate::leanh::lean_dec_ref_known(v_t_3748_, 5);
                    crate::leanh::lean_inc_ref(v_cmp_3746_);
                    crate::leanh::lean_inc(v_k_3747_);
                    v___x_3752_ = crate::leanh::lean_apply_2(v_cmp_3746_, v_k_3747_, v_k_3749_);
                    v___x_3753_ = (crate::leanh::lean_unbox(v___x_3752_) as u8);
                    match v___x_3753_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_3751_);
                            v_t_3748_ = v_l_3750_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_3751_);
                            crate::leanh::lean_dec(v_l_3750_);
                            crate::leanh::lean_dec(v_k_3747_);
                            crate::leanh::lean_dec_ref(v_cmp_3746_);
                            v___x_3755_ = 1;
                            return v___x_3755_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_3750_);
                            v_t_3748_ = v_r_3751_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3747_);
                    crate::leanh::lean_dec_ref(v_cmp_3746_);
                    v___x_3757_ = 0;
                    return v___x_3757_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg___boxed(
    mut v_cmp_3758_: *mut crate::leanh::LeanObject,
    mut v_k_3759_: *mut crate::leanh::LeanObject,
    mut v_t_3760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3761_: u8 = 0;
    let mut v_r_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(
            v_cmp_3758_,
            v_k_3759_,
            v_t_3760_,
        );
    v_r_3762_ = crate::leanh::lean_box((v_res_3761_) as usize);
    return v_r_3762_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
    mut v_cmp_3763_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3764_: *mut crate::leanh::LeanObject,
    mut v_b_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3764_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_3763_);
                    return v_b_3765_;
                } else {
                    v_head_3766_ = crate::leanh::lean_ctor_get(v_as_x27_3764_, 0);
                    v_tail_3767_ = crate::leanh::lean_ctor_get(v_as_x27_3764_, 1);
                    crate::leanh::lean_inc(v_b_3765_);
                    crate::leanh::lean_inc(v_head_3766_);
                    crate::leanh::lean_inc_ref(v_cmp_3763_);
                    v___x_3768_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_3763_, v_head_3766_, v_b_3765_);
                    if v___x_3768_ == 0 {
                        v___x_3769_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_head_3766_);
                        crate::leanh::lean_inc_ref(v_cmp_3763_);
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
    mut v_cmp_3773_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3774_: *mut crate::leanh::LeanObject,
    mut v_b_3775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3776_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
        v_cmp_3773_,
        v_as_x27_3774_,
        v_b_3775_,
    );
    crate::leanh::lean_dec(v_as_x27_3774_);
    return v_res_3776_;
}
pub unsafe fn l_Std_TreeSet_ofList___redArg(
    mut v_l_3777_: *mut crate::leanh::LeanObject,
    mut v_cmp_3778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_3779_ = crate::leanh::lean_box(1);
    v___x_3780_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
        v_cmp_3778_,
        v_l_3777_,
        v_r_3779_,
    );
    return v___x_3780_;
}
pub unsafe fn l_Std_TreeSet_ofList___redArg___boxed(
    mut v_l_3781_: *mut crate::leanh::LeanObject,
    mut v_cmp_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3783_ = l_Std_TreeSet_ofList___redArg(v_l_3781_, v_cmp_3782_);
    crate::leanh::lean_dec(v_l_3781_);
    return v_res_3783_;
}
pub unsafe fn l_Std_TreeSet_ofList(
    mut v_00_u03b1_3784_: *mut crate::leanh::LeanObject,
    mut v_l_3785_: *mut crate::leanh::LeanObject,
    mut v_cmp_3786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = l_Std_TreeSet_ofList___redArg(v_l_3785_, v_cmp_3786_);
    return v___x_3787_;
}
pub unsafe fn l_Std_TreeSet_ofList___boxed(
    mut v_00_u03b1_3788_: *mut crate::leanh::LeanObject,
    mut v_l_3789_: *mut crate::leanh::LeanObject,
    mut v_cmp_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Std_TreeSet_ofList(v_00_u03b1_3788_, v_l_3789_, v_cmp_3790_);
    crate::leanh::lean_dec(v_l_3789_);
    return v_res_3791_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(
    mut v_00_u03b1_3792_: *mut crate::leanh::LeanObject,
    mut v_cmp_3793_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3794_: *mut crate::leanh::LeanObject,
    mut v_k_3795_: *mut crate::leanh::LeanObject,
    mut v_t_3796_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_3798_: *mut crate::leanh::LeanObject,
    mut v_cmp_3799_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3800_: *mut crate::leanh::LeanObject,
    mut v_k_3801_: *mut crate::leanh::LeanObject,
    mut v_t_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3803_: u8 = 0;
    let mut v_r_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0(
        v_00_u03b1_3798_,
        v_cmp_3799_,
        v_00_u03b2_3800_,
        v_k_3801_,
        v_t_3802_,
    );
    v_r_3804_ = crate::leanh::lean_box((v_res_3803_) as usize);
    return v_r_3804_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1(
    mut v_00_u03b1_3805_: *mut crate::leanh::LeanObject,
    mut v_cmp_3806_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3807_: *mut crate::leanh::LeanObject,
    mut v_k_3808_: *mut crate::leanh::LeanObject,
    mut v_v_3809_: *mut crate::leanh::LeanObject,
    mut v_t_3810_: *mut crate::leanh::LeanObject,
    mut v_hl_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_TreeSet_ofList_spec__1___redArg(
        v_cmp_3806_,
        v_k_3808_,
        v_v_3809_,
        v_t_3810_,
    );
    return v___x_3812_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(
    mut v_00_u03b1_3813_: *mut crate::leanh::LeanObject,
    mut v_cmp_3814_: *mut crate::leanh::LeanObject,
    mut v_as_3815_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3816_: *mut crate::leanh::LeanObject,
    mut v_b_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3819_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___redArg(
        v_cmp_3814_,
        v_as_x27_3816_,
        v_b_3817_,
    );
    return v___x_3819_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2___boxed(
    mut v_00_u03b1_3820_: *mut crate::leanh::LeanObject,
    mut v_cmp_3821_: *mut crate::leanh::LeanObject,
    mut v_as_3822_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3823_: *mut crate::leanh::LeanObject,
    mut v_b_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3826_ = l_List_forIn_x27_loop___at___00Std_TreeSet_ofList_spec__2(
        v_00_u03b1_3820_,
        v_cmp_3821_,
        v_as_3822_,
        v_as_x27_3823_,
        v_b_3824_,
        v_a_3825_,
    );
    crate::leanh::lean_dec(v_as_x27_3823_);
    crate::leanh::lean_dec(v_as_3822_);
    return v_res_3826_;
}
pub unsafe fn l_Std_TreeSet_toArray___redArg___lam__0(
    mut v_l_3827_: *mut crate::leanh::LeanObject,
    mut v_k_3828_: *mut crate::leanh::LeanObject,
    mut v_x_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = lean_array_push(v_l_3827_, v_k_3828_);
    return v___x_3830_;
}
pub unsafe fn l_Std_TreeSet_toArray___redArg(
    mut v_t_3832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3833_ = l_Std_TreeSet_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_3832_) == 0 {
                    v_size_3838_ = crate::leanh::lean_ctor_get(v_t_3832_, 0);
                    crate::leanh::lean_inc(v_size_3838_);
                    v___y_3835_ = v_size_3838_;
                    state = 1;
                    continue;
                } else {
                    v___x_3839_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3835_ = v___x_3839_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3836_ = lean_mk_empty_array_with_capacity(v___y_3835_);
                crate::leanh::lean_dec(v___y_3835_);
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
    mut v_00_u03b1_3840_: *mut crate::leanh::LeanObject,
    mut v_cmp_3841_: *mut crate::leanh::LeanObject,
    mut v_t_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3843_ = l_Std_TreeSet_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_3842_) == 0 {
                    v_size_3848_ = crate::leanh::lean_ctor_get(v_t_3842_, 0);
                    crate::leanh::lean_inc(v_size_3848_);
                    v___y_3845_ = v_size_3848_;
                    state = 1;
                    continue;
                } else {
                    v___x_3849_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3845_ = v___x_3849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3846_ = lean_mk_empty_array_with_capacity(v___y_3845_);
                crate::leanh::lean_dec(v___y_3845_);
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
    mut v_00_u03b1_3850_: *mut crate::leanh::LeanObject,
    mut v_cmp_3851_: *mut crate::leanh::LeanObject,
    mut v_t_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Std_TreeSet_toArray(v_00_u03b1_3850_, v_cmp_3851_, v_t_3852_);
    crate::leanh::lean_dec_ref(v_cmp_3851_);
    return v_res_3853_;
}
pub unsafe fn _init_l_Std_TreeSet_ofArray___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet___auto__1___closed__26_once),
        _init_l_Std_TreeSet___auto__1___closed__26,
    );
    return v___x_3854_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(
    mut v_cmp_3855_: *mut crate::leanh::LeanObject,
    mut v_as_3856_: *mut crate::leanh::LeanObject,
    mut v_sz_3857_: usize,
    mut v_i_3858_: usize,
    mut v_b_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: usize = 0;
    let mut v___x_3863_: usize = 0;
    let mut v___x_3865_: u8 = 0;
    let mut v_a_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3865_ = lean_usize_dec_lt(v_i_3858_, v_sz_3857_);
                if v___x_3865_ == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_3855_);
                    return v_b_3859_;
                } else {
                    v_a_3866_ = lean_array_uget_borrowed(v_as_3856_, v_i_3858_);
                    crate::leanh::lean_inc(v_b_3859_);
                    crate::leanh::lean_inc(v_a_3866_);
                    crate::leanh::lean_inc_ref(v_cmp_3855_);
                    v___x_3867_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_TreeSet_ofList_spec__0___redArg(v_cmp_3855_, v_a_3866_, v_b_3859_);
                    if v___x_3867_ == 0 {
                        v___x_3868_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_a_3866_);
                        crate::leanh::lean_inc_ref(v_cmp_3855_);
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
    mut v_cmp_3870_: *mut crate::leanh::LeanObject,
    mut v_as_3871_: *mut crate::leanh::LeanObject,
    mut v_sz_3872_: *mut crate::leanh::LeanObject,
    mut v_i_3873_: *mut crate::leanh::LeanObject,
    mut v_b_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3875_: usize = 0;
    let mut v_i_boxed_3876_: usize = 0;
    let mut v_res_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3875_ = crate::leanh::lean_unbox_usize(v_sz_3872_);
    crate::leanh::lean_dec(v_sz_3872_);
    v_i_boxed_3876_ = crate::leanh::lean_unbox_usize(v_i_3873_);
    crate::leanh::lean_dec(v_i_3873_);
    v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_3870_, v_as_3871_, v_sz_boxed_3875_, v_i_boxed_3876_, v_b_3874_);
    crate::leanh::lean_dec_ref(v_as_3871_);
    return v_res_3877_;
}
pub unsafe fn l_Std_TreeSet_ofArray___redArg(
    mut v_a_3878_: *mut crate::leanh::LeanObject,
    mut v_cmp_3879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3881_: usize = 0;
    let mut v___x_3882_: usize = 0;
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_3880_ = crate::leanh::lean_box(1);
    v_sz_3881_ = lean_array_size(v_a_3878_);
    v___x_3882_ = 0usize;
    v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_3879_, v_a_3878_, v_sz_3881_, v___x_3882_, v_r_3880_);
    return v___x_3883_;
}
pub unsafe fn l_Std_TreeSet_ofArray___redArg___boxed(
    mut v_a_3884_: *mut crate::leanh::LeanObject,
    mut v_cmp_3885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3886_ = l_Std_TreeSet_ofArray___redArg(v_a_3884_, v_cmp_3885_);
    crate::leanh::lean_dec_ref(v_a_3884_);
    return v_res_3886_;
}
pub unsafe fn l_Std_TreeSet_ofArray(
    mut v_00_u03b1_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
    mut v_cmp_3889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = l_Std_TreeSet_ofArray___redArg(v_a_3888_, v_cmp_3889_);
    return v___x_3890_;
}
pub unsafe fn l_Std_TreeSet_ofArray___boxed(
    mut v_00_u03b1_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_cmp_3893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3894_ = l_Std_TreeSet_ofArray(v_00_u03b1_3891_, v_a_3892_, v_cmp_3893_);
    crate::leanh::lean_dec_ref(v_a_3892_);
    return v_res_3894_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(
    mut v_00_u03b1_3895_: *mut crate::leanh::LeanObject,
    mut v_cmp_3896_: *mut crate::leanh::LeanObject,
    mut v_as_3897_: *mut crate::leanh::LeanObject,
    mut v_sz_3898_: usize,
    mut v_i_3899_: usize,
    mut v_b_3900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___redArg(v_cmp_3896_, v_as_3897_, v_sz_3898_, v_i_3899_, v_b_3900_);
    return v___x_3901_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0___boxed(
    mut v_00_u03b1_3902_: *mut crate::leanh::LeanObject,
    mut v_cmp_3903_: *mut crate::leanh::LeanObject,
    mut v_as_3904_: *mut crate::leanh::LeanObject,
    mut v_sz_3905_: *mut crate::leanh::LeanObject,
    mut v_i_3906_: *mut crate::leanh::LeanObject,
    mut v_b_3907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3908_: usize = 0;
    let mut v_i_boxed_3909_: usize = 0;
    let mut v_res_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3908_ = crate::leanh::lean_unbox_usize(v_sz_3905_);
    crate::leanh::lean_dec(v_sz_3905_);
    v_i_boxed_3909_ = crate::leanh::lean_unbox_usize(v_i_3906_);
    crate::leanh::lean_dec(v_i_3906_);
    v_res_3910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_TreeSet_ofArray_spec__0(v_00_u03b1_3902_, v_cmp_3903_, v_as_3904_, v_sz_boxed_3908_, v_i_boxed_3909_, v_b_3907_);
    crate::leanh::lean_dec_ref(v_as_3904_);
    return v_res_3910_;
}
pub unsafe fn l_Std_TreeSet_merge___redArg___lam__0(
    mut v_b_u2082_3913_: *mut crate::leanh::LeanObject,
    mut v_x_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3914_) == 0 {
        let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3915_, 0, v_b_u2082_3913_);
        return v___x_3915_;
    } else {
        let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3916_ = l_Std_TreeSet_merge___redArg___lam__0___closed__0;
        return v___x_3916_;
    }
}
pub unsafe fn l_Std_TreeSet_merge___redArg___lam__0___boxed(
    mut v_b_u2082_3917_: *mut crate::leanh::LeanObject,
    mut v_x_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Std_TreeSet_merge___redArg___lam__0(v_b_u2082_3917_, v_x_3918_);
    crate::leanh::lean_dec(v_x_3918_);
    return v_res_3919_;
}
pub unsafe fn l_Std_TreeSet_merge___redArg___lam__1(
    mut v_cmp_3920_: *mut crate::leanh::LeanObject,
    mut v_t_3921_: *mut crate::leanh::LeanObject,
    mut v_a_3922_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_3923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3924_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_merge___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3924_, 0, v_b_u2082_3923_);
    v___x_3925_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v_cmp_3920_,
        v_a_3922_,
        v___f_3924_,
        v_t_3921_,
    );
    return v___x_3925_;
}
pub unsafe fn l_Std_TreeSet_merge___redArg(
    mut v_cmp_3926_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3927_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3929_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3929_, 0, v_cmp_3926_);
    v___x_3930_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3929_, v_t_u2081_3927_, v_t_u2082_3928_);
    return v___x_3930_;
}
pub unsafe fn l_Std_TreeSet_merge(
    mut v_00_u03b1_3931_: *mut crate::leanh::LeanObject,
    mut v_cmp_3932_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3933_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3935_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_merge___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3935_, 0, v_cmp_3932_);
    v___x_3936_ =
        l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3935_, v_t_u2081_3933_, v_t_u2082_3934_);
    return v___x_3936_;
}
pub unsafe fn l_Std_TreeSet_insertMany___redArg___lam__0(
    mut v_cmp_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_____s_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3940_: u8 = 0;
    crate::leanh::lean_inc(v_____s_3939_);
    crate::leanh::lean_inc(v_a_3938_);
    crate::leanh::lean_inc_ref(v_cmp_3937_);
    v___x_3940_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_3937_, v_a_3938_, v_____s_3939_);
    if v___x_3940_ == 0 {
        let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3941_ = crate::leanh::lean_box(0);
        v___x_3942_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_3937_,
            v_a_3938_,
            v___x_3941_,
            v_____s_3939_,
        );
        v___x_3943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3943_, 0, v___x_3942_);
        return v___x_3943_;
    } else {
        let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3938_);
        crate::leanh::lean_dec_ref(v_cmp_3937_);
        v___x_3944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3944_, 0, v_____s_3939_);
        return v___x_3944_;
    }
}
pub unsafe fn l_Std_TreeSet_insertMany___redArg(
    mut v_cmp_3945_: *mut crate::leanh::LeanObject,
    mut v_inst_3946_: *mut crate::leanh::LeanObject,
    mut v_t_3947_: *mut crate::leanh::LeanObject,
    mut v_l_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3949_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3949_, 0, v_cmp_3945_);
    v___x_3950_ = crate::leanh::lean_apply_4(
        v_inst_3946_,
        crate::leanh::lean_box(0),
        v_l_3948_,
        v_t_3947_,
        v___f_3949_,
    );
    return v___x_3950_;
}
pub unsafe fn l_Std_TreeSet_insertMany(
    mut v_00_u03b1_3951_: *mut crate::leanh::LeanObject,
    mut v_cmp_3952_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3953_: *mut crate::leanh::LeanObject,
    mut v_inst_3954_: *mut crate::leanh::LeanObject,
    mut v_t_3955_: *mut crate::leanh::LeanObject,
    mut v_l_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3957_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3957_, 0, v_cmp_3952_);
    v___x_3958_ = crate::leanh::lean_apply_4(
        v_inst_3954_,
        crate::leanh::lean_box(0),
        v_l_3956_,
        v_t_3955_,
        v___f_3957_,
    );
    return v___x_3958_;
}
pub unsafe fn l_Std_TreeSet_union___redArg(
    mut v_cmp_3959_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3960_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3962_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3959_,
        v_t_u2081_3960_,
        v_t_u2082_3961_,
    );
    return v___x_3962_;
}
pub unsafe fn l_Std_TreeSet_union(
    mut v_00_u03b1_3963_: *mut crate::leanh::LeanObject,
    mut v_cmp_3964_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3965_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3967_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(
        v_cmp_3964_,
        v_t_u2081_3965_,
        v_t_u2082_3966_,
    );
    return v___x_3967_;
}
pub unsafe fn l_Std_TreeSet_instUnion___redArg(
    mut v_cmp_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3969_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_union as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3969_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3969_, 1, v_cmp_3968_);
    return v___x_3969_;
}
pub unsafe fn l_Std_TreeSet_instUnion(
    mut v_00_u03b1_3970_: *mut crate::leanh::LeanObject,
    mut v_cmp_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_union as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3972_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3972_, 1, v_cmp_3971_);
    return v___x_3972_;
}
pub unsafe fn l_Std_TreeSet_inter___redArg(
    mut v_cmp_3973_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3974_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3976_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3973_,
        v_t_u2081_3974_,
        v_t_u2082_3975_,
    );
    return v___x_3976_;
}
pub unsafe fn l_Std_TreeSet_inter(
    mut v_00_u03b1_3977_: *mut crate::leanh::LeanObject,
    mut v_cmp_3978_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_3979_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(
        v_cmp_3978_,
        v_t_u2081_3979_,
        v_t_u2082_3980_,
    );
    return v___x_3981_;
}
pub unsafe fn l_Std_TreeSet_instInter___redArg(
    mut v_cmp_3982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3983_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_inter as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3983_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3983_, 1, v_cmp_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Std_TreeSet_instInter(
    mut v_00_u03b1_3984_: *mut crate::leanh::LeanObject,
    mut v_cmp_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3986_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_inter as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3986_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3986_, 1, v_cmp_3985_);
    return v___x_3986_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_cmp_3987_: *mut crate::leanh::LeanObject,
    mut v_t_3988_: *mut crate::leanh::LeanObject,
    mut v_k_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3988_) == 0 {
                    v_k_3990_ = crate::leanh::lean_ctor_get(v_t_3988_, 1);
                    crate::leanh::lean_inc(v_k_3990_);
                    v_v_3991_ = crate::leanh::lean_ctor_get(v_t_3988_, 2);
                    crate::leanh::lean_inc(v_v_3991_);
                    v_l_3992_ = crate::leanh::lean_ctor_get(v_t_3988_, 3);
                    crate::leanh::lean_inc(v_l_3992_);
                    v_r_3993_ = crate::leanh::lean_ctor_get(v_t_3988_, 4);
                    crate::leanh::lean_inc(v_r_3993_);
                    crate::leanh::lean_dec_ref_known(v_t_3988_, 5);
                    crate::leanh::lean_inc_ref(v_cmp_3987_);
                    crate::leanh::lean_inc(v_k_3989_);
                    v___x_3994_ = crate::leanh::lean_apply_2(v_cmp_3987_, v_k_3989_, v_k_3990_);
                    v___x_3995_ = (crate::leanh::lean_unbox(v___x_3994_) as u8);
                    match v___x_3995_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_3993_);
                            crate::leanh::lean_dec(v_v_3991_);
                            v_t_3988_ = v_l_3992_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_3993_);
                            crate::leanh::lean_dec(v_l_3992_);
                            crate::leanh::lean_dec(v_k_3989_);
                            crate::leanh::lean_dec_ref(v_cmp_3987_);
                            v___x_3997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3997_, 0, v_v_3991_);
                            return v___x_3997_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_3992_);
                            crate::leanh::lean_dec(v_v_3991_);
                            v_t_3988_ = v_r_3993_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3989_);
                    crate::leanh::lean_dec_ref(v_cmp_3987_);
                    v___x_3999_ = crate::leanh::lean_box(0);
                    return v___x_3999_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(
    mut v_x_4000_: *mut crate::leanh::LeanObject,
    mut v_x_4001_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4000_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4001_) == 0 {
            let mut v___x_4002_: u8 = 0;
            v___x_4002_ = 1;
            return v___x_4002_;
        } else {
            let mut v___x_4003_: u8 = 0;
            v___x_4003_ = 0;
            return v___x_4003_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4001_) == 0 {
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
    mut v_x_4006_: *mut crate::leanh::LeanObject,
    mut v_x_4007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4008_: u8 = 0;
    let mut v_r_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4008_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v_x_4006_, v_x_4007_);
    crate::leanh::lean_dec(v_x_4007_);
    crate::leanh::lean_dec(v_x_4006_);
    v_r_4009_ = crate::leanh::lean_box((v_res_4008_) as usize);
    return v_r_4009_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_cmp_4010_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4011_: *mut crate::leanh::LeanObject,
    mut v_init_4012_: *mut crate::leanh::LeanObject,
    mut v_x_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: u8 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut v_unused_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4013_) == 0 {
                    v_k_4014_ = crate::leanh::lean_ctor_get(v_x_4013_, 1);
                    crate::leanh::lean_inc(v_k_4014_);
                    v_v_4015_ = crate::leanh::lean_ctor_get(v_x_4013_, 2);
                    crate::leanh::lean_inc(v_v_4015_);
                    v_l_4016_ = crate::leanh::lean_ctor_get(v_x_4013_, 3);
                    crate::leanh::lean_inc(v_l_4016_);
                    v_r_4017_ = crate::leanh::lean_ctor_get(v_x_4013_, 4);
                    crate::leanh::lean_inc(v_r_4017_);
                    crate::leanh::lean_dec_ref_known(v_x_4013_, 5);
                    crate::leanh::lean_inc(v_t_u2082_4011_);
                    crate::leanh::lean_inc_ref(v_cmp_4010_);
                    v___x_4018_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_4010_, v_t_u2082_4011_, v_init_4012_, v_l_4016_);
                    if crate::leanh::lean_obj_tag(v___x_4018_) == 0 {
                        crate::leanh::lean_dec(v_r_4017_);
                        crate::leanh::lean_dec(v_v_4015_);
                        crate::leanh::lean_dec(v_k_4014_);
                        crate::leanh::lean_dec(v_t_u2082_4011_);
                        crate::leanh::lean_dec_ref(v_cmp_4010_);
                        return v___x_4018_;
                    } else {
                        v_isSharedCheck_4034_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4018_)) as u8;
                        if v_isSharedCheck_4034_ == 0 {
                            v_unused_4035_ = crate::leanh::lean_ctor_get(v___x_4018_, 0);
                            crate::leanh::lean_dec(v_unused_4035_);
                            v___x_4020_ = v___x_4018_;
                            v_isShared_4021_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4018_);
                            v___x_4020_ = crate::leanh::lean_box(0);
                            v_isShared_4021_ = v_isSharedCheck_4034_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_t_u2082_4011_);
                    crate::leanh::lean_dec_ref(v_cmp_4010_);
                    v___x_4036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4036_, 0, v_init_4012_);
                    return v___x_4036_;
                }
            }
            1 => {
                v___x_4022_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_t_u2082_4011_);
                crate::leanh::lean_inc_ref(v_cmp_4010_);
                v___x_4023_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_4010_, v_t_u2082_4011_, v_k_4014_);
                v___x_4024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4024_, 0, v_v_4015_);
                v___x_4025_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__3(v___x_4023_, v___x_4024_);
                crate::leanh::lean_dec_ref_known(v___x_4024_, 1);
                crate::leanh::lean_dec(v___x_4023_);
                if v___x_4025_ == 0 {
                    crate::leanh::lean_dec(v_r_4017_);
                    crate::leanh::lean_dec(v_t_u2082_4011_);
                    crate::leanh::lean_dec_ref(v_cmp_4010_);
                    v___x_4026_ = crate::leanh::lean_box((v___x_4025_) as usize);
                    v___x_4027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4027_, 0, v___x_4026_);
                    v___x_4028_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4028_, 0, v___x_4027_);
                    crate::leanh::lean_ctor_set(v___x_4028_, 1, v___x_4022_);
                    if v_isShared_4021_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4020_, 0);
                        crate::leanh::lean_ctor_set(v___x_4020_, 0, v___x_4028_);
                        v___x_4030_ = v___x_4020_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
                        v___x_4030_ = v_reuseFailAlloc_4031_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4020_);
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
    mut v_cmp_4037_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4038_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4039_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u8 = 0;
    let mut v_val_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: u8 = 0;
    let mut v___y_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_u2081_4038_) == 0 {
                    v_size_4057_ = crate::leanh::lean_ctor_get(v_t_u2081_4038_, 0);
                    crate::leanh::lean_inc(v_size_4057_);
                    v___y_4054_ = v_size_4057_;
                    state = 3;
                    continue;
                } else {
                    v___x_4058_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4054_ = v___x_4058_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_fst_4042_ = crate::leanh::lean_ctor_get(v___y_4041_, 0);
                crate::leanh::lean_inc(v_fst_4042_);
                crate::leanh::lean_dec_ref(v___y_4041_);
                if crate::leanh::lean_obj_tag(v_fst_4042_) == 0 {
                    v___x_4043_ = 1;
                    return v___x_4043_;
                } else {
                    v_val_4044_ = crate::leanh::lean_ctor_get(v_fst_4042_, 0);
                    crate::leanh::lean_inc(v_val_4044_);
                    crate::leanh::lean_dec_ref_known(v_fst_4042_, 1);
                    v___x_4045_ = (crate::leanh::lean_unbox(v_val_4044_) as u8);
                    crate::leanh::lean_dec(v_val_4044_);
                    return v___x_4045_;
                }
            }
            2 => {
                v___x_4049_ = lean_nat_dec_eq(v___y_4047_, v___y_4048_);
                crate::leanh::lean_dec(v___y_4048_);
                crate::leanh::lean_dec(v___y_4047_);
                if v___x_4049_ == 0 {
                    crate::leanh::lean_dec(v_t_u2082_4039_);
                    crate::leanh::lean_dec(v_t_u2081_4038_);
                    crate::leanh::lean_dec_ref(v_cmp_4037_);
                    return v___x_4049_;
                } else {
                    v___x_4050_ = l_Std_TreeSet_any___redArg___closed__0;
                    v___x_4051_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_4037_, v_t_u2082_4039_, v___x_4050_, v_t_u2081_4038_);
                    v_a_4052_ = crate::leanh::lean_ctor_get(v___x_4051_, 0);
                    crate::leanh::lean_inc(v_a_4052_);
                    crate::leanh::lean_dec_ref(v___x_4051_);
                    v___y_4041_ = v_a_4052_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_t_u2082_4039_) == 0 {
                    v_size_4055_ = crate::leanh::lean_ctor_get(v_t_u2082_4039_, 0);
                    crate::leanh::lean_inc(v_size_4055_);
                    v___y_4047_ = v___y_4054_;
                    v___y_4048_ = v_size_4055_;
                    state = 2;
                    continue;
                } else {
                    v___x_4056_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_cmp_4059_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4060_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4062_: u8 = 0;
    let mut v_r_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4059_, v_t_u2081_4060_, v_t_u2082_4061_);
    v_r_4063_ = crate::leanh::lean_box((v_res_4062_) as usize);
    return v_r_4063_;
}
pub unsafe fn l_Std_TreeSet_beq___redArg(
    mut v_cmp_4064_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4065_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4066_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4067_: u8 = 0;
    v___x_4067_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4064_, v_t_u2081_4065_, v_t_u2082_4066_);
    return v___x_4067_;
}
pub unsafe fn l_Std_TreeSet_beq___redArg___boxed(
    mut v_cmp_4068_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4069_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4071_: u8 = 0;
    let mut v_r_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Std_TreeSet_beq___redArg(v_cmp_4068_, v_t_u2081_4069_, v_t_u2082_4070_);
    v_r_4072_ = crate::leanh::lean_box((v_res_4071_) as usize);
    return v_r_4072_;
}
pub unsafe fn l_Std_TreeSet_beq(
    mut v_00_u03b1_4073_: *mut crate::leanh::LeanObject,
    mut v_cmp_4074_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4075_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4076_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4077_: u8 = 0;
    v___x_4077_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4074_, v_t_u2081_4075_, v_t_u2082_4076_);
    return v___x_4077_;
}
pub unsafe fn l_Std_TreeSet_beq___boxed(
    mut v_00_u03b1_4078_: *mut crate::leanh::LeanObject,
    mut v_cmp_4079_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4080_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4082_: u8 = 0;
    let mut v_r_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4082_ = l_Std_TreeSet_beq(
        v_00_u03b1_4078_,
        v_cmp_4079_,
        v_t_u2081_4080_,
        v_t_u2082_4081_,
    );
    v_r_4083_ = crate::leanh::lean_box((v_res_4082_) as usize);
    return v_r_4083_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(
    mut v_cmp_4084_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4085_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4086_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4087_: u8 = 0;
    v___x_4087_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4084_, v_t_u2081_4085_, v_t_u2082_4086_);
    return v___x_4087_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg___boxed(
    mut v_cmp_4088_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4089_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4091_: u8 = 0;
    let mut v_r_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___redArg(
        v_cmp_4088_,
        v_t_u2081_4089_,
        v_t_u2082_4090_,
    );
    v_r_4092_ = crate::leanh::lean_box((v_res_4091_) as usize);
    return v_r_4092_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(
    mut v_00_u03b1_4093_: *mut crate::leanh::LeanObject,
    mut v_cmp_4094_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4095_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4096_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4097_: u8 = 0;
    v___x_4097_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4094_, v_t_u2081_4095_, v_t_u2082_4096_);
    return v___x_4097_;
}
pub unsafe fn l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0___boxed(
    mut v_00_u03b1_4098_: *mut crate::leanh::LeanObject,
    mut v_cmp_4099_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4100_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4102_: u8 = 0;
    let mut v_r_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4102_ = l_Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0(
        v_00_u03b1_4098_,
        v_cmp_4099_,
        v_t_u2081_4100_,
        v_t_u2082_4101_,
    );
    v_r_4103_ = crate::leanh::lean_box((v_res_4102_) as usize);
    return v_r_4103_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(
    mut v_cmp_4104_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4105_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4106_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4107_: u8 = 0;
    v___x_4107_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4104_, v_t_u2081_4105_, v_t_u2082_4106_);
    return v___x_4107_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg___boxed(
    mut v_cmp_4108_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4109_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4111_: u8 = 0;
    let mut v_r_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4111_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___redArg(v_cmp_4108_, v_t_u2081_4109_, v_t_u2082_4110_);
    v_r_4112_ = crate::leanh::lean_box((v_res_4111_) as usize);
    return v_r_4112_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(
    mut v_00_u03b1_4113_: *mut crate::leanh::LeanObject,
    mut v_cmp_4114_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4115_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4116_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4117_: u8 = 0;
    v___x_4117_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4114_, v_t_u2081_4115_, v_t_u2082_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0___boxed(
    mut v_00_u03b1_4118_: *mut crate::leanh::LeanObject,
    mut v_cmp_4119_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4120_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4122_: u8 = 0;
    let mut v_r_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4122_ =
        l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0(
            v_00_u03b1_4118_,
            v_cmp_4119_,
            v_t_u2081_4120_,
            v_t_u2082_4121_,
        );
    v_r_4123_ = crate::leanh::lean_box((v_res_4122_) as usize);
    return v_r_4123_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4124_: *mut crate::leanh::LeanObject,
    mut v_cmp_4125_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4126_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4127_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4128_: u8 = 0;
    v___x_4128_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___redArg(v_cmp_4125_, v_t_u2081_4126_, v_t_u2082_4127_);
    return v___x_4128_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4129_: *mut crate::leanh::LeanObject,
    mut v_cmp_4130_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4131_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4133_: u8 = 0;
    let mut v_r_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1(v_00_u03b1_4129_, v_cmp_4130_, v_t_u2081_4131_, v_t_u2082_4132_);
    v_r_4134_ = crate::leanh::lean_box((v_res_4133_) as usize);
    return v_r_4134_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4135_: *mut crate::leanh::LeanObject,
    mut v_cmp_4136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4137_: *mut crate::leanh::LeanObject,
    mut v_t_4138_: *mut crate::leanh::LeanObject,
    mut v_k_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_4136_, v_t_4138_, v_k_4139_);
    return v___x_4140_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_4141_: *mut crate::leanh::LeanObject,
    mut v_cmp_4142_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4143_: *mut crate::leanh::LeanObject,
    mut v_init_4144_: *mut crate::leanh::LeanObject,
    mut v_x_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Std_TreeSet_beq_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_4142_, v_t_u2082_4143_, v_init_4144_, v_x_4145_);
    return v___x_4146_;
}
pub unsafe fn l_Std_TreeSet_instBEq___redArg(
    mut v_cmp_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4148_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_beq___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_4148_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4148_, 1, v_cmp_4147_);
    return v___x_4148_;
}
pub unsafe fn l_Std_TreeSet_instBEq(
    mut v_00_u03b1_4149_: *mut crate::leanh::LeanObject,
    mut v_cmp_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4151_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_beq___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_4151_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4151_, 1, v_cmp_4150_);
    return v___x_4151_;
}
pub unsafe fn l_Std_TreeSet_diff___redArg(
    mut v_cmp_4152_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4153_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4155_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_4152_,
        v_t_u2081_4153_,
        v_t_u2082_4154_,
    );
    return v___x_4155_;
}
pub unsafe fn l_Std_TreeSet_diff(
    mut v_00_u03b1_4156_: *mut crate::leanh::LeanObject,
    mut v_cmp_4157_: *mut crate::leanh::LeanObject,
    mut v_t_u2081_4158_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Std_DTreeMap_Internal_Impl_diff___at___00Std_DTreeMap_diff_spec__0___redArg(
        v_cmp_4157_,
        v_t_u2081_4158_,
        v_t_u2082_4159_,
    );
    return v___x_4160_;
}
pub unsafe fn l_Std_TreeSet_instSDiff___redArg(
    mut v_cmp_4161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4162_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_diff as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_4162_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4162_, 1, v_cmp_4161_);
    return v___x_4162_;
}
pub unsafe fn l_Std_TreeSet_instSDiff(
    mut v_00_u03b1_4163_: *mut crate::leanh::LeanObject,
    mut v_cmp_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ =
        crate::leanh::lean_alloc_closure(l_Std_TreeSet_diff as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_4165_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4165_, 1, v_cmp_4164_);
    return v___x_4165_;
}
pub unsafe fn l_Std_TreeSet_eraseMany___redArg___lam__0(
    mut v_cmp_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_____s_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4169_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v_cmp_4166_, v_a_4167_, v_____s_4168_);
    v___x_4170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4170_, 0, v_r_4169_);
    return v___x_4170_;
}
pub unsafe fn l_Std_TreeSet_eraseMany___redArg(
    mut v_cmp_4171_: *mut crate::leanh::LeanObject,
    mut v_inst_4172_: *mut crate::leanh::LeanObject,
    mut v_t_4173_: *mut crate::leanh::LeanObject,
    mut v_l_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4175_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4175_, 0, v_cmp_4171_);
    v___x_4176_ = crate::leanh::lean_apply_4(
        v_inst_4172_,
        crate::leanh::lean_box(0),
        v_l_4174_,
        v_t_4173_,
        v___f_4175_,
    );
    return v___x_4176_;
}
pub unsafe fn l_Std_TreeSet_eraseMany(
    mut v_00_u03b1_4177_: *mut crate::leanh::LeanObject,
    mut v_cmp_4178_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4179_: *mut crate::leanh::LeanObject,
    mut v_inst_4180_: *mut crate::leanh::LeanObject,
    mut v_t_4181_: *mut crate::leanh::LeanObject,
    mut v_l_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4183_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_eraseMany___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4183_, 0, v_cmp_4178_);
    v___x_4184_ = crate::leanh::lean_apply_4(
        v_inst_4180_,
        crate::leanh::lean_box(0),
        v_l_4182_,
        v_t_4181_,
        v___f_4183_,
    );
    return v___x_4184_;
}
pub unsafe fn l_Std_TreeSet_instRepr___redArg___lam__1(
    mut v___f_4188_: *mut crate::leanh::LeanObject,
    mut v_inst_4189_: *mut crate::leanh::LeanObject,
    mut v_m_4190_: *mut crate::leanh::LeanObject,
    mut v_prec_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4192_ = l_Std_TreeSet_instRepr___redArg___lam__1___closed__1;
    v___x_4193_ = crate::leanh::lean_box(0);
    v___x_4194_ = l_Std_TreeSet_foldr___redArg___closed__9;
    v___x_4195_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_4194_,
        v___f_4188_,
        v___x_4193_,
        v_m_4190_,
    );
    v___x_4196_ = l_List_repr___redArg(v_inst_4189_, v___x_4195_);
    v___x_4197_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4197_, 0, v___x_4192_);
    crate::leanh::lean_ctor_set(v___x_4197_, 1, v___x_4196_);
    v___x_4198_ = l_Repr_addAppParen(v___x_4197_, v_prec_4191_);
    return v___x_4198_;
}
pub unsafe fn l_Std_TreeSet_instRepr___redArg___lam__1___boxed(
    mut v___f_4199_: *mut crate::leanh::LeanObject,
    mut v_inst_4200_: *mut crate::leanh::LeanObject,
    mut v_m_4201_: *mut crate::leanh::LeanObject,
    mut v_prec_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4203_ = l_Std_TreeSet_instRepr___redArg___lam__1(
        v___f_4199_,
        v_inst_4200_,
        v_m_4201_,
        v_prec_4202_,
    );
    crate::leanh::lean_dec(v_prec_4202_);
    return v_res_4203_;
}
pub unsafe fn l_Std_TreeSet_instRepr___redArg(
    mut v_inst_4204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4205_ = l_Std_TreeSet_toList___redArg___closed__0;
    v___f_4206_ = crate::leanh::lean_alloc_closure(
        l_Std_TreeSet_instRepr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4206_, 0, v___f_4205_);
    crate::leanh::lean_closure_set(v___f_4206_, 1, v_inst_4204_);
    return v___f_4206_;
}
pub unsafe fn l_Std_TreeSet_instRepr(
    mut v_00_u03b1_4207_: *mut crate::leanh::LeanObject,
    mut v_cmp_4208_: *mut crate::leanh::LeanObject,
    mut v_inst_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = l_Std_TreeSet_instRepr___redArg(v_inst_4209_);
    return v___x_4210_;
}
pub unsafe fn l_Std_TreeSet_instRepr___boxed(
    mut v_00_u03b1_4211_: *mut crate::leanh::LeanObject,
    mut v_cmp_4212_: *mut crate::leanh::LeanObject,
    mut v_inst_4213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4214_ = l_Std_TreeSet_instRepr(v_00_u03b1_4211_, v_cmp_4212_, v_inst_4213_);
    crate::leanh::lean_dec_ref(v_cmp_4212_);
    return v_res_4214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeSet___auto__1 = _init_l_Std_TreeSet___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet___auto__1);
    l_Std_TreeSet_ofList___auto__1 = _init_l_Std_TreeSet_ofList___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_ofList___auto__1);
    l_Std_TreeSet_ofArray___auto__1 = _init_l_Std_TreeSet_ofArray___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_ofArray___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Basic(builtin);
}
