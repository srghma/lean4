// Lean compiler output
// Module: Std.Data.DHashMap.Raw
// Imports: Init.Data.LawfulHashable Std.Data.DHashMap.Internal.Defs Std.Data.DHashMap.Internal.Defs
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0,
};
use crate::r#gen::Init::Data::LawfulHashable::{
    initialize_Init_Data_LawfulHashable, runtime_initialize_Init_Data_LawfulHashable,
};
use crate::r#gen::Init::Data::List::Control::l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::Repr::{
    l_List_repr___redArg, l_Repr_addAppParen, l_Sigma_repr___boxed,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go,
    l_Std_DHashMap_Internal_AssocList_contains___redArg,
    l_Std_DHashMap_Internal_AssocList_foldlM___redArg,
    l_Std_DHashMap_Internal_AssocList_foldrM___redArg,
    l_Std_DHashMap_Internal_AssocList_get_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_replace___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    initialize_Std_Data_DHashMap_Internal_Defs,
    l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_beq___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_erase___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_expand___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_inter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_map___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_modify___redArg,
    runtime_initialize_Std_Data_DHashMap_Internal_Defs,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{lean_usize_of_nat, lean_usize_sub};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [68, 72, 97, 115, 104, 77, 97, 112, 0],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__3_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            18035583711357664763 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            4155810031736705028 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            14381247710261688386 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__9_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__13_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DHashMap_Raw_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [82, 97, 119, 46, 69, 113, 117, 105, 118, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value) as *mut crate::leanh::LeanObject,3422484220311391684 as *mut crate::leanh::LeanObject] };
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject,16179887037867133675 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,18035583711357664763 as *mut crate::leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value) as *mut crate::leanh::LeanObject,4155810031736705028 as *mut crate::leanh::LeanObject] };
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject,8373056252130840875 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1: u8 =
    0;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_toArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_keysArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keysArray___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_keysArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keysArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_union___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_union___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_union___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_values___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_values___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_values___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_values___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_values___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_values___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_values___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_values___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_values___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_valuesArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_valuesArray___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_valuesArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toList___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_toList___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_toList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_toList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_Const_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Const_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toList___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_Const_toList___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_toList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 82, 97, 119, 46, 111, 102, 76,
        105, 115, 116, 32, 0,
    ],
};
static mut l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keys___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DHashMap_Raw_keys___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keys___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keys___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DHashMap_Raw_values___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_keys___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_keys___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keys___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_ofList___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_ofList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_ofList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Raw_ofList___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_ofList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_ofList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_ofList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity___redArg(
    mut v_capacity_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2642_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2643_ = lean_nat_mul(v_capacity_2640_, v___x_2642_);
    v___x_2644_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2645_ = lean_nat_div(v___x_2643_, v___x_2644_);
    crate::leanh::lean_dec(v___x_2643_);
    v___x_2646_ = l_Nat_nextPowerOfTwo(v___x_2645_);
    crate::leanh::lean_dec(v___x_2645_);
    v___x_2647_ = crate::leanh::lean_box(0);
    v___x_2648_ = lean_mk_array(v___x_2646_, v___x_2647_);
    v___x_2649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2649_, 0, v___x_2641_);
    crate::leanh::lean_ctor_set(v___x_2649_, 1, v___x_2648_);
    return v___x_2649_;
}
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity___redArg___boxed(
    mut v_capacity_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Std_DHashMap_Raw_emptyWithCapacity___redArg(v_capacity_2650_);
    crate::leanh::lean_dec(v_capacity_2650_);
    return v_res_2651_;
}
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity(
    mut v_00_u03b1_2652_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2653_: *mut crate::leanh::LeanObject,
    mut v_capacity_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2656_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2657_ = lean_nat_mul(v_capacity_2654_, v___x_2656_);
    v___x_2658_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2659_ = lean_nat_div(v___x_2657_, v___x_2658_);
    crate::leanh::lean_dec(v___x_2657_);
    v___x_2660_ = l_Nat_nextPowerOfTwo(v___x_2659_);
    crate::leanh::lean_dec(v___x_2659_);
    v___x_2661_ = crate::leanh::lean_box(0);
    v___x_2662_ = lean_mk_array(v___x_2660_, v___x_2661_);
    v___x_2663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2655_);
    crate::leanh::lean_ctor_set(v___x_2663_, 1, v___x_2662_);
    return v___x_2663_;
}
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity___boxed(
    mut v_00_u03b1_2664_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2665_: *mut crate::leanh::LeanObject,
    mut v_capacity_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2667_ =
        l_Std_DHashMap_Raw_emptyWithCapacity(v_00_u03b1_2664_, v_00_u03b2_2665_, v_capacity_2666_);
    crate::leanh::lean_dec(v_capacity_2666_);
    return v_res_2667_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = crate::leanh::lean_box(0);
    v___x_2669_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2670_ = lean_mk_array(v___x_2669_, v___x_2668_);
    return v___x_2670_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2672_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2673_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2673_, 0, v___x_2672_);
    crate::leanh::lean_ctor_set(v___x_2673_, 1, v___x_2671_);
    return v___x_2673_;
}
pub unsafe fn l_Std_DHashMap_Raw_instEmptyCollection(
    mut v_00_u03b1_2674_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2676_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInhabited(
    mut v_00_u03b1_2677_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2679_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2679_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5;
    v___x_2721_ = l_String_toRawSubstring_x27(v___x_2720_);
    return v___x_2721_;
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(
    mut v_x_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: u8 = 0;
    v___x_2748_ = l_Std_DHashMap_Raw_term___x7em___00__closed__4;
    crate::leanh::lean_inc(v_x_2745_);
    v___x_2749_ = l_Lean_Syntax_isOfKind(v_x_2745_, v___x_2748_);
    if v___x_2749_ == 0 {
        let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2745_);
        v___x_2750_ = crate::leanh::lean_box(1);
        v___x_2751_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2751_, 0, v___x_2750_);
        crate::leanh::lean_ctor_set(v___x_2751_, 1, v_a_2747_);
        return v___x_2751_;
    } else {
        let mut v_quotContext_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2759_: u8 = 0;
        let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2752_ = crate::leanh::lean_ctor_get(v_a_2746_, 1);
        v_currMacroScope_2753_ = crate::leanh::lean_ctor_get(v_a_2746_, 2);
        v_ref_2754_ = crate::leanh::lean_ctor_get(v_a_2746_, 5);
        v___x_2755_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2756_ = l_Lean_Syntax_getArg(v_x_2745_, v___x_2755_);
        v___x_2757_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2758_ = l_Lean_Syntax_getArg(v_x_2745_, v___x_2757_);
        crate::leanh::lean_dec(v_x_2745_);
        v___x_2759_ = 0;
        v___x_2760_ = l_Lean_SourceInfo_fromRef(v_ref_2754_, v___x_2759_);
        v___x_2761_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4;
        v___x_2762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once), _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
        v___x_2763_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8;
        crate::leanh::lean_inc(v_currMacroScope_2753_);
        crate::leanh::lean_inc(v_quotContext_2752_);
        v___x_2764_ =
            l_Lean_addMacroScope(v_quotContext_2752_, v___x_2763_, v_currMacroScope_2753_);
        v___x_2765_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13;
        crate::leanh::lean_inc_n(v___x_2760_, 2);
        v___x_2766_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2766_, 0, v___x_2760_);
        crate::leanh::lean_ctor_set(v___x_2766_, 1, v___x_2762_);
        crate::leanh::lean_ctor_set(v___x_2766_, 2, v___x_2764_);
        crate::leanh::lean_ctor_set(v___x_2766_, 3, v___x_2765_);
        v___x_2767_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15;
        v___x_2768_ = l_Lean_Syntax_node2(v___x_2760_, v___x_2767_, v___x_2756_, v___x_2758_);
        v___x_2769_ = l_Lean_Syntax_node2(v___x_2760_, v___x_2761_, v___x_2766_, v___x_2768_);
        v___x_2770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2770_, 0, v___x_2769_);
        crate::leanh::lean_ctor_set(v___x_2770_, 1, v_a_2747_);
        return v___x_2770_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(
    mut v_x_2771_: *mut crate::leanh::LeanObject,
    mut v_a_2772_: *mut crate::leanh::LeanObject,
    mut v_a_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(v_x_2771_, v_a_2772_, v_a_2773_);
    crate::leanh::lean_dec_ref(v_a_2772_);
    return v_res_2774_;
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(
    mut v_x_2778_: *mut crate::leanh::LeanObject,
    mut v_a_2779_: *mut crate::leanh::LeanObject,
    mut v_a_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: u8 = 0;
    v___x_2781_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4;
    crate::leanh::lean_inc(v_x_2778_);
    v___x_2782_ = l_Lean_Syntax_isOfKind(v_x_2778_, v___x_2781_);
    if v___x_2782_ == 0 {
        let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2778_);
        v___x_2783_ = crate::leanh::lean_box(0);
        v___x_2784_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2784_, 0, v___x_2783_);
        crate::leanh::lean_ctor_set(v___x_2784_, 1, v_a_2780_);
        return v___x_2784_;
    } else {
        let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2788_: u8 = 0;
        v___x_2785_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2786_ = l_Lean_Syntax_getArg(v_x_2778_, v___x_2785_);
        v___x_2787_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_2786_);
        v___x_2788_ = l_Lean_Syntax_isOfKind(v___x_2786_, v___x_2787_);
        if v___x_2788_ == 0 {
            let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2786_);
            crate::leanh::lean_dec(v_x_2778_);
            v___x_2789_ = crate::leanh::lean_box(0);
            v___x_2790_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2790_, 0, v___x_2789_);
            crate::leanh::lean_ctor_set(v___x_2790_, 1, v_a_2780_);
            return v___x_2790_;
        } else {
            let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2794_: u8 = 0;
            v___x_2791_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2792_ = l_Lean_Syntax_getArg(v_x_2778_, v___x_2791_);
            crate::leanh::lean_dec(v_x_2778_);
            v___x_2793_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_2792_);
            v___x_2794_ = l_Lean_Syntax_matchesNull(v___x_2792_, v___x_2793_);
            if v___x_2794_ == 0 {
                let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2792_);
                crate::leanh::lean_dec(v___x_2786_);
                v___x_2795_ = crate::leanh::lean_box(0);
                v___x_2796_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                crate::leanh::lean_ctor_set(v___x_2796_, 1, v_a_2780_);
                return v___x_2796_;
            } else {
                let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2800_: u8 = 0;
                let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2797_ = l_Lean_Syntax_getArg(v___x_2792_, v___x_2785_);
                v___x_2798_ = l_Lean_Syntax_getArg(v___x_2792_, v___x_2791_);
                crate::leanh::lean_dec(v___x_2792_);
                v_ref_2799_ = l_Lean_replaceRef(v___x_2786_, v_a_2779_);
                crate::leanh::lean_dec(v___x_2786_);
                v___x_2800_ = 0;
                v___x_2801_ = l_Lean_SourceInfo_fromRef(v_ref_2799_, v___x_2800_);
                crate::leanh::lean_dec(v_ref_2799_);
                v___x_2802_ = l_Std_DHashMap_Raw_term___x7em___00__closed__4;
                v___x_2803_ = l_Std_DHashMap_Raw_term___x7em___00__closed__7;
                crate::leanh::lean_inc(v___x_2801_);
                v___x_2804_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2804_, 0, v___x_2801_);
                crate::leanh::lean_ctor_set(v___x_2804_, 1, v___x_2803_);
                v___x_2805_ = l_Lean_Syntax_node3(
                    v___x_2801_,
                    v___x_2802_,
                    v___x_2797_,
                    v___x_2804_,
                    v___x_2798_,
                );
                v___x_2806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2806_, 0, v___x_2805_);
                crate::leanh::lean_ctor_set(v___x_2806_, 1, v_a_2780_);
                return v___x_2806_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(
    mut v_x_2807_: *mut crate::leanh::LeanObject,
    mut v_a_2808_: *mut crate::leanh::LeanObject,
    mut v_a_2809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_2807_, v_a_2808_, v_a_2809_);
    crate::leanh::lean_dec(v_a_2808_);
    return v_res_2810_;
}
pub unsafe fn l_Std_DHashMap_Raw_insert___redArg(
    mut v_inst_2811_: *mut crate::leanh::LeanObject,
    mut v_inst_2812_: *mut crate::leanh::LeanObject,
    mut v_m_2813_: *mut crate::leanh::LeanObject,
    mut v_a_2814_: *mut crate::leanh::LeanObject,
    mut v_b_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    v_buckets_2816_ = crate::leanh::lean_ctor_get(v_m_2813_, 1);
    v___x_2817_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2818_ = lean_array_get_size(v_buckets_2816_);
    v___x_2819_ = lean_nat_dec_lt(v___x_2817_, v___x_2818_);
    if v___x_2819_ == 0 {
        crate::leanh::lean_dec(v_b_2815_);
        crate::leanh::lean_dec(v_a_2814_);
        crate::leanh::lean_dec_ref(v_inst_2812_);
        crate::leanh::lean_dec_ref(v_inst_2811_);
        return v_m_2813_;
    } else {
        let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2820_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_2811_,
            v_inst_2812_,
            v_m_2813_,
            v_a_2814_,
            v_b_2815_,
        );
        return v___x_2820_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_insert(
    mut v_00_u03b1_2821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2822_: *mut crate::leanh::LeanObject,
    mut v_inst_2823_: *mut crate::leanh::LeanObject,
    mut v_inst_2824_: *mut crate::leanh::LeanObject,
    mut v_m_2825_: *mut crate::leanh::LeanObject,
    mut v_a_2826_: *mut crate::leanh::LeanObject,
    mut v_b_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v_buckets_2828_ = crate::leanh::lean_ctor_get(v_m_2825_, 1);
    v___x_2829_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2830_ = lean_array_get_size(v_buckets_2828_);
    v___x_2831_ = lean_nat_dec_lt(v___x_2829_, v___x_2830_);
    if v___x_2831_ == 0 {
        crate::leanh::lean_dec(v_b_2827_);
        crate::leanh::lean_dec(v_a_2826_);
        crate::leanh::lean_dec_ref(v_inst_2824_);
        crate::leanh::lean_dec_ref(v_inst_2823_);
        return v_m_2825_;
    } else {
        let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2832_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_2823_,
            v_inst_2824_,
            v_m_2825_,
            v_a_2826_,
            v_b_2827_,
        );
        return v___x_2832_;
    }
}
pub unsafe fn _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2833_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2834_ = lean_array_get_size(v___x_2833_);
    return v___x_2834_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1()
-> u8 {
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    v___x_2835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0,
    );
    v___x_2836_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2837_ = lean_nat_dec_lt(v___x_2836_, v___x_2835_);
    return v___x_2837_;
}
pub unsafe fn l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2838_: *mut crate::leanh::LeanObject,
    mut v_inst_2839_: *mut crate::leanh::LeanObject,
    mut v_x_2840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u8 = 0;
    v_fst_2841_ = crate::leanh::lean_ctor_get(v_x_2840_, 0);
    crate::leanh::lean_inc(v_fst_2841_);
    v_snd_2842_ = crate::leanh::lean_ctor_get(v_x_2840_, 1);
    crate::leanh::lean_inc(v_snd_2842_);
    crate::leanh::lean_dec_ref(v_x_2840_);
    v___x_2843_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_2844_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2844_ == 0 {
        crate::leanh::lean_dec(v_snd_2842_);
        crate::leanh::lean_dec(v_fst_2841_);
        crate::leanh::lean_dec_ref(v_inst_2839_);
        crate::leanh::lean_dec_ref(v_inst_2838_);
        return v___x_2843_;
    } else {
        let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_2838_,
            v_inst_2839_,
            v___x_2843_,
            v_fst_2841_,
            v_snd_2842_,
        );
        return v___x_2845_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(
    mut v_inst_2846_: *mut crate::leanh::LeanObject,
    mut v_inst_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2848_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2848_, 0, v_inst_2846_);
    crate::leanh::lean_closure_set(v___f_2848_, 1, v_inst_2847_);
    return v___f_2848_;
}
pub unsafe fn l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(
    mut v_00_u03b1_2849_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2850_: *mut crate::leanh::LeanObject,
    mut v_inst_2851_: *mut crate::leanh::LeanObject,
    mut v_inst_2852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2853_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2853_, 0, v_inst_2851_);
    crate::leanh::lean_closure_set(v___f_2853_, 1, v_inst_2852_);
    return v___f_2853_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2854_: *mut crate::leanh::LeanObject,
    mut v_inst_2855_: *mut crate::leanh::LeanObject,
    mut v_x_2856_: *mut crate::leanh::LeanObject,
    mut v_s_2857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    v_fst_2858_ = crate::leanh::lean_ctor_get(v_x_2856_, 0);
    crate::leanh::lean_inc(v_fst_2858_);
    v_snd_2859_ = crate::leanh::lean_ctor_get(v_x_2856_, 1);
    crate::leanh::lean_inc(v_snd_2859_);
    crate::leanh::lean_dec_ref(v_x_2856_);
    v_buckets_2860_ = crate::leanh::lean_ctor_get(v_s_2857_, 1);
    v___x_2861_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2862_ = lean_array_get_size(v_buckets_2860_);
    v___x_2863_ = lean_nat_dec_lt(v___x_2861_, v___x_2862_);
    if v___x_2863_ == 0 {
        crate::leanh::lean_dec(v_snd_2859_);
        crate::leanh::lean_dec(v_fst_2858_);
        crate::leanh::lean_dec_ref(v_inst_2855_);
        crate::leanh::lean_dec_ref(v_inst_2854_);
        return v_s_2857_;
    } else {
        let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2864_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_2854_,
            v_inst_2855_,
            v_s_2857_,
            v_fst_2858_,
            v_snd_2859_,
        );
        return v___x_2864_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(
    mut v_inst_2865_: *mut crate::leanh::LeanObject,
    mut v_inst_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2867_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2867_, 0, v_inst_2865_);
    crate::leanh::lean_closure_set(v___f_2867_, 1, v_inst_2866_);
    return v___f_2867_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(
    mut v_00_u03b1_2868_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2869_: *mut crate::leanh::LeanObject,
    mut v_inst_2870_: *mut crate::leanh::LeanObject,
    mut v_inst_2871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2872_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2872_, 0, v_inst_2870_);
    crate::leanh::lean_closure_set(v___f_2872_, 1, v_inst_2871_);
    return v___f_2872_;
}
pub unsafe fn l_Std_DHashMap_Raw_insertIfNew___redArg(
    mut v_inst_2873_: *mut crate::leanh::LeanObject,
    mut v_inst_2874_: *mut crate::leanh::LeanObject,
    mut v_m_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
    mut v_b_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    v_buckets_2878_ = crate::leanh::lean_ctor_get(v_m_2875_, 1);
    v___x_2879_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2880_ = lean_array_get_size(v_buckets_2878_);
    v___x_2881_ = lean_nat_dec_lt(v___x_2879_, v___x_2880_);
    if v___x_2881_ == 0 {
        crate::leanh::lean_dec(v_b_2877_);
        crate::leanh::lean_dec(v_a_2876_);
        crate::leanh::lean_dec_ref(v_inst_2874_);
        crate::leanh::lean_dec_ref(v_inst_2873_);
        return v_m_2875_;
    } else {
        let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2882_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_2873_,
            v_inst_2874_,
            v_m_2875_,
            v_a_2876_,
            v_b_2877_,
        );
        return v___x_2882_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_insertIfNew(
    mut v_00_u03b1_2883_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2884_: *mut crate::leanh::LeanObject,
    mut v_inst_2885_: *mut crate::leanh::LeanObject,
    mut v_inst_2886_: *mut crate::leanh::LeanObject,
    mut v_m_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
    mut v_b_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    v_buckets_2890_ = crate::leanh::lean_ctor_get(v_m_2887_, 1);
    v___x_2891_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2892_ = lean_array_get_size(v_buckets_2890_);
    v___x_2893_ = lean_nat_dec_lt(v___x_2891_, v___x_2892_);
    if v___x_2893_ == 0 {
        crate::leanh::lean_dec(v_b_2889_);
        crate::leanh::lean_dec(v_a_2888_);
        crate::leanh::lean_dec_ref(v_inst_2886_);
        crate::leanh::lean_dec_ref(v_inst_2885_);
        return v_m_2887_;
    } else {
        let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2894_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_2885_,
            v_inst_2886_,
            v_m_2887_,
            v_a_2888_,
            v_b_2889_,
        );
        return v___x_2894_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_containsThenInsert___redArg(
    mut v_inst_2895_: *mut crate::leanh::LeanObject,
    mut v_inst_2896_: *mut crate::leanh::LeanObject,
    mut v_m_2897_: *mut crate::leanh::LeanObject,
    mut v_a_2898_: *mut crate::leanh::LeanObject,
    mut v_b_2899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u64 = 0;
    let mut v___x_2912_: u64 = 0;
    let mut v___x_2913_: u64 = 0;
    let mut v___x_2914_: u64 = 0;
    let mut v_fold_2915_: u64 = 0;
    let mut v___x_2916_: u64 = 0;
    let mut v___x_2917_: u64 = 0;
    let mut v___x_2918_: u64 = 0;
    let mut v___x_2919_: usize = 0;
    let mut v___x_2920_: usize = 0;
    let mut v___x_2921_: usize = 0;
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: usize = 0;
    let mut v_bkt_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: u8 = 0;
    let mut v_val_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_unused_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2900_ = crate::leanh::lean_ctor_get(v_m_2897_, 0);
                v_buckets_2901_ = crate::leanh::lean_ctor_get(v_m_2897_, 1);
                v___x_2902_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2903_ = lean_array_get_size(v_buckets_2901_);
                v___x_2904_ = lean_nat_dec_lt(v___x_2902_, v___x_2903_);
                if v___x_2904_ == 0 {
                    crate::leanh::lean_dec(v_b_2899_);
                    crate::leanh::lean_dec(v_a_2898_);
                    crate::leanh::lean_dec_ref(v_inst_2896_);
                    crate::leanh::lean_dec_ref(v_inst_2895_);
                    v___x_2905_ = crate::leanh::lean_box((v___x_2904_) as usize);
                    v___x_2906_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2906_, 0, v___x_2905_);
                    crate::leanh::lean_ctor_set(v___x_2906_, 1, v_m_2897_);
                    return v___x_2906_;
                } else {
                    crate::leanh::lean_inc_ref(v_buckets_2901_);
                    crate::leanh::lean_inc(v_size_2900_);
                    v_isSharedCheck_2956_ = (!crate::leanh::lean_is_exclusive(v_m_2897_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v_unused_2957_ = crate::leanh::lean_ctor_get(v_m_2897_, 1);
                        crate::leanh::lean_dec(v_unused_2957_);
                        v_unused_2958_ = crate::leanh::lean_ctor_get(v_m_2897_, 0);
                        crate::leanh::lean_dec(v_unused_2958_);
                        v___x_2908_ = v_m_2897_;
                        v_isShared_2909_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2897_);
                        v___x_2908_ = crate::leanh::lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_2896_);
                crate::leanh::lean_inc_n(v_a_2898_, 2);
                v___x_2910_ = crate::leanh::lean_apply_1(v_inst_2896_, v_a_2898_);
                v___x_2911_ = 32u64;
                v___x_2912_ = crate::leanh::lean_unbox_uint64(v___x_2910_);
                v___x_2913_ = lean_uint64_shift_right(v___x_2912_, v___x_2911_);
                v___x_2914_ = crate::leanh::lean_unbox_uint64(v___x_2910_);
                crate::leanh::lean_dec_ref(v___x_2910_);
                v_fold_2915_ = lean_uint64_xor(v___x_2914_, v___x_2913_);
                v___x_2916_ = 16u64;
                v___x_2917_ = lean_uint64_shift_right(v_fold_2915_, v___x_2916_);
                v___x_2918_ = lean_uint64_xor(v_fold_2915_, v___x_2917_);
                v___x_2919_ = lean_uint64_to_usize(v___x_2918_);
                v___x_2920_ = lean_usize_of_nat(v___x_2903_);
                v___x_2921_ = 1usize;
                v___x_2922_ = lean_usize_sub(v___x_2920_, v___x_2921_);
                v___x_2923_ = lean_usize_land(v___x_2919_, v___x_2922_);
                v_bkt_2924_ = lean_array_uget_borrowed(v_buckets_2901_, v___x_2923_);
                crate::leanh::lean_inc(v_bkt_2924_);
                crate::leanh::lean_inc_ref(v_inst_2895_);
                v___x_2925_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2895_,
                    v_a_2898_,
                    v_bkt_2924_,
                );
                if v___x_2925_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2895_);
                    v___x_2926_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2927_ = lean_nat_add(v_size_2900_, v___x_2926_);
                    crate::leanh::lean_dec(v_size_2900_);
                    crate::leanh::lean_inc(v_bkt_2924_);
                    v___x_2928_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2928_, 0, v_a_2898_);
                    crate::leanh::lean_ctor_set(v___x_2928_, 1, v_b_2899_);
                    crate::leanh::lean_ctor_set(v___x_2928_, 2, v_bkt_2924_);
                    v_buckets_x27_2929_ =
                        lean_array_uset(v_buckets_2901_, v___x_2923_, v___x_2928_);
                    v___x_2930_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2931_ = lean_nat_mul(v_size_x27_2927_, v___x_2930_);
                    v___x_2932_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2933_ = lean_nat_div(v___x_2931_, v___x_2932_);
                    crate::leanh::lean_dec(v___x_2931_);
                    v___x_2934_ = lean_array_get_size(v_buckets_x27_2929_);
                    v___x_2935_ = lean_nat_dec_le(v___x_2933_, v___x_2934_);
                    crate::leanh::lean_dec(v___x_2933_);
                    if v___x_2935_ == 0 {
                        v_val_2936_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2896_,
                            v_buckets_x27_2929_,
                        );
                        if v_isShared_2909_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2908_, 1, v_val_2936_);
                            crate::leanh::lean_ctor_set(v___x_2908_, 0, v_size_x27_2927_);
                            v___x_2938_ = v___x_2908_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2941_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2941_,
                                0,
                                v_size_x27_2927_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_val_2936_);
                            v___x_2938_ = v_reuseFailAlloc_2941_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2896_);
                        if v_isShared_2909_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2908_, 1, v_buckets_x27_2929_);
                            crate::leanh::lean_ctor_set(v___x_2908_, 0, v_size_x27_2927_);
                            v___x_2943_ = v___x_2908_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2946_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2946_,
                                0,
                                v_size_x27_2927_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2946_,
                                1,
                                v_buckets_x27_2929_,
                            );
                            v___x_2943_ = v_reuseFailAlloc_2946_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2924_);
                    crate::leanh::lean_dec_ref(v_inst_2896_);
                    v___x_2947_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2948_ =
                        lean_array_uset(v_buckets_2901_, v___x_2923_, v___x_2947_);
                    v___x_2949_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_2895_,
                        v_a_2898_,
                        v_b_2899_,
                        v_bkt_2924_,
                    );
                    v___x_2950_ = lean_array_uset(v_buckets_x27_2948_, v___x_2923_, v___x_2949_);
                    if v_isShared_2909_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2908_, 1, v___x_2950_);
                        v___x_2952_ = v___x_2908_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2955_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_size_2900_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 1, v___x_2950_);
                        v___x_2952_ = v_reuseFailAlloc_2955_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2939_ = crate::leanh::lean_box((v___x_2925_) as usize);
                v___x_2940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2940_, 0, v___x_2939_);
                crate::leanh::lean_ctor_set(v___x_2940_, 1, v___x_2938_);
                return v___x_2940_;
            }
            3 => {
                v___x_2944_ = crate::leanh::lean_box((v___x_2925_) as usize);
                v___x_2945_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2944_);
                crate::leanh::lean_ctor_set(v___x_2945_, 1, v___x_2943_);
                return v___x_2945_;
            }
            4 => {
                v___x_2953_ = crate::leanh::lean_box((v___x_2925_) as usize);
                v___x_2954_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2954_, 0, v___x_2953_);
                crate::leanh::lean_ctor_set(v___x_2954_, 1, v___x_2952_);
                return v___x_2954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_containsThenInsert(
    mut v_00_u03b1_2959_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2960_: *mut crate::leanh::LeanObject,
    mut v_inst_2961_: *mut crate::leanh::LeanObject,
    mut v_inst_2962_: *mut crate::leanh::LeanObject,
    mut v_m_2963_: *mut crate::leanh::LeanObject,
    mut v_a_2964_: *mut crate::leanh::LeanObject,
    mut v_b_2965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2975_: u8 = 0;
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u64 = 0;
    let mut v___x_2978_: u64 = 0;
    let mut v___x_2979_: u64 = 0;
    let mut v___x_2980_: u64 = 0;
    let mut v_fold_2981_: u64 = 0;
    let mut v___x_2982_: u64 = 0;
    let mut v___x_2983_: u64 = 0;
    let mut v___x_2984_: u64 = 0;
    let mut v___x_2985_: usize = 0;
    let mut v___x_2986_: usize = 0;
    let mut v___x_2987_: usize = 0;
    let mut v___x_2988_: usize = 0;
    let mut v___x_2989_: usize = 0;
    let mut v_bkt_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: u8 = 0;
    let mut v_val_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_unused_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2966_ = crate::leanh::lean_ctor_get(v_m_2963_, 0);
                v_buckets_2967_ = crate::leanh::lean_ctor_get(v_m_2963_, 1);
                v___x_2968_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2969_ = lean_array_get_size(v_buckets_2967_);
                v___x_2970_ = lean_nat_dec_lt(v___x_2968_, v___x_2969_);
                if v___x_2970_ == 0 {
                    crate::leanh::lean_dec(v_b_2965_);
                    crate::leanh::lean_dec(v_a_2964_);
                    crate::leanh::lean_dec_ref(v_inst_2962_);
                    crate::leanh::lean_dec_ref(v_inst_2961_);
                    v___x_2971_ = crate::leanh::lean_box((v___x_2970_) as usize);
                    v___x_2972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2972_, 0, v___x_2971_);
                    crate::leanh::lean_ctor_set(v___x_2972_, 1, v_m_2963_);
                    return v___x_2972_;
                } else {
                    crate::leanh::lean_inc_ref(v_buckets_2967_);
                    crate::leanh::lean_inc(v_size_2966_);
                    v_isSharedCheck_3022_ = (!crate::leanh::lean_is_exclusive(v_m_2963_)) as u8;
                    if v_isSharedCheck_3022_ == 0 {
                        v_unused_3023_ = crate::leanh::lean_ctor_get(v_m_2963_, 1);
                        crate::leanh::lean_dec(v_unused_3023_);
                        v_unused_3024_ = crate::leanh::lean_ctor_get(v_m_2963_, 0);
                        crate::leanh::lean_dec(v_unused_3024_);
                        v___x_2974_ = v_m_2963_;
                        v_isShared_2975_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2963_);
                        v___x_2974_ = crate::leanh::lean_box(0);
                        v_isShared_2975_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_2962_);
                crate::leanh::lean_inc_n(v_a_2964_, 2);
                v___x_2976_ = crate::leanh::lean_apply_1(v_inst_2962_, v_a_2964_);
                v___x_2977_ = 32u64;
                v___x_2978_ = crate::leanh::lean_unbox_uint64(v___x_2976_);
                v___x_2979_ = lean_uint64_shift_right(v___x_2978_, v___x_2977_);
                v___x_2980_ = crate::leanh::lean_unbox_uint64(v___x_2976_);
                crate::leanh::lean_dec_ref(v___x_2976_);
                v_fold_2981_ = lean_uint64_xor(v___x_2980_, v___x_2979_);
                v___x_2982_ = 16u64;
                v___x_2983_ = lean_uint64_shift_right(v_fold_2981_, v___x_2982_);
                v___x_2984_ = lean_uint64_xor(v_fold_2981_, v___x_2983_);
                v___x_2985_ = lean_uint64_to_usize(v___x_2984_);
                v___x_2986_ = lean_usize_of_nat(v___x_2969_);
                v___x_2987_ = 1usize;
                v___x_2988_ = lean_usize_sub(v___x_2986_, v___x_2987_);
                v___x_2989_ = lean_usize_land(v___x_2985_, v___x_2988_);
                v_bkt_2990_ = lean_array_uget_borrowed(v_buckets_2967_, v___x_2989_);
                crate::leanh::lean_inc(v_bkt_2990_);
                crate::leanh::lean_inc_ref(v_inst_2961_);
                v___x_2991_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2961_,
                    v_a_2964_,
                    v_bkt_2990_,
                );
                if v___x_2991_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2961_);
                    v___x_2992_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2993_ = lean_nat_add(v_size_2966_, v___x_2992_);
                    crate::leanh::lean_dec(v_size_2966_);
                    crate::leanh::lean_inc(v_bkt_2990_);
                    v___x_2994_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2994_, 0, v_a_2964_);
                    crate::leanh::lean_ctor_set(v___x_2994_, 1, v_b_2965_);
                    crate::leanh::lean_ctor_set(v___x_2994_, 2, v_bkt_2990_);
                    v_buckets_x27_2995_ =
                        lean_array_uset(v_buckets_2967_, v___x_2989_, v___x_2994_);
                    v___x_2996_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2997_ = lean_nat_mul(v_size_x27_2993_, v___x_2996_);
                    v___x_2998_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2999_ = lean_nat_div(v___x_2997_, v___x_2998_);
                    crate::leanh::lean_dec(v___x_2997_);
                    v___x_3000_ = lean_array_get_size(v_buckets_x27_2995_);
                    v___x_3001_ = lean_nat_dec_le(v___x_2999_, v___x_3000_);
                    crate::leanh::lean_dec(v___x_2999_);
                    if v___x_3001_ == 0 {
                        v_val_3002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2962_,
                            v_buckets_x27_2995_,
                        );
                        if v_isShared_2975_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2974_, 1, v_val_3002_);
                            crate::leanh::lean_ctor_set(v___x_2974_, 0, v_size_x27_2993_);
                            v___x_3004_ = v___x_2974_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3007_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3007_,
                                0,
                                v_size_x27_2993_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_val_3002_);
                            v___x_3004_ = v_reuseFailAlloc_3007_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2962_);
                        if v_isShared_2975_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2974_, 1, v_buckets_x27_2995_);
                            crate::leanh::lean_ctor_set(v___x_2974_, 0, v_size_x27_2993_);
                            v___x_3009_ = v___x_2974_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3012_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3012_,
                                0,
                                v_size_x27_2993_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3012_,
                                1,
                                v_buckets_x27_2995_,
                            );
                            v___x_3009_ = v_reuseFailAlloc_3012_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2990_);
                    crate::leanh::lean_dec_ref(v_inst_2962_);
                    v___x_3013_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3014_ =
                        lean_array_uset(v_buckets_2967_, v___x_2989_, v___x_3013_);
                    v___x_3015_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_2961_,
                        v_a_2964_,
                        v_b_2965_,
                        v_bkt_2990_,
                    );
                    v___x_3016_ = lean_array_uset(v_buckets_x27_3014_, v___x_2989_, v___x_3015_);
                    if v_isShared_2975_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2974_, 1, v___x_3016_);
                        v___x_3018_ = v___x_2974_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_size_2966_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3016_);
                        v___x_3018_ = v_reuseFailAlloc_3021_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3005_ = crate::leanh::lean_box((v___x_2991_) as usize);
                v___x_3006_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3006_, 0, v___x_3005_);
                crate::leanh::lean_ctor_set(v___x_3006_, 1, v___x_3004_);
                return v___x_3006_;
            }
            3 => {
                v___x_3010_ = crate::leanh::lean_box((v___x_2991_) as usize);
                v___x_3011_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3011_, 0, v___x_3010_);
                crate::leanh::lean_ctor_set(v___x_3011_, 1, v___x_3009_);
                return v___x_3011_;
            }
            4 => {
                v___x_3019_ = crate::leanh::lean_box((v___x_2991_) as usize);
                v___x_3020_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3020_, 0, v___x_3019_);
                crate::leanh::lean_ctor_set(v___x_3020_, 1, v___x_3018_);
                return v___x_3020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(
    mut v_inst_3025_: *mut crate::leanh::LeanObject,
    mut v_inst_3026_: *mut crate::leanh::LeanObject,
    mut v_m_3027_: *mut crate::leanh::LeanObject,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
    mut v_b_3029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: u8 = 0;
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u64 = 0;
    let mut v___x_3039_: u64 = 0;
    let mut v___x_3040_: u64 = 0;
    let mut v___x_3041_: u64 = 0;
    let mut v_fold_3042_: u64 = 0;
    let mut v___x_3043_: u64 = 0;
    let mut v___x_3044_: u64 = 0;
    let mut v___x_3045_: u64 = 0;
    let mut v___x_3046_: usize = 0;
    let mut v___x_3047_: usize = 0;
    let mut v___x_3048_: usize = 0;
    let mut v___x_3049_: usize = 0;
    let mut v___x_3050_: usize = 0;
    let mut v_bkt_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3055_: u8 = 0;
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v_val_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3075_: u8 = 0;
    let mut v_unused_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3030_ = crate::leanh::lean_ctor_get(v_m_3027_, 0);
                v_buckets_3031_ = crate::leanh::lean_ctor_get(v_m_3027_, 1);
                v___x_3032_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3033_ = lean_array_get_size(v_buckets_3031_);
                v___x_3034_ = lean_nat_dec_lt(v___x_3032_, v___x_3033_);
                if v___x_3034_ == 0 {
                    crate::leanh::lean_dec(v_b_3029_);
                    crate::leanh::lean_dec(v_a_3028_);
                    crate::leanh::lean_dec_ref(v_inst_3026_);
                    crate::leanh::lean_dec_ref(v_inst_3025_);
                    v___x_3035_ = crate::leanh::lean_box(0);
                    v___x_3036_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3036_, 0, v___x_3035_);
                    crate::leanh::lean_ctor_set(v___x_3036_, 1, v_m_3027_);
                    return v___x_3036_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_3026_);
                    crate::leanh::lean_inc_n(v_a_3028_, 2);
                    v___x_3037_ = crate::leanh::lean_apply_1(v_inst_3026_, v_a_3028_);
                    v___x_3038_ = 32u64;
                    v___x_3039_ = crate::leanh::lean_unbox_uint64(v___x_3037_);
                    v___x_3040_ = lean_uint64_shift_right(v___x_3039_, v___x_3038_);
                    v___x_3041_ = crate::leanh::lean_unbox_uint64(v___x_3037_);
                    crate::leanh::lean_dec_ref(v___x_3037_);
                    v_fold_3042_ = lean_uint64_xor(v___x_3041_, v___x_3040_);
                    v___x_3043_ = 16u64;
                    v___x_3044_ = lean_uint64_shift_right(v_fold_3042_, v___x_3043_);
                    v___x_3045_ = lean_uint64_xor(v_fold_3042_, v___x_3044_);
                    v___x_3046_ = lean_uint64_to_usize(v___x_3045_);
                    v___x_3047_ = lean_usize_of_nat(v___x_3033_);
                    v___x_3048_ = 1usize;
                    v___x_3049_ = lean_usize_sub(v___x_3047_, v___x_3048_);
                    v___x_3050_ = lean_usize_land(v___x_3046_, v___x_3049_);
                    v_bkt_3051_ = lean_array_uget_borrowed(v_buckets_3031_, v___x_3050_);
                    crate::leanh::lean_inc(v_bkt_3051_);
                    v___x_3052_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                        v_inst_3025_,
                        v_a_3028_,
                        v_bkt_3051_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3052_) == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_3031_);
                        crate::leanh::lean_inc(v_size_3030_);
                        v_isSharedCheck_3075_ = (!crate::leanh::lean_is_exclusive(v_m_3027_)) as u8;
                        if v_isSharedCheck_3075_ == 0 {
                            v_unused_3076_ = crate::leanh::lean_ctor_get(v_m_3027_, 1);
                            crate::leanh::lean_dec(v_unused_3076_);
                            v_unused_3077_ = crate::leanh::lean_ctor_get(v_m_3027_, 0);
                            crate::leanh::lean_dec(v_unused_3077_);
                            v___x_3054_ = v_m_3027_;
                            v_isShared_3055_ = v_isSharedCheck_3075_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_3027_);
                            v___x_3054_ = crate::leanh::lean_box(0);
                            v_isShared_3055_ = v_isSharedCheck_3075_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3029_);
                        crate::leanh::lean_dec(v_a_3028_);
                        crate::leanh::lean_dec_ref(v_inst_3026_);
                        v___x_3078_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3078_, 0, v___x_3052_);
                        crate::leanh::lean_ctor_set(v___x_3078_, 1, v_m_3027_);
                        return v___x_3078_;
                    }
                }
            }
            1 => {
                v___x_3056_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3057_ = lean_nat_add(v_size_3030_, v___x_3056_);
                crate::leanh::lean_dec(v_size_3030_);
                crate::leanh::lean_inc(v_bkt_3051_);
                v___x_3058_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3058_, 0, v_a_3028_);
                crate::leanh::lean_ctor_set(v___x_3058_, 1, v_b_3029_);
                crate::leanh::lean_ctor_set(v___x_3058_, 2, v_bkt_3051_);
                v_buckets_x27_3059_ = lean_array_uset(v_buckets_3031_, v___x_3050_, v___x_3058_);
                v___x_3060_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3061_ = lean_nat_mul(v_size_x27_3057_, v___x_3060_);
                v___x_3062_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3063_ = lean_nat_div(v___x_3061_, v___x_3062_);
                crate::leanh::lean_dec(v___x_3061_);
                v___x_3064_ = lean_array_get_size(v_buckets_x27_3059_);
                v___x_3065_ = lean_nat_dec_le(v___x_3063_, v___x_3064_);
                crate::leanh::lean_dec(v___x_3063_);
                if v___x_3065_ == 0 {
                    v_val_3066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3026_,
                        v_buckets_x27_3059_,
                    );
                    if v_isShared_3055_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3054_, 1, v_val_3066_);
                        crate::leanh::lean_ctor_set(v___x_3054_, 0, v_size_x27_3057_);
                        v___x_3068_ = v___x_3054_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3070_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_size_x27_3057_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_val_3066_);
                        v___x_3068_ = v_reuseFailAlloc_3070_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_3026_);
                    if v_isShared_3055_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3054_, 1, v_buckets_x27_3059_);
                        crate::leanh::lean_ctor_set(v___x_3054_, 0, v_size_x27_3057_);
                        v___x_3072_ = v___x_3054_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_size_x27_3057_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_buckets_x27_3059_);
                        v___x_3072_ = v_reuseFailAlloc_3074_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3069_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3052_);
                crate::leanh::lean_ctor_set(v___x_3069_, 1, v___x_3068_);
                return v___x_3069_;
            }
            3 => {
                v___x_3073_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3073_, 0, v___x_3052_);
                crate::leanh::lean_ctor_set(v___x_3073_, 1, v___x_3072_);
                return v___x_3073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(
    mut v_00_u03b1_3079_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3080_: *mut crate::leanh::LeanObject,
    mut v_inst_3081_: *mut crate::leanh::LeanObject,
    mut v_inst_3082_: *mut crate::leanh::LeanObject,
    mut v_inst_3083_: *mut crate::leanh::LeanObject,
    mut v_m_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_b_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: u64 = 0;
    let mut v___x_3096_: u64 = 0;
    let mut v___x_3097_: u64 = 0;
    let mut v___x_3098_: u64 = 0;
    let mut v_fold_3099_: u64 = 0;
    let mut v___x_3100_: u64 = 0;
    let mut v___x_3101_: u64 = 0;
    let mut v___x_3102_: u64 = 0;
    let mut v___x_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: usize = 0;
    let mut v___x_3106_: usize = 0;
    let mut v___x_3107_: usize = 0;
    let mut v_bkt_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3112_: u8 = 0;
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v_val_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_unused_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3087_ = crate::leanh::lean_ctor_get(v_m_3084_, 0);
                v_buckets_3088_ = crate::leanh::lean_ctor_get(v_m_3084_, 1);
                v___x_3089_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3090_ = lean_array_get_size(v_buckets_3088_);
                v___x_3091_ = lean_nat_dec_lt(v___x_3089_, v___x_3090_);
                if v___x_3091_ == 0 {
                    crate::leanh::lean_dec(v_b_3086_);
                    crate::leanh::lean_dec(v_a_3085_);
                    crate::leanh::lean_dec_ref(v_inst_3082_);
                    crate::leanh::lean_dec_ref(v_inst_3081_);
                    v___x_3092_ = crate::leanh::lean_box(0);
                    v___x_3093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3093_, 0, v___x_3092_);
                    crate::leanh::lean_ctor_set(v___x_3093_, 1, v_m_3084_);
                    return v___x_3093_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_3082_);
                    crate::leanh::lean_inc_n(v_a_3085_, 2);
                    v___x_3094_ = crate::leanh::lean_apply_1(v_inst_3082_, v_a_3085_);
                    v___x_3095_ = 32u64;
                    v___x_3096_ = crate::leanh::lean_unbox_uint64(v___x_3094_);
                    v___x_3097_ = lean_uint64_shift_right(v___x_3096_, v___x_3095_);
                    v___x_3098_ = crate::leanh::lean_unbox_uint64(v___x_3094_);
                    crate::leanh::lean_dec_ref(v___x_3094_);
                    v_fold_3099_ = lean_uint64_xor(v___x_3098_, v___x_3097_);
                    v___x_3100_ = 16u64;
                    v___x_3101_ = lean_uint64_shift_right(v_fold_3099_, v___x_3100_);
                    v___x_3102_ = lean_uint64_xor(v_fold_3099_, v___x_3101_);
                    v___x_3103_ = lean_uint64_to_usize(v___x_3102_);
                    v___x_3104_ = lean_usize_of_nat(v___x_3090_);
                    v___x_3105_ = 1usize;
                    v___x_3106_ = lean_usize_sub(v___x_3104_, v___x_3105_);
                    v___x_3107_ = lean_usize_land(v___x_3103_, v___x_3106_);
                    v_bkt_3108_ = lean_array_uget_borrowed(v_buckets_3088_, v___x_3107_);
                    crate::leanh::lean_inc(v_bkt_3108_);
                    v___x_3109_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                        v_inst_3081_,
                        v_a_3085_,
                        v_bkt_3108_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3109_) == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_3088_);
                        crate::leanh::lean_inc(v_size_3087_);
                        v_isSharedCheck_3132_ = (!crate::leanh::lean_is_exclusive(v_m_3084_)) as u8;
                        if v_isSharedCheck_3132_ == 0 {
                            v_unused_3133_ = crate::leanh::lean_ctor_get(v_m_3084_, 1);
                            crate::leanh::lean_dec(v_unused_3133_);
                            v_unused_3134_ = crate::leanh::lean_ctor_get(v_m_3084_, 0);
                            crate::leanh::lean_dec(v_unused_3134_);
                            v___x_3111_ = v_m_3084_;
                            v_isShared_3112_ = v_isSharedCheck_3132_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_3084_);
                            v___x_3111_ = crate::leanh::lean_box(0);
                            v_isShared_3112_ = v_isSharedCheck_3132_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3086_);
                        crate::leanh::lean_dec(v_a_3085_);
                        crate::leanh::lean_dec_ref(v_inst_3082_);
                        v___x_3135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3135_, 0, v___x_3109_);
                        crate::leanh::lean_ctor_set(v___x_3135_, 1, v_m_3084_);
                        return v___x_3135_;
                    }
                }
            }
            1 => {
                v___x_3113_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3114_ = lean_nat_add(v_size_3087_, v___x_3113_);
                crate::leanh::lean_dec(v_size_3087_);
                crate::leanh::lean_inc(v_bkt_3108_);
                v___x_3115_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3115_, 0, v_a_3085_);
                crate::leanh::lean_ctor_set(v___x_3115_, 1, v_b_3086_);
                crate::leanh::lean_ctor_set(v___x_3115_, 2, v_bkt_3108_);
                v_buckets_x27_3116_ = lean_array_uset(v_buckets_3088_, v___x_3107_, v___x_3115_);
                v___x_3117_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3118_ = lean_nat_mul(v_size_x27_3114_, v___x_3117_);
                v___x_3119_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3120_ = lean_nat_div(v___x_3118_, v___x_3119_);
                crate::leanh::lean_dec(v___x_3118_);
                v___x_3121_ = lean_array_get_size(v_buckets_x27_3116_);
                v___x_3122_ = lean_nat_dec_le(v___x_3120_, v___x_3121_);
                crate::leanh::lean_dec(v___x_3120_);
                if v___x_3122_ == 0 {
                    v_val_3123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3082_,
                        v_buckets_x27_3116_,
                    );
                    if v_isShared_3112_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3111_, 1, v_val_3123_);
                        crate::leanh::lean_ctor_set(v___x_3111_, 0, v_size_x27_3114_);
                        v___x_3125_ = v___x_3111_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3127_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_size_x27_3114_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_val_3123_);
                        v___x_3125_ = v_reuseFailAlloc_3127_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_3082_);
                    if v_isShared_3112_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3111_, 1, v_buckets_x27_3116_);
                        crate::leanh::lean_ctor_set(v___x_3111_, 0, v_size_x27_3114_);
                        v___x_3129_ = v___x_3111_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_size_x27_3114_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_buckets_x27_3116_);
                        v___x_3129_ = v_reuseFailAlloc_3131_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3126_, 0, v___x_3109_);
                crate::leanh::lean_ctor_set(v___x_3126_, 1, v___x_3125_);
                return v___x_3126_;
            }
            3 => {
                v___x_3130_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3130_, 0, v___x_3109_);
                crate::leanh::lean_ctor_set(v___x_3130_, 1, v___x_3129_);
                return v___x_3130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(
    mut v_inst_3136_: *mut crate::leanh::LeanObject,
    mut v_inst_3137_: *mut crate::leanh::LeanObject,
    mut v_m_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_b_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: u64 = 0;
    let mut v___x_3150_: u64 = 0;
    let mut v___x_3151_: u64 = 0;
    let mut v___x_3152_: u64 = 0;
    let mut v_fold_3153_: u64 = 0;
    let mut v___x_3154_: u64 = 0;
    let mut v___x_3155_: u64 = 0;
    let mut v___x_3156_: u64 = 0;
    let mut v___x_3157_: usize = 0;
    let mut v___x_3158_: usize = 0;
    let mut v___x_3159_: usize = 0;
    let mut v___x_3160_: usize = 0;
    let mut v___x_3161_: usize = 0;
    let mut v_bkt_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v_val_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v_unused_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3141_ = crate::leanh::lean_ctor_get(v_m_3138_, 0);
                v_buckets_3142_ = crate::leanh::lean_ctor_get(v_m_3138_, 1);
                v___x_3143_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3144_ = lean_array_get_size(v_buckets_3142_);
                v___x_3145_ = lean_nat_dec_lt(v___x_3143_, v___x_3144_);
                if v___x_3145_ == 0 {
                    crate::leanh::lean_dec(v_b_3140_);
                    crate::leanh::lean_dec(v_a_3139_);
                    crate::leanh::lean_dec_ref(v_inst_3137_);
                    crate::leanh::lean_dec_ref(v_inst_3136_);
                    v___x_3146_ = crate::leanh::lean_box((v___x_3145_) as usize);
                    v___x_3147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3147_, 0, v___x_3146_);
                    crate::leanh::lean_ctor_set(v___x_3147_, 1, v_m_3138_);
                    return v___x_3147_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_3137_);
                    crate::leanh::lean_inc_n(v_a_3139_, 2);
                    v___x_3148_ = crate::leanh::lean_apply_1(v_inst_3137_, v_a_3139_);
                    v___x_3149_ = 32u64;
                    v___x_3150_ = crate::leanh::lean_unbox_uint64(v___x_3148_);
                    v___x_3151_ = lean_uint64_shift_right(v___x_3150_, v___x_3149_);
                    v___x_3152_ = crate::leanh::lean_unbox_uint64(v___x_3148_);
                    crate::leanh::lean_dec_ref(v___x_3148_);
                    v_fold_3153_ = lean_uint64_xor(v___x_3152_, v___x_3151_);
                    v___x_3154_ = 16u64;
                    v___x_3155_ = lean_uint64_shift_right(v_fold_3153_, v___x_3154_);
                    v___x_3156_ = lean_uint64_xor(v_fold_3153_, v___x_3155_);
                    v___x_3157_ = lean_uint64_to_usize(v___x_3156_);
                    v___x_3158_ = lean_usize_of_nat(v___x_3144_);
                    v___x_3159_ = 1usize;
                    v___x_3160_ = lean_usize_sub(v___x_3158_, v___x_3159_);
                    v___x_3161_ = lean_usize_land(v___x_3157_, v___x_3160_);
                    v_bkt_3162_ = lean_array_uget_borrowed(v_buckets_3142_, v___x_3161_);
                    crate::leanh::lean_inc(v_bkt_3162_);
                    v___x_3163_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_3136_,
                        v_a_3139_,
                        v_bkt_3162_,
                    );
                    if v___x_3163_ == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_3142_);
                        crate::leanh::lean_inc(v_size_3141_);
                        v_isSharedCheck_3188_ = (!crate::leanh::lean_is_exclusive(v_m_3138_)) as u8;
                        if v_isSharedCheck_3188_ == 0 {
                            v_unused_3189_ = crate::leanh::lean_ctor_get(v_m_3138_, 1);
                            crate::leanh::lean_dec(v_unused_3189_);
                            v_unused_3190_ = crate::leanh::lean_ctor_get(v_m_3138_, 0);
                            crate::leanh::lean_dec(v_unused_3190_);
                            v___x_3165_ = v_m_3138_;
                            v_isShared_3166_ = v_isSharedCheck_3188_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_3138_);
                            v___x_3165_ = crate::leanh::lean_box(0);
                            v_isShared_3166_ = v_isSharedCheck_3188_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3140_);
                        crate::leanh::lean_dec(v_a_3139_);
                        crate::leanh::lean_dec_ref(v_inst_3137_);
                        v___x_3191_ = crate::leanh::lean_box((v___x_3163_) as usize);
                        v___x_3192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3192_, 0, v___x_3191_);
                        crate::leanh::lean_ctor_set(v___x_3192_, 1, v_m_3138_);
                        return v___x_3192_;
                    }
                }
            }
            1 => {
                v___x_3167_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3168_ = lean_nat_add(v_size_3141_, v___x_3167_);
                crate::leanh::lean_dec(v_size_3141_);
                crate::leanh::lean_inc(v_bkt_3162_);
                v___x_3169_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3169_, 0, v_a_3139_);
                crate::leanh::lean_ctor_set(v___x_3169_, 1, v_b_3140_);
                crate::leanh::lean_ctor_set(v___x_3169_, 2, v_bkt_3162_);
                v_buckets_x27_3170_ = lean_array_uset(v_buckets_3142_, v___x_3161_, v___x_3169_);
                v___x_3171_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3172_ = lean_nat_mul(v_size_x27_3168_, v___x_3171_);
                v___x_3173_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3174_ = lean_nat_div(v___x_3172_, v___x_3173_);
                crate::leanh::lean_dec(v___x_3172_);
                v___x_3175_ = lean_array_get_size(v_buckets_x27_3170_);
                v___x_3176_ = lean_nat_dec_le(v___x_3174_, v___x_3175_);
                crate::leanh::lean_dec(v___x_3174_);
                if v___x_3176_ == 0 {
                    v_val_3177_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3137_,
                        v_buckets_x27_3170_,
                    );
                    if v_isShared_3166_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3165_, 1, v_val_3177_);
                        crate::leanh::lean_ctor_set(v___x_3165_, 0, v_size_x27_3168_);
                        v___x_3179_ = v___x_3165_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_size_x27_3168_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_val_3177_);
                        v___x_3179_ = v_reuseFailAlloc_3182_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_3137_);
                    if v_isShared_3166_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3165_, 1, v_buckets_x27_3170_);
                        crate::leanh::lean_ctor_set(v___x_3165_, 0, v_size_x27_3168_);
                        v___x_3184_ = v___x_3165_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3187_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_size_x27_3168_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_buckets_x27_3170_);
                        v___x_3184_ = v_reuseFailAlloc_3187_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3180_ = crate::leanh::lean_box((v___x_3163_) as usize);
                v___x_3181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3181_, 0, v___x_3180_);
                crate::leanh::lean_ctor_set(v___x_3181_, 1, v___x_3179_);
                return v___x_3181_;
            }
            3 => {
                v___x_3185_ = crate::leanh::lean_box((v___x_3163_) as usize);
                v___x_3186_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3186_, 0, v___x_3185_);
                crate::leanh::lean_ctor_set(v___x_3186_, 1, v___x_3184_);
                return v___x_3186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_containsThenInsertIfNew(
    mut v_00_u03b1_3193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3194_: *mut crate::leanh::LeanObject,
    mut v_inst_3195_: *mut crate::leanh::LeanObject,
    mut v_inst_3196_: *mut crate::leanh::LeanObject,
    mut v_m_3197_: *mut crate::leanh::LeanObject,
    mut v_a_3198_: *mut crate::leanh::LeanObject,
    mut v_b_3199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: u64 = 0;
    let mut v___x_3209_: u64 = 0;
    let mut v___x_3210_: u64 = 0;
    let mut v___x_3211_: u64 = 0;
    let mut v_fold_3212_: u64 = 0;
    let mut v___x_3213_: u64 = 0;
    let mut v___x_3214_: u64 = 0;
    let mut v___x_3215_: u64 = 0;
    let mut v___x_3216_: usize = 0;
    let mut v___x_3217_: usize = 0;
    let mut v___x_3218_: usize = 0;
    let mut v___x_3219_: usize = 0;
    let mut v___x_3220_: usize = 0;
    let mut v_bkt_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u8 = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: u8 = 0;
    let mut v_val_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_unused_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3200_ = crate::leanh::lean_ctor_get(v_m_3197_, 0);
                v_buckets_3201_ = crate::leanh::lean_ctor_get(v_m_3197_, 1);
                v___x_3202_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3203_ = lean_array_get_size(v_buckets_3201_);
                v___x_3204_ = lean_nat_dec_lt(v___x_3202_, v___x_3203_);
                if v___x_3204_ == 0 {
                    crate::leanh::lean_dec(v_b_3199_);
                    crate::leanh::lean_dec(v_a_3198_);
                    crate::leanh::lean_dec_ref(v_inst_3196_);
                    crate::leanh::lean_dec_ref(v_inst_3195_);
                    v___x_3205_ = crate::leanh::lean_box((v___x_3204_) as usize);
                    v___x_3206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3206_, 0, v___x_3205_);
                    crate::leanh::lean_ctor_set(v___x_3206_, 1, v_m_3197_);
                    return v___x_3206_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_3196_);
                    crate::leanh::lean_inc_n(v_a_3198_, 2);
                    v___x_3207_ = crate::leanh::lean_apply_1(v_inst_3196_, v_a_3198_);
                    v___x_3208_ = 32u64;
                    v___x_3209_ = crate::leanh::lean_unbox_uint64(v___x_3207_);
                    v___x_3210_ = lean_uint64_shift_right(v___x_3209_, v___x_3208_);
                    v___x_3211_ = crate::leanh::lean_unbox_uint64(v___x_3207_);
                    crate::leanh::lean_dec_ref(v___x_3207_);
                    v_fold_3212_ = lean_uint64_xor(v___x_3211_, v___x_3210_);
                    v___x_3213_ = 16u64;
                    v___x_3214_ = lean_uint64_shift_right(v_fold_3212_, v___x_3213_);
                    v___x_3215_ = lean_uint64_xor(v_fold_3212_, v___x_3214_);
                    v___x_3216_ = lean_uint64_to_usize(v___x_3215_);
                    v___x_3217_ = lean_usize_of_nat(v___x_3203_);
                    v___x_3218_ = 1usize;
                    v___x_3219_ = lean_usize_sub(v___x_3217_, v___x_3218_);
                    v___x_3220_ = lean_usize_land(v___x_3216_, v___x_3219_);
                    v_bkt_3221_ = lean_array_uget_borrowed(v_buckets_3201_, v___x_3220_);
                    crate::leanh::lean_inc(v_bkt_3221_);
                    v___x_3222_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_3195_,
                        v_a_3198_,
                        v_bkt_3221_,
                    );
                    if v___x_3222_ == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_3201_);
                        crate::leanh::lean_inc(v_size_3200_);
                        v_isSharedCheck_3247_ = (!crate::leanh::lean_is_exclusive(v_m_3197_)) as u8;
                        if v_isSharedCheck_3247_ == 0 {
                            v_unused_3248_ = crate::leanh::lean_ctor_get(v_m_3197_, 1);
                            crate::leanh::lean_dec(v_unused_3248_);
                            v_unused_3249_ = crate::leanh::lean_ctor_get(v_m_3197_, 0);
                            crate::leanh::lean_dec(v_unused_3249_);
                            v___x_3224_ = v_m_3197_;
                            v_isShared_3225_ = v_isSharedCheck_3247_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_3197_);
                            v___x_3224_ = crate::leanh::lean_box(0);
                            v_isShared_3225_ = v_isSharedCheck_3247_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3199_);
                        crate::leanh::lean_dec(v_a_3198_);
                        crate::leanh::lean_dec_ref(v_inst_3196_);
                        v___x_3250_ = crate::leanh::lean_box((v___x_3222_) as usize);
                        v___x_3251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3251_, 0, v___x_3250_);
                        crate::leanh::lean_ctor_set(v___x_3251_, 1, v_m_3197_);
                        return v___x_3251_;
                    }
                }
            }
            1 => {
                v___x_3226_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3227_ = lean_nat_add(v_size_3200_, v___x_3226_);
                crate::leanh::lean_dec(v_size_3200_);
                crate::leanh::lean_inc(v_bkt_3221_);
                v___x_3228_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3228_, 0, v_a_3198_);
                crate::leanh::lean_ctor_set(v___x_3228_, 1, v_b_3199_);
                crate::leanh::lean_ctor_set(v___x_3228_, 2, v_bkt_3221_);
                v_buckets_x27_3229_ = lean_array_uset(v_buckets_3201_, v___x_3220_, v___x_3228_);
                v___x_3230_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3231_ = lean_nat_mul(v_size_x27_3227_, v___x_3230_);
                v___x_3232_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3233_ = lean_nat_div(v___x_3231_, v___x_3232_);
                crate::leanh::lean_dec(v___x_3231_);
                v___x_3234_ = lean_array_get_size(v_buckets_x27_3229_);
                v___x_3235_ = lean_nat_dec_le(v___x_3233_, v___x_3234_);
                crate::leanh::lean_dec(v___x_3233_);
                if v___x_3235_ == 0 {
                    v_val_3236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3196_,
                        v_buckets_x27_3229_,
                    );
                    if v_isShared_3225_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3224_, 1, v_val_3236_);
                        crate::leanh::lean_ctor_set(v___x_3224_, 0, v_size_x27_3227_);
                        v___x_3238_ = v___x_3224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3241_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_size_x27_3227_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_val_3236_);
                        v___x_3238_ = v_reuseFailAlloc_3241_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_3196_);
                    if v_isShared_3225_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3224_, 1, v_buckets_x27_3229_);
                        crate::leanh::lean_ctor_set(v___x_3224_, 0, v_size_x27_3227_);
                        v___x_3243_ = v___x_3224_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3246_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_size_x27_3227_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_buckets_x27_3229_);
                        v___x_3243_ = v_reuseFailAlloc_3246_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3239_ = crate::leanh::lean_box((v___x_3222_) as usize);
                v___x_3240_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3240_, 0, v___x_3239_);
                crate::leanh::lean_ctor_set(v___x_3240_, 1, v___x_3238_);
                return v___x_3240_;
            }
            3 => {
                v___x_3244_ = crate::leanh::lean_box((v___x_3222_) as usize);
                v___x_3245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3245_, 0, v___x_3244_);
                crate::leanh::lean_ctor_set(v___x_3245_, 1, v___x_3243_);
                return v___x_3245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_get_x3f___redArg(
    mut v_inst_3252_: *mut crate::leanh::LeanObject,
    mut v_inst_3253_: *mut crate::leanh::LeanObject,
    mut v_m_3254_: *mut crate::leanh::LeanObject,
    mut v_a_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: u8 = 0;
    v_buckets_3256_ = crate::leanh::lean_ctor_get(v_m_3254_, 1);
    v___x_3257_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3258_ = lean_array_get_size(v_buckets_3256_);
    v___x_3259_ = lean_nat_dec_lt(v___x_3257_, v___x_3258_);
    if v___x_3259_ == 0 {
        let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3255_);
        crate::leanh::lean_dec_ref(v_inst_3253_);
        crate::leanh::lean_dec_ref(v_inst_3252_);
        v___x_3260_ = crate::leanh::lean_box(0);
        return v___x_3260_;
    } else {
        let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3261_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
            v_inst_3252_,
            v_inst_3253_,
            v_m_3254_,
            v_a_3255_,
        );
        return v___x_3261_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_get_x3f___redArg___boxed(
    mut v_inst_3262_: *mut crate::leanh::LeanObject,
    mut v_inst_3263_: *mut crate::leanh::LeanObject,
    mut v_m_3264_: *mut crate::leanh::LeanObject,
    mut v_a_3265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ =
        l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_3262_, v_inst_3263_, v_m_3264_, v_a_3265_);
    crate::leanh::lean_dec_ref(v_m_3264_);
    return v_res_3266_;
}
pub unsafe fn l_Std_DHashMap_Raw_get_x3f(
    mut v_00_u03b1_3267_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3268_: *mut crate::leanh::LeanObject,
    mut v_inst_3269_: *mut crate::leanh::LeanObject,
    mut v_inst_3270_: *mut crate::leanh::LeanObject,
    mut v_inst_3271_: *mut crate::leanh::LeanObject,
    mut v_m_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    v_buckets_3274_ = crate::leanh::lean_ctor_get(v_m_3272_, 1);
    v___x_3275_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3276_ = lean_array_get_size(v_buckets_3274_);
    v___x_3277_ = lean_nat_dec_lt(v___x_3275_, v___x_3276_);
    if v___x_3277_ == 0 {
        let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3273_);
        crate::leanh::lean_dec_ref(v_inst_3271_);
        crate::leanh::lean_dec_ref(v_inst_3269_);
        v___x_3278_ = crate::leanh::lean_box(0);
        return v___x_3278_;
    } else {
        let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
            v_inst_3269_,
            v_inst_3271_,
            v_m_3272_,
            v_a_3273_,
        );
        return v___x_3279_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_get_x3f___boxed(
    mut v_00_u03b1_3280_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3281_: *mut crate::leanh::LeanObject,
    mut v_inst_3282_: *mut crate::leanh::LeanObject,
    mut v_inst_3283_: *mut crate::leanh::LeanObject,
    mut v_inst_3284_: *mut crate::leanh::LeanObject,
    mut v_m_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3287_ = l_Std_DHashMap_Raw_get_x3f(
        v_00_u03b1_3280_,
        v_00_u03b2_3281_,
        v_inst_3282_,
        v_inst_3283_,
        v_inst_3284_,
        v_m_3285_,
        v_a_3286_,
    );
    crate::leanh::lean_dec_ref(v_m_3285_);
    return v_res_3287_;
}
pub unsafe fn l_Std_DHashMap_Raw_contains___redArg(
    mut v_inst_3288_: *mut crate::leanh::LeanObject,
    mut v_inst_3289_: *mut crate::leanh::LeanObject,
    mut v_m_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    v_buckets_3292_ = crate::leanh::lean_ctor_get(v_m_3290_, 1);
    v___x_3293_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3294_ = lean_array_get_size(v_buckets_3292_);
    v___x_3295_ = lean_nat_dec_lt(v___x_3293_, v___x_3294_);
    if v___x_3295_ == 0 {
        crate::leanh::lean_dec(v_a_3291_);
        crate::leanh::lean_dec_ref(v_inst_3289_);
        crate::leanh::lean_dec_ref(v_inst_3288_);
        return v___x_3295_;
    } else {
        let mut v___x_3296_: u8 = 0;
        v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_3288_,
            v_inst_3289_,
            v_m_3290_,
            v_a_3291_,
        );
        return v___x_3296_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_contains___redArg___boxed(
    mut v_inst_3297_: *mut crate::leanh::LeanObject,
    mut v_inst_3298_: *mut crate::leanh::LeanObject,
    mut v_m_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3301_: u8 = 0;
    let mut v_r_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3301_ =
        l_Std_DHashMap_Raw_contains___redArg(v_inst_3297_, v_inst_3298_, v_m_3299_, v_a_3300_);
    crate::leanh::lean_dec_ref(v_m_3299_);
    v_r_3302_ = crate::leanh::lean_box((v_res_3301_) as usize);
    return v_r_3302_;
}
pub unsafe fn l_Std_DHashMap_Raw_contains(
    mut v_00_u03b1_3303_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3304_: *mut crate::leanh::LeanObject,
    mut v_inst_3305_: *mut crate::leanh::LeanObject,
    mut v_inst_3306_: *mut crate::leanh::LeanObject,
    mut v_m_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: u8 = 0;
    v_buckets_3309_ = crate::leanh::lean_ctor_get(v_m_3307_, 1);
    v___x_3310_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3311_ = lean_array_get_size(v_buckets_3309_);
    v___x_3312_ = lean_nat_dec_lt(v___x_3310_, v___x_3311_);
    if v___x_3312_ == 0 {
        crate::leanh::lean_dec(v_a_3308_);
        crate::leanh::lean_dec_ref(v_inst_3306_);
        crate::leanh::lean_dec_ref(v_inst_3305_);
        return v___x_3312_;
    } else {
        let mut v___x_3313_: u8 = 0;
        v___x_3313_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_3305_,
            v_inst_3306_,
            v_m_3307_,
            v_a_3308_,
        );
        return v___x_3313_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_contains___boxed(
    mut v_00_u03b1_3314_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3315_: *mut crate::leanh::LeanObject,
    mut v_inst_3316_: *mut crate::leanh::LeanObject,
    mut v_inst_3317_: *mut crate::leanh::LeanObject,
    mut v_m_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3320_: u8 = 0;
    let mut v_r_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Std_DHashMap_Raw_contains(
        v_00_u03b1_3314_,
        v_00_u03b2_3315_,
        v_inst_3316_,
        v_inst_3317_,
        v_m_3318_,
        v_a_3319_,
    );
    crate::leanh::lean_dec_ref(v_m_3318_);
    v_r_3321_ = crate::leanh::lean_box((v_res_3320_) as usize);
    return v_r_3321_;
}
pub unsafe fn l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(
    mut v_00_u03b1_3322_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3323_: *mut crate::leanh::LeanObject,
    mut v_inst_3324_: *mut crate::leanh::LeanObject,
    mut v_inst_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3326_ = crate::leanh::lean_box(0);
    return v___x_3326_;
}
pub unsafe fn l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(
    mut v_00_u03b1_3327_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3328_: *mut crate::leanh::LeanObject,
    mut v_inst_3329_: *mut crate::leanh::LeanObject,
    mut v_inst_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(
        v_00_u03b1_3327_,
        v_00_u03b2_3328_,
        v_inst_3329_,
        v_inst_3330_,
    );
    crate::leanh::lean_dec_ref(v_inst_3330_);
    crate::leanh::lean_dec_ref(v_inst_3329_);
    return v_res_3331_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableMem___redArg(
    mut v_inst_3332_: *mut crate::leanh::LeanObject,
    mut v_inst_3333_: *mut crate::leanh::LeanObject,
    mut v_m_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    v_buckets_3336_ = crate::leanh::lean_ctor_get(v_m_3334_, 1);
    v___x_3337_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3338_ = lean_array_get_size(v_buckets_3336_);
    v___x_3339_ = lean_nat_dec_lt(v___x_3337_, v___x_3338_);
    if v___x_3339_ == 0 {
        crate::leanh::lean_dec(v_a_3335_);
        crate::leanh::lean_dec_ref(v_inst_3333_);
        crate::leanh::lean_dec_ref(v_inst_3332_);
        return v___x_3339_;
    } else {
        let mut v___x_3340_: u8 = 0;
        v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_3332_,
            v_inst_3333_,
            v_m_3334_,
            v_a_3335_,
        );
        return v___x_3340_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(
    mut v_inst_3341_: *mut crate::leanh::LeanObject,
    mut v_inst_3342_: *mut crate::leanh::LeanObject,
    mut v_m_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3345_: u8 = 0;
    let mut v_r_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3345_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(
        v_inst_3341_,
        v_inst_3342_,
        v_m_3343_,
        v_a_3344_,
    );
    crate::leanh::lean_dec_ref(v_m_3343_);
    v_r_3346_ = crate::leanh::lean_box((v_res_3345_) as usize);
    return v_r_3346_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableMem(
    mut v_00_u03b1_3347_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3348_: *mut crate::leanh::LeanObject,
    mut v_inst_3349_: *mut crate::leanh::LeanObject,
    mut v_inst_3350_: *mut crate::leanh::LeanObject,
    mut v_m_3351_: *mut crate::leanh::LeanObject,
    mut v_a_3352_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3353_: u8 = 0;
    v___x_3353_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(
        v_inst_3349_,
        v_inst_3350_,
        v_m_3351_,
        v_a_3352_,
    );
    return v___x_3353_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableMem___boxed(
    mut v_00_u03b1_3354_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3355_: *mut crate::leanh::LeanObject,
    mut v_inst_3356_: *mut crate::leanh::LeanObject,
    mut v_inst_3357_: *mut crate::leanh::LeanObject,
    mut v_m_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3360_: u8 = 0;
    let mut v_r_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3360_ = l_Std_DHashMap_Raw_instDecidableMem(
        v_00_u03b1_3354_,
        v_00_u03b2_3355_,
        v_inst_3356_,
        v_inst_3357_,
        v_m_3358_,
        v_a_3359_,
    );
    crate::leanh::lean_dec_ref(v_m_3358_);
    v_r_3361_ = crate::leanh::lean_box((v_res_3360_) as usize);
    return v_r_3361_;
}
pub unsafe fn l_Std_DHashMap_Raw_get___redArg(
    mut v_inst_3362_: *mut crate::leanh::LeanObject,
    mut v_inst_3363_: *mut crate::leanh::LeanObject,
    mut v_m_3364_: *mut crate::leanh::LeanObject,
    mut v_a_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(
        v_inst_3362_,
        v_inst_3363_,
        v_m_3364_,
        v_a_3365_,
    );
    return v___x_3366_;
}
pub unsafe fn l_Std_DHashMap_Raw_get___redArg___boxed(
    mut v_inst_3367_: *mut crate::leanh::LeanObject,
    mut v_inst_3368_: *mut crate::leanh::LeanObject,
    mut v_m_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3371_ = l_Std_DHashMap_Raw_get___redArg(v_inst_3367_, v_inst_3368_, v_m_3369_, v_a_3370_);
    crate::leanh::lean_dec_ref(v_m_3369_);
    return v_res_3371_;
}
pub unsafe fn l_Std_DHashMap_Raw_get(
    mut v_00_u03b1_3372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3373_: *mut crate::leanh::LeanObject,
    mut v_inst_3374_: *mut crate::leanh::LeanObject,
    mut v_inst_3375_: *mut crate::leanh::LeanObject,
    mut v_inst_3376_: *mut crate::leanh::LeanObject,
    mut v_m_3377_: *mut crate::leanh::LeanObject,
    mut v_a_3378_: *mut crate::leanh::LeanObject,
    mut v_h_3379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3380_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(
        v_inst_3374_,
        v_inst_3375_,
        v_m_3377_,
        v_a_3378_,
    );
    return v___x_3380_;
}
pub unsafe fn l_Std_DHashMap_Raw_get___boxed(
    mut v_00_u03b1_3381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3382_: *mut crate::leanh::LeanObject,
    mut v_inst_3383_: *mut crate::leanh::LeanObject,
    mut v_inst_3384_: *mut crate::leanh::LeanObject,
    mut v_inst_3385_: *mut crate::leanh::LeanObject,
    mut v_m_3386_: *mut crate::leanh::LeanObject,
    mut v_a_3387_: *mut crate::leanh::LeanObject,
    mut v_h_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3389_ = l_Std_DHashMap_Raw_get(
        v_00_u03b1_3381_,
        v_00_u03b2_3382_,
        v_inst_3383_,
        v_inst_3384_,
        v_inst_3385_,
        v_m_3386_,
        v_a_3387_,
        v_h_3388_,
    );
    crate::leanh::lean_dec_ref(v_m_3386_);
    return v_res_3389_;
}
pub unsafe fn l_Std_DHashMap_Raw_getD___redArg(
    mut v_inst_3390_: *mut crate::leanh::LeanObject,
    mut v_inst_3391_: *mut crate::leanh::LeanObject,
    mut v_m_3392_: *mut crate::leanh::LeanObject,
    mut v_a_3393_: *mut crate::leanh::LeanObject,
    mut v_fallback_3394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    v_buckets_3395_ = crate::leanh::lean_ctor_get(v_m_3392_, 1);
    v___x_3396_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3397_ = lean_array_get_size(v_buckets_3395_);
    v___x_3398_ = lean_nat_dec_lt(v___x_3396_, v___x_3397_);
    if v___x_3398_ == 0 {
        crate::leanh::lean_dec(v_a_3393_);
        crate::leanh::lean_dec_ref(v_inst_3391_);
        crate::leanh::lean_dec_ref(v_inst_3390_);
        crate::leanh::lean_inc(v_fallback_3394_);
        return v_fallback_3394_;
    } else {
        let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3399_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
            v_inst_3390_,
            v_inst_3391_,
            v_m_3392_,
            v_a_3393_,
            v_fallback_3394_,
        );
        return v___x_3399_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getD___redArg___boxed(
    mut v_inst_3400_: *mut crate::leanh::LeanObject,
    mut v_inst_3401_: *mut crate::leanh::LeanObject,
    mut v_m_3402_: *mut crate::leanh::LeanObject,
    mut v_a_3403_: *mut crate::leanh::LeanObject,
    mut v_fallback_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3405_ = l_Std_DHashMap_Raw_getD___redArg(
        v_inst_3400_,
        v_inst_3401_,
        v_m_3402_,
        v_a_3403_,
        v_fallback_3404_,
    );
    crate::leanh::lean_dec(v_fallback_3404_);
    crate::leanh::lean_dec_ref(v_m_3402_);
    return v_res_3405_;
}
pub unsafe fn l_Std_DHashMap_Raw_getD(
    mut v_00_u03b1_3406_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3407_: *mut crate::leanh::LeanObject,
    mut v_inst_3408_: *mut crate::leanh::LeanObject,
    mut v_inst_3409_: *mut crate::leanh::LeanObject,
    mut v_inst_3410_: *mut crate::leanh::LeanObject,
    mut v_m_3411_: *mut crate::leanh::LeanObject,
    mut v_a_3412_: *mut crate::leanh::LeanObject,
    mut v_fallback_3413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    v_buckets_3414_ = crate::leanh::lean_ctor_get(v_m_3411_, 1);
    v___x_3415_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3416_ = lean_array_get_size(v_buckets_3414_);
    v___x_3417_ = lean_nat_dec_lt(v___x_3415_, v___x_3416_);
    if v___x_3417_ == 0 {
        crate::leanh::lean_dec(v_a_3412_);
        crate::leanh::lean_dec_ref(v_inst_3409_);
        crate::leanh::lean_dec_ref(v_inst_3408_);
        crate::leanh::lean_inc(v_fallback_3413_);
        return v_fallback_3413_;
    } else {
        let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3418_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
            v_inst_3408_,
            v_inst_3409_,
            v_m_3411_,
            v_a_3412_,
            v_fallback_3413_,
        );
        return v___x_3418_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getD___boxed(
    mut v_00_u03b1_3419_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3420_: *mut crate::leanh::LeanObject,
    mut v_inst_3421_: *mut crate::leanh::LeanObject,
    mut v_inst_3422_: *mut crate::leanh::LeanObject,
    mut v_inst_3423_: *mut crate::leanh::LeanObject,
    mut v_m_3424_: *mut crate::leanh::LeanObject,
    mut v_a_3425_: *mut crate::leanh::LeanObject,
    mut v_fallback_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Std_DHashMap_Raw_getD(
        v_00_u03b1_3419_,
        v_00_u03b2_3420_,
        v_inst_3421_,
        v_inst_3422_,
        v_inst_3423_,
        v_m_3424_,
        v_a_3425_,
        v_fallback_3426_,
    );
    crate::leanh::lean_dec(v_fallback_3426_);
    crate::leanh::lean_dec_ref(v_m_3424_);
    return v_res_3427_;
}
pub unsafe fn l_Std_DHashMap_Raw_get_x21___redArg(
    mut v_inst_3428_: *mut crate::leanh::LeanObject,
    mut v_inst_3429_: *mut crate::leanh::LeanObject,
    mut v_m_3430_: *mut crate::leanh::LeanObject,
    mut v_a_3431_: *mut crate::leanh::LeanObject,
    mut v_inst_3432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    v_buckets_3433_ = crate::leanh::lean_ctor_get(v_m_3430_, 1);
    v___x_3434_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3435_ = lean_array_get_size(v_buckets_3433_);
    v___x_3436_ = lean_nat_dec_lt(v___x_3434_, v___x_3435_);
    if v___x_3436_ == 0 {
        crate::leanh::lean_dec(v_a_3431_);
        crate::leanh::lean_dec_ref(v_inst_3429_);
        crate::leanh::lean_dec_ref(v_inst_3428_);
        crate::leanh::lean_inc(v_inst_3432_);
        return v_inst_3432_;
    } else {
        let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3437_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
            v_inst_3428_,
            v_inst_3429_,
            v_m_3430_,
            v_a_3431_,
            v_inst_3432_,
        );
        return v___x_3437_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_get_x21___redArg___boxed(
    mut v_inst_3438_: *mut crate::leanh::LeanObject,
    mut v_inst_3439_: *mut crate::leanh::LeanObject,
    mut v_m_3440_: *mut crate::leanh::LeanObject,
    mut v_a_3441_: *mut crate::leanh::LeanObject,
    mut v_inst_3442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3443_ = l_Std_DHashMap_Raw_get_x21___redArg(
        v_inst_3438_,
        v_inst_3439_,
        v_m_3440_,
        v_a_3441_,
        v_inst_3442_,
    );
    crate::leanh::lean_dec(v_inst_3442_);
    crate::leanh::lean_dec_ref(v_m_3440_);
    return v_res_3443_;
}
pub unsafe fn l_Std_DHashMap_Raw_get_x21(
    mut v_00_u03b1_3444_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3445_: *mut crate::leanh::LeanObject,
    mut v_inst_3446_: *mut crate::leanh::LeanObject,
    mut v_inst_3447_: *mut crate::leanh::LeanObject,
    mut v_inst_3448_: *mut crate::leanh::LeanObject,
    mut v_m_3449_: *mut crate::leanh::LeanObject,
    mut v_a_3450_: *mut crate::leanh::LeanObject,
    mut v_inst_3451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: u8 = 0;
    v_buckets_3452_ = crate::leanh::lean_ctor_get(v_m_3449_, 1);
    v___x_3453_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3454_ = lean_array_get_size(v_buckets_3452_);
    v___x_3455_ = lean_nat_dec_lt(v___x_3453_, v___x_3454_);
    if v___x_3455_ == 0 {
        crate::leanh::lean_dec(v_a_3450_);
        crate::leanh::lean_dec_ref(v_inst_3447_);
        crate::leanh::lean_dec_ref(v_inst_3446_);
        crate::leanh::lean_inc(v_inst_3451_);
        return v_inst_3451_;
    } else {
        let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
            v_inst_3446_,
            v_inst_3447_,
            v_m_3449_,
            v_a_3450_,
            v_inst_3451_,
        );
        return v___x_3456_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_get_x21___boxed(
    mut v_00_u03b1_3457_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3458_: *mut crate::leanh::LeanObject,
    mut v_inst_3459_: *mut crate::leanh::LeanObject,
    mut v_inst_3460_: *mut crate::leanh::LeanObject,
    mut v_inst_3461_: *mut crate::leanh::LeanObject,
    mut v_m_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
    mut v_inst_3464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3465_ = l_Std_DHashMap_Raw_get_x21(
        v_00_u03b1_3457_,
        v_00_u03b2_3458_,
        v_inst_3459_,
        v_inst_3460_,
        v_inst_3461_,
        v_m_3462_,
        v_a_3463_,
        v_inst_3464_,
    );
    crate::leanh::lean_dec(v_inst_3464_);
    crate::leanh::lean_dec_ref(v_m_3462_);
    return v_res_3465_;
}
pub unsafe fn l_Std_DHashMap_Raw_erase___redArg(
    mut v_inst_3466_: *mut crate::leanh::LeanObject,
    mut v_inst_3467_: *mut crate::leanh::LeanObject,
    mut v_m_3468_: *mut crate::leanh::LeanObject,
    mut v_a_3469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: u8 = 0;
    v_buckets_3470_ = crate::leanh::lean_ctor_get(v_m_3468_, 1);
    v___x_3471_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3472_ = lean_array_get_size(v_buckets_3470_);
    v___x_3473_ = lean_nat_dec_lt(v___x_3471_, v___x_3472_);
    if v___x_3473_ == 0 {
        crate::leanh::lean_dec(v_a_3469_);
        crate::leanh::lean_dec_ref(v_inst_3467_);
        crate::leanh::lean_dec_ref(v_inst_3466_);
        return v_m_3468_;
    } else {
        let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3474_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
            v_inst_3466_,
            v_inst_3467_,
            v_m_3468_,
            v_a_3469_,
        );
        return v___x_3474_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_erase(
    mut v_00_u03b1_3475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3476_: *mut crate::leanh::LeanObject,
    mut v_inst_3477_: *mut crate::leanh::LeanObject,
    mut v_inst_3478_: *mut crate::leanh::LeanObject,
    mut v_m_3479_: *mut crate::leanh::LeanObject,
    mut v_a_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: u8 = 0;
    v_buckets_3481_ = crate::leanh::lean_ctor_get(v_m_3479_, 1);
    v___x_3482_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3483_ = lean_array_get_size(v_buckets_3481_);
    v___x_3484_ = lean_nat_dec_lt(v___x_3482_, v___x_3483_);
    if v___x_3484_ == 0 {
        crate::leanh::lean_dec(v_a_3480_);
        crate::leanh::lean_dec_ref(v_inst_3478_);
        crate::leanh::lean_dec_ref(v_inst_3477_);
        return v_m_3479_;
    } else {
        let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3485_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
            v_inst_3477_,
            v_inst_3478_,
            v_m_3479_,
            v_a_3480_,
        );
        return v___x_3485_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x3f___redArg(
    mut v_inst_3486_: *mut crate::leanh::LeanObject,
    mut v_inst_3487_: *mut crate::leanh::LeanObject,
    mut v_m_3488_: *mut crate::leanh::LeanObject,
    mut v_a_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: u8 = 0;
    v_buckets_3490_ = crate::leanh::lean_ctor_get(v_m_3488_, 1);
    v___x_3491_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3492_ = lean_array_get_size(v_buckets_3490_);
    v___x_3493_ = lean_nat_dec_lt(v___x_3491_, v___x_3492_);
    if v___x_3493_ == 0 {
        let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3489_);
        crate::leanh::lean_dec_ref(v_inst_3487_);
        crate::leanh::lean_dec_ref(v_inst_3486_);
        v___x_3494_ = crate::leanh::lean_box(0);
        return v___x_3494_;
    } else {
        let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_inst_3486_,
            v_inst_3487_,
            v_m_3488_,
            v_a_3489_,
        );
        return v___x_3495_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(
    mut v_inst_3496_: *mut crate::leanh::LeanObject,
    mut v_inst_3497_: *mut crate::leanh::LeanObject,
    mut v_m_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3500_ =
        l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_3496_, v_inst_3497_, v_m_3498_, v_a_3499_);
    crate::leanh::lean_dec_ref(v_m_3498_);
    return v_res_3500_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x3f(
    mut v_00_u03b1_3501_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3502_: *mut crate::leanh::LeanObject,
    mut v_inst_3503_: *mut crate::leanh::LeanObject,
    mut v_inst_3504_: *mut crate::leanh::LeanObject,
    mut v_m_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: u8 = 0;
    v_buckets_3507_ = crate::leanh::lean_ctor_get(v_m_3505_, 1);
    v___x_3508_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3509_ = lean_array_get_size(v_buckets_3507_);
    v___x_3510_ = lean_nat_dec_lt(v___x_3508_, v___x_3509_);
    if v___x_3510_ == 0 {
        let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3506_);
        crate::leanh::lean_dec_ref(v_inst_3504_);
        crate::leanh::lean_dec_ref(v_inst_3503_);
        v___x_3511_ = crate::leanh::lean_box(0);
        return v___x_3511_;
    } else {
        let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_inst_3503_,
            v_inst_3504_,
            v_m_3505_,
            v_a_3506_,
        );
        return v___x_3512_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x3f___boxed(
    mut v_00_u03b1_3513_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3514_: *mut crate::leanh::LeanObject,
    mut v_inst_3515_: *mut crate::leanh::LeanObject,
    mut v_inst_3516_: *mut crate::leanh::LeanObject,
    mut v_m_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3519_ = l_Std_DHashMap_Raw_Const_get_x3f(
        v_00_u03b1_3513_,
        v_00_u03b2_3514_,
        v_inst_3515_,
        v_inst_3516_,
        v_m_3517_,
        v_a_3518_,
    );
    crate::leanh::lean_dec_ref(v_m_3517_);
    return v_res_3519_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get___redArg(
    mut v_inst_3520_: *mut crate::leanh::LeanObject,
    mut v_inst_3521_: *mut crate::leanh::LeanObject,
    mut v_m_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_3520_,
        v_inst_3521_,
        v_m_3522_,
        v_a_3523_,
    );
    return v___x_3524_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get___redArg___boxed(
    mut v_inst_3525_: *mut crate::leanh::LeanObject,
    mut v_inst_3526_: *mut crate::leanh::LeanObject,
    mut v_m_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3529_ =
        l_Std_DHashMap_Raw_Const_get___redArg(v_inst_3525_, v_inst_3526_, v_m_3527_, v_a_3528_);
    crate::leanh::lean_dec_ref(v_m_3527_);
    return v_res_3529_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get(
    mut v_00_u03b1_3530_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3531_: *mut crate::leanh::LeanObject,
    mut v_inst_3532_: *mut crate::leanh::LeanObject,
    mut v_inst_3533_: *mut crate::leanh::LeanObject,
    mut v_m_3534_: *mut crate::leanh::LeanObject,
    mut v_a_3535_: *mut crate::leanh::LeanObject,
    mut v_h_3536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_3532_,
        v_inst_3533_,
        v_m_3534_,
        v_a_3535_,
    );
    return v___x_3537_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get___boxed(
    mut v_00_u03b1_3538_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3539_: *mut crate::leanh::LeanObject,
    mut v_inst_3540_: *mut crate::leanh::LeanObject,
    mut v_inst_3541_: *mut crate::leanh::LeanObject,
    mut v_m_3542_: *mut crate::leanh::LeanObject,
    mut v_a_3543_: *mut crate::leanh::LeanObject,
    mut v_h_3544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3545_ = l_Std_DHashMap_Raw_Const_get(
        v_00_u03b1_3538_,
        v_00_u03b2_3539_,
        v_inst_3540_,
        v_inst_3541_,
        v_m_3542_,
        v_a_3543_,
        v_h_3544_,
    );
    crate::leanh::lean_dec_ref(v_m_3542_);
    return v_res_3545_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getD___redArg(
    mut v_inst_3546_: *mut crate::leanh::LeanObject,
    mut v_inst_3547_: *mut crate::leanh::LeanObject,
    mut v_m_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_fallback_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: u8 = 0;
    v_buckets_3551_ = crate::leanh::lean_ctor_get(v_m_3548_, 1);
    v___x_3552_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3553_ = lean_array_get_size(v_buckets_3551_);
    v___x_3554_ = lean_nat_dec_lt(v___x_3552_, v___x_3553_);
    if v___x_3554_ == 0 {
        crate::leanh::lean_dec(v_a_3549_);
        crate::leanh::lean_dec_ref(v_inst_3547_);
        crate::leanh::lean_dec_ref(v_inst_3546_);
        crate::leanh::lean_inc(v_fallback_3550_);
        return v_fallback_3550_;
    } else {
        let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
            v_inst_3546_,
            v_inst_3547_,
            v_m_3548_,
            v_a_3549_,
            v_fallback_3550_,
        );
        return v___x_3555_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getD___redArg___boxed(
    mut v_inst_3556_: *mut crate::leanh::LeanObject,
    mut v_inst_3557_: *mut crate::leanh::LeanObject,
    mut v_m_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
    mut v_fallback_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l_Std_DHashMap_Raw_Const_getD___redArg(
        v_inst_3556_,
        v_inst_3557_,
        v_m_3558_,
        v_a_3559_,
        v_fallback_3560_,
    );
    crate::leanh::lean_dec(v_fallback_3560_);
    crate::leanh::lean_dec_ref(v_m_3558_);
    return v_res_3561_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getD(
    mut v_00_u03b1_3562_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3563_: *mut crate::leanh::LeanObject,
    mut v_inst_3564_: *mut crate::leanh::LeanObject,
    mut v_inst_3565_: *mut crate::leanh::LeanObject,
    mut v_m_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
    mut v_fallback_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    v_buckets_3569_ = crate::leanh::lean_ctor_get(v_m_3566_, 1);
    v___x_3570_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3571_ = lean_array_get_size(v_buckets_3569_);
    v___x_3572_ = lean_nat_dec_lt(v___x_3570_, v___x_3571_);
    if v___x_3572_ == 0 {
        crate::leanh::lean_dec(v_a_3567_);
        crate::leanh::lean_dec_ref(v_inst_3565_);
        crate::leanh::lean_dec_ref(v_inst_3564_);
        crate::leanh::lean_inc(v_fallback_3568_);
        return v_fallback_3568_;
    } else {
        let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
            v_inst_3564_,
            v_inst_3565_,
            v_m_3566_,
            v_a_3567_,
            v_fallback_3568_,
        );
        return v___x_3573_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getD___boxed(
    mut v_00_u03b1_3574_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3575_: *mut crate::leanh::LeanObject,
    mut v_inst_3576_: *mut crate::leanh::LeanObject,
    mut v_inst_3577_: *mut crate::leanh::LeanObject,
    mut v_m_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_fallback_3580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Std_DHashMap_Raw_Const_getD(
        v_00_u03b1_3574_,
        v_00_u03b2_3575_,
        v_inst_3576_,
        v_inst_3577_,
        v_m_3578_,
        v_a_3579_,
        v_fallback_3580_,
    );
    crate::leanh::lean_dec(v_fallback_3580_);
    crate::leanh::lean_dec_ref(v_m_3578_);
    return v_res_3581_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x21___redArg(
    mut v_inst_3582_: *mut crate::leanh::LeanObject,
    mut v_inst_3583_: *mut crate::leanh::LeanObject,
    mut v_inst_3584_: *mut crate::leanh::LeanObject,
    mut v_m_3585_: *mut crate::leanh::LeanObject,
    mut v_a_3586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    v_buckets_3587_ = crate::leanh::lean_ctor_get(v_m_3585_, 1);
    v___x_3588_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3589_ = lean_array_get_size(v_buckets_3587_);
    v___x_3590_ = lean_nat_dec_lt(v___x_3588_, v___x_3589_);
    if v___x_3590_ == 0 {
        crate::leanh::lean_dec(v_a_3586_);
        crate::leanh::lean_dec_ref(v_inst_3583_);
        crate::leanh::lean_dec_ref(v_inst_3582_);
        crate::leanh::lean_inc(v_inst_3584_);
        return v_inst_3584_;
    } else {
        let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
            v_inst_3582_,
            v_inst_3583_,
            v_inst_3584_,
            v_m_3585_,
            v_a_3586_,
        );
        return v___x_3591_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(
    mut v_inst_3592_: *mut crate::leanh::LeanObject,
    mut v_inst_3593_: *mut crate::leanh::LeanObject,
    mut v_inst_3594_: *mut crate::leanh::LeanObject,
    mut v_m_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(
        v_inst_3592_,
        v_inst_3593_,
        v_inst_3594_,
        v_m_3595_,
        v_a_3596_,
    );
    crate::leanh::lean_dec_ref(v_m_3595_);
    crate::leanh::lean_dec(v_inst_3594_);
    return v_res_3597_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x21(
    mut v_00_u03b1_3598_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3599_: *mut crate::leanh::LeanObject,
    mut v_inst_3600_: *mut crate::leanh::LeanObject,
    mut v_inst_3601_: *mut crate::leanh::LeanObject,
    mut v_inst_3602_: *mut crate::leanh::LeanObject,
    mut v_m_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: u8 = 0;
    v_buckets_3605_ = crate::leanh::lean_ctor_get(v_m_3603_, 1);
    v___x_3606_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3607_ = lean_array_get_size(v_buckets_3605_);
    v___x_3608_ = lean_nat_dec_lt(v___x_3606_, v___x_3607_);
    if v___x_3608_ == 0 {
        crate::leanh::lean_dec(v_a_3604_);
        crate::leanh::lean_dec_ref(v_inst_3601_);
        crate::leanh::lean_dec_ref(v_inst_3600_);
        crate::leanh::lean_inc(v_inst_3602_);
        return v_inst_3602_;
    } else {
        let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
            v_inst_3600_,
            v_inst_3601_,
            v_inst_3602_,
            v_m_3603_,
            v_a_3604_,
        );
        return v___x_3609_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x21___boxed(
    mut v_00_u03b1_3610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3611_: *mut crate::leanh::LeanObject,
    mut v_inst_3612_: *mut crate::leanh::LeanObject,
    mut v_inst_3613_: *mut crate::leanh::LeanObject,
    mut v_inst_3614_: *mut crate::leanh::LeanObject,
    mut v_m_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3617_ = l_Std_DHashMap_Raw_Const_get_x21(
        v_00_u03b1_3610_,
        v_00_u03b2_3611_,
        v_inst_3612_,
        v_inst_3613_,
        v_inst_3614_,
        v_m_3615_,
        v_a_3616_,
    );
    crate::leanh::lean_dec_ref(v_m_3615_);
    crate::leanh::lean_dec(v_inst_3614_);
    return v_res_3617_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(
    mut v_inst_3618_: *mut crate::leanh::LeanObject,
    mut v_inst_3619_: *mut crate::leanh::LeanObject,
    mut v_m_3620_: *mut crate::leanh::LeanObject,
    mut v_a_3621_: *mut crate::leanh::LeanObject,
    mut v_b_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: u8 = 0;
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u64 = 0;
    let mut v___x_3632_: u64 = 0;
    let mut v___x_3633_: u64 = 0;
    let mut v___x_3634_: u64 = 0;
    let mut v_fold_3635_: u64 = 0;
    let mut v___x_3636_: u64 = 0;
    let mut v___x_3637_: u64 = 0;
    let mut v___x_3638_: u64 = 0;
    let mut v___x_3639_: usize = 0;
    let mut v___x_3640_: usize = 0;
    let mut v___x_3641_: usize = 0;
    let mut v___x_3642_: usize = 0;
    let mut v___x_3643_: usize = 0;
    let mut v_bkt_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: u8 = 0;
    let mut v_val_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut v_unused_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3623_ = crate::leanh::lean_ctor_get(v_m_3620_, 0);
                v_buckets_3624_ = crate::leanh::lean_ctor_get(v_m_3620_, 1);
                v___x_3625_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3626_ = lean_array_get_size(v_buckets_3624_);
                v___x_3627_ = lean_nat_dec_lt(v___x_3625_, v___x_3626_);
                if v___x_3627_ == 0 {
                    crate::leanh::lean_dec(v_b_3622_);
                    crate::leanh::lean_dec(v_a_3621_);
                    crate::leanh::lean_dec_ref(v_inst_3619_);
                    crate::leanh::lean_dec_ref(v_inst_3618_);
                    v___x_3628_ = crate::leanh::lean_box(0);
                    v___x_3629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3629_, 0, v___x_3628_);
                    crate::leanh::lean_ctor_set(v___x_3629_, 1, v_m_3620_);
                    return v___x_3629_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_3619_);
                    crate::leanh::lean_inc_n(v_a_3621_, 2);
                    v___x_3630_ = crate::leanh::lean_apply_1(v_inst_3619_, v_a_3621_);
                    v___x_3631_ = 32u64;
                    v___x_3632_ = crate::leanh::lean_unbox_uint64(v___x_3630_);
                    v___x_3633_ = lean_uint64_shift_right(v___x_3632_, v___x_3631_);
                    v___x_3634_ = crate::leanh::lean_unbox_uint64(v___x_3630_);
                    crate::leanh::lean_dec_ref(v___x_3630_);
                    v_fold_3635_ = lean_uint64_xor(v___x_3634_, v___x_3633_);
                    v___x_3636_ = 16u64;
                    v___x_3637_ = lean_uint64_shift_right(v_fold_3635_, v___x_3636_);
                    v___x_3638_ = lean_uint64_xor(v_fold_3635_, v___x_3637_);
                    v___x_3639_ = lean_uint64_to_usize(v___x_3638_);
                    v___x_3640_ = lean_usize_of_nat(v___x_3626_);
                    v___x_3641_ = 1usize;
                    v___x_3642_ = lean_usize_sub(v___x_3640_, v___x_3641_);
                    v___x_3643_ = lean_usize_land(v___x_3639_, v___x_3642_);
                    v_bkt_3644_ = lean_array_uget_borrowed(v_buckets_3624_, v___x_3643_);
                    crate::leanh::lean_inc(v_bkt_3644_);
                    v___x_3645_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_3618_,
                        v_a_3621_,
                        v_bkt_3644_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3645_) == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_3624_);
                        crate::leanh::lean_inc(v_size_3623_);
                        v_isSharedCheck_3668_ = (!crate::leanh::lean_is_exclusive(v_m_3620_)) as u8;
                        if v_isSharedCheck_3668_ == 0 {
                            v_unused_3669_ = crate::leanh::lean_ctor_get(v_m_3620_, 1);
                            crate::leanh::lean_dec(v_unused_3669_);
                            v_unused_3670_ = crate::leanh::lean_ctor_get(v_m_3620_, 0);
                            crate::leanh::lean_dec(v_unused_3670_);
                            v___x_3647_ = v_m_3620_;
                            v_isShared_3648_ = v_isSharedCheck_3668_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_3620_);
                            v___x_3647_ = crate::leanh::lean_box(0);
                            v_isShared_3648_ = v_isSharedCheck_3668_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3622_);
                        crate::leanh::lean_dec(v_a_3621_);
                        crate::leanh::lean_dec_ref(v_inst_3619_);
                        v___x_3671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3671_, 0, v___x_3645_);
                        crate::leanh::lean_ctor_set(v___x_3671_, 1, v_m_3620_);
                        return v___x_3671_;
                    }
                }
            }
            1 => {
                v___x_3649_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3650_ = lean_nat_add(v_size_3623_, v___x_3649_);
                crate::leanh::lean_dec(v_size_3623_);
                crate::leanh::lean_inc(v_bkt_3644_);
                v___x_3651_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3651_, 0, v_a_3621_);
                crate::leanh::lean_ctor_set(v___x_3651_, 1, v_b_3622_);
                crate::leanh::lean_ctor_set(v___x_3651_, 2, v_bkt_3644_);
                v_buckets_x27_3652_ = lean_array_uset(v_buckets_3624_, v___x_3643_, v___x_3651_);
                v___x_3653_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3654_ = lean_nat_mul(v_size_x27_3650_, v___x_3653_);
                v___x_3655_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3656_ = lean_nat_div(v___x_3654_, v___x_3655_);
                crate::leanh::lean_dec(v___x_3654_);
                v___x_3657_ = lean_array_get_size(v_buckets_x27_3652_);
                v___x_3658_ = lean_nat_dec_le(v___x_3656_, v___x_3657_);
                crate::leanh::lean_dec(v___x_3656_);
                if v___x_3658_ == 0 {
                    v_val_3659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3619_,
                        v_buckets_x27_3652_,
                    );
                    if v_isShared_3648_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3647_, 1, v_val_3659_);
                        crate::leanh::lean_ctor_set(v___x_3647_, 0, v_size_x27_3650_);
                        v___x_3661_ = v___x_3647_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_size_x27_3650_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_val_3659_);
                        v___x_3661_ = v_reuseFailAlloc_3663_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_3619_);
                    if v_isShared_3648_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3647_, 1, v_buckets_x27_3652_);
                        crate::leanh::lean_ctor_set(v___x_3647_, 0, v_size_x27_3650_);
                        v___x_3665_ = v___x_3647_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_size_x27_3650_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_buckets_x27_3652_);
                        v___x_3665_ = v_reuseFailAlloc_3667_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3662_, 0, v___x_3645_);
                crate::leanh::lean_ctor_set(v___x_3662_, 1, v___x_3661_);
                return v___x_3662_;
            }
            3 => {
                v___x_3666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3666_, 0, v___x_3645_);
                crate::leanh::lean_ctor_set(v___x_3666_, 1, v___x_3665_);
                return v___x_3666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_3672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3673_: *mut crate::leanh::LeanObject,
    mut v_inst_3674_: *mut crate::leanh::LeanObject,
    mut v_inst_3675_: *mut crate::leanh::LeanObject,
    mut v_m_3676_: *mut crate::leanh::LeanObject,
    mut v_a_3677_: *mut crate::leanh::LeanObject,
    mut v_b_3678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: u8 = 0;
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: u64 = 0;
    let mut v___x_3688_: u64 = 0;
    let mut v___x_3689_: u64 = 0;
    let mut v___x_3690_: u64 = 0;
    let mut v_fold_3691_: u64 = 0;
    let mut v___x_3692_: u64 = 0;
    let mut v___x_3693_: u64 = 0;
    let mut v___x_3694_: u64 = 0;
    let mut v___x_3695_: usize = 0;
    let mut v___x_3696_: usize = 0;
    let mut v___x_3697_: usize = 0;
    let mut v___x_3698_: usize = 0;
    let mut v___x_3699_: usize = 0;
    let mut v_bkt_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v_val_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut v_unused_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3679_ = crate::leanh::lean_ctor_get(v_m_3676_, 0);
                v_buckets_3680_ = crate::leanh::lean_ctor_get(v_m_3676_, 1);
                v___x_3681_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3682_ = lean_array_get_size(v_buckets_3680_);
                v___x_3683_ = lean_nat_dec_lt(v___x_3681_, v___x_3682_);
                if v___x_3683_ == 0 {
                    crate::leanh::lean_dec(v_b_3678_);
                    crate::leanh::lean_dec(v_a_3677_);
                    crate::leanh::lean_dec_ref(v_inst_3675_);
                    crate::leanh::lean_dec_ref(v_inst_3674_);
                    v___x_3684_ = crate::leanh::lean_box(0);
                    v___x_3685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3685_, 0, v___x_3684_);
                    crate::leanh::lean_ctor_set(v___x_3685_, 1, v_m_3676_);
                    return v___x_3685_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_3675_);
                    crate::leanh::lean_inc_n(v_a_3677_, 2);
                    v___x_3686_ = crate::leanh::lean_apply_1(v_inst_3675_, v_a_3677_);
                    v___x_3687_ = 32u64;
                    v___x_3688_ = crate::leanh::lean_unbox_uint64(v___x_3686_);
                    v___x_3689_ = lean_uint64_shift_right(v___x_3688_, v___x_3687_);
                    v___x_3690_ = crate::leanh::lean_unbox_uint64(v___x_3686_);
                    crate::leanh::lean_dec_ref(v___x_3686_);
                    v_fold_3691_ = lean_uint64_xor(v___x_3690_, v___x_3689_);
                    v___x_3692_ = 16u64;
                    v___x_3693_ = lean_uint64_shift_right(v_fold_3691_, v___x_3692_);
                    v___x_3694_ = lean_uint64_xor(v_fold_3691_, v___x_3693_);
                    v___x_3695_ = lean_uint64_to_usize(v___x_3694_);
                    v___x_3696_ = lean_usize_of_nat(v___x_3682_);
                    v___x_3697_ = 1usize;
                    v___x_3698_ = lean_usize_sub(v___x_3696_, v___x_3697_);
                    v___x_3699_ = lean_usize_land(v___x_3695_, v___x_3698_);
                    v_bkt_3700_ = lean_array_uget_borrowed(v_buckets_3680_, v___x_3699_);
                    crate::leanh::lean_inc(v_bkt_3700_);
                    v___x_3701_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_3674_,
                        v_a_3677_,
                        v_bkt_3700_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3701_) == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_3680_);
                        crate::leanh::lean_inc(v_size_3679_);
                        v_isSharedCheck_3724_ = (!crate::leanh::lean_is_exclusive(v_m_3676_)) as u8;
                        if v_isSharedCheck_3724_ == 0 {
                            v_unused_3725_ = crate::leanh::lean_ctor_get(v_m_3676_, 1);
                            crate::leanh::lean_dec(v_unused_3725_);
                            v_unused_3726_ = crate::leanh::lean_ctor_get(v_m_3676_, 0);
                            crate::leanh::lean_dec(v_unused_3726_);
                            v___x_3703_ = v_m_3676_;
                            v_isShared_3704_ = v_isSharedCheck_3724_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_3676_);
                            v___x_3703_ = crate::leanh::lean_box(0);
                            v_isShared_3704_ = v_isSharedCheck_3724_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_3678_);
                        crate::leanh::lean_dec(v_a_3677_);
                        crate::leanh::lean_dec_ref(v_inst_3675_);
                        v___x_3727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3727_, 0, v___x_3701_);
                        crate::leanh::lean_ctor_set(v___x_3727_, 1, v_m_3676_);
                        return v___x_3727_;
                    }
                }
            }
            1 => {
                v___x_3705_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3706_ = lean_nat_add(v_size_3679_, v___x_3705_);
                crate::leanh::lean_dec(v_size_3679_);
                crate::leanh::lean_inc(v_bkt_3700_);
                v___x_3707_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3707_, 0, v_a_3677_);
                crate::leanh::lean_ctor_set(v___x_3707_, 1, v_b_3678_);
                crate::leanh::lean_ctor_set(v___x_3707_, 2, v_bkt_3700_);
                v_buckets_x27_3708_ = lean_array_uset(v_buckets_3680_, v___x_3699_, v___x_3707_);
                v___x_3709_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3710_ = lean_nat_mul(v_size_x27_3706_, v___x_3709_);
                v___x_3711_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3712_ = lean_nat_div(v___x_3710_, v___x_3711_);
                crate::leanh::lean_dec(v___x_3710_);
                v___x_3713_ = lean_array_get_size(v_buckets_x27_3708_);
                v___x_3714_ = lean_nat_dec_le(v___x_3712_, v___x_3713_);
                crate::leanh::lean_dec(v___x_3712_);
                if v___x_3714_ == 0 {
                    v_val_3715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3675_,
                        v_buckets_x27_3708_,
                    );
                    if v_isShared_3704_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3703_, 1, v_val_3715_);
                        crate::leanh::lean_ctor_set(v___x_3703_, 0, v_size_x27_3706_);
                        v___x_3717_ = v___x_3703_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3719_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_size_x27_3706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_val_3715_);
                        v___x_3717_ = v_reuseFailAlloc_3719_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_3675_);
                    if v_isShared_3704_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3703_, 1, v_buckets_x27_3708_);
                        crate::leanh::lean_ctor_set(v___x_3703_, 0, v_size_x27_3706_);
                        v___x_3721_ = v___x_3703_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_size_x27_3706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_buckets_x27_3708_);
                        v___x_3721_ = v_reuseFailAlloc_3723_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3701_);
                crate::leanh::lean_ctor_set(v___x_3718_, 1, v___x_3717_);
                return v___x_3718_;
            }
            3 => {
                v___x_3722_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3722_, 0, v___x_3701_);
                crate::leanh::lean_ctor_set(v___x_3722_, 1, v___x_3721_);
                return v___x_3722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x3f___redArg(
    mut v_inst_3728_: *mut crate::leanh::LeanObject,
    mut v_inst_3729_: *mut crate::leanh::LeanObject,
    mut v_m_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: u8 = 0;
    v_buckets_3732_ = crate::leanh::lean_ctor_get(v_m_3730_, 1);
    v___x_3733_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3734_ = lean_array_get_size(v_buckets_3732_);
    v___x_3735_ = lean_nat_dec_lt(v___x_3733_, v___x_3734_);
    if v___x_3735_ == 0 {
        let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3731_);
        crate::leanh::lean_dec_ref(v_inst_3729_);
        crate::leanh::lean_dec_ref(v_inst_3728_);
        v___x_3736_ = crate::leanh::lean_box(0);
        return v___x_3736_;
    } else {
        let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3737_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
            v_inst_3728_,
            v_inst_3729_,
            v_m_3730_,
            v_a_3731_,
        );
        return v___x_3737_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(
    mut v_inst_3738_: *mut crate::leanh::LeanObject,
    mut v_inst_3739_: *mut crate::leanh::LeanObject,
    mut v_m_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3742_ =
        l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_3738_, v_inst_3739_, v_m_3740_, v_a_3741_);
    crate::leanh::lean_dec_ref(v_m_3740_);
    return v_res_3742_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x3f(
    mut v_00_u03b1_3743_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3744_: *mut crate::leanh::LeanObject,
    mut v_inst_3745_: *mut crate::leanh::LeanObject,
    mut v_inst_3746_: *mut crate::leanh::LeanObject,
    mut v_m_3747_: *mut crate::leanh::LeanObject,
    mut v_a_3748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    v_buckets_3749_ = crate::leanh::lean_ctor_get(v_m_3747_, 1);
    v___x_3750_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3751_ = lean_array_get_size(v_buckets_3749_);
    v___x_3752_ = lean_nat_dec_lt(v___x_3750_, v___x_3751_);
    if v___x_3752_ == 0 {
        let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3748_);
        crate::leanh::lean_dec_ref(v_inst_3746_);
        crate::leanh::lean_dec_ref(v_inst_3745_);
        v___x_3753_ = crate::leanh::lean_box(0);
        return v___x_3753_;
    } else {
        let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3754_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
            v_inst_3745_,
            v_inst_3746_,
            v_m_3747_,
            v_a_3748_,
        );
        return v___x_3754_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x3f___boxed(
    mut v_00_u03b1_3755_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3756_: *mut crate::leanh::LeanObject,
    mut v_inst_3757_: *mut crate::leanh::LeanObject,
    mut v_inst_3758_: *mut crate::leanh::LeanObject,
    mut v_m_3759_: *mut crate::leanh::LeanObject,
    mut v_a_3760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Std_DHashMap_Raw_getKey_x3f(
        v_00_u03b1_3755_,
        v_00_u03b2_3756_,
        v_inst_3757_,
        v_inst_3758_,
        v_m_3759_,
        v_a_3760_,
    );
    crate::leanh::lean_dec_ref(v_m_3759_);
    return v_res_3761_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey___redArg(
    mut v_inst_3762_: *mut crate::leanh::LeanObject,
    mut v_inst_3763_: *mut crate::leanh::LeanObject,
    mut v_m_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3762_,
        v_inst_3763_,
        v_m_3764_,
        v_a_3765_,
    );
    return v___x_3766_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey___redArg___boxed(
    mut v_inst_3767_: *mut crate::leanh::LeanObject,
    mut v_inst_3768_: *mut crate::leanh::LeanObject,
    mut v_m_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ =
        l_Std_DHashMap_Raw_getKey___redArg(v_inst_3767_, v_inst_3768_, v_m_3769_, v_a_3770_);
    crate::leanh::lean_dec_ref(v_m_3769_);
    return v_res_3771_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey(
    mut v_00_u03b1_3772_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3773_: *mut crate::leanh::LeanObject,
    mut v_inst_3774_: *mut crate::leanh::LeanObject,
    mut v_inst_3775_: *mut crate::leanh::LeanObject,
    mut v_m_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_h_3778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3774_,
        v_inst_3775_,
        v_m_3776_,
        v_a_3777_,
    );
    return v___x_3779_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey___boxed(
    mut v_00_u03b1_3780_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3781_: *mut crate::leanh::LeanObject,
    mut v_inst_3782_: *mut crate::leanh::LeanObject,
    mut v_inst_3783_: *mut crate::leanh::LeanObject,
    mut v_m_3784_: *mut crate::leanh::LeanObject,
    mut v_a_3785_: *mut crate::leanh::LeanObject,
    mut v_h_3786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Std_DHashMap_Raw_getKey(
        v_00_u03b1_3780_,
        v_00_u03b2_3781_,
        v_inst_3782_,
        v_inst_3783_,
        v_m_3784_,
        v_a_3785_,
        v_h_3786_,
    );
    crate::leanh::lean_dec_ref(v_m_3784_);
    return v_res_3787_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKeyD___redArg(
    mut v_inst_3788_: *mut crate::leanh::LeanObject,
    mut v_inst_3789_: *mut crate::leanh::LeanObject,
    mut v_m_3790_: *mut crate::leanh::LeanObject,
    mut v_a_3791_: *mut crate::leanh::LeanObject,
    mut v_fallback_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    v_buckets_3793_ = crate::leanh::lean_ctor_get(v_m_3790_, 1);
    v___x_3794_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3795_ = lean_array_get_size(v_buckets_3793_);
    v___x_3796_ = lean_nat_dec_lt(v___x_3794_, v___x_3795_);
    if v___x_3796_ == 0 {
        crate::leanh::lean_dec(v_a_3791_);
        crate::leanh::lean_dec_ref(v_inst_3789_);
        crate::leanh::lean_dec_ref(v_inst_3788_);
        crate::leanh::lean_inc(v_fallback_3792_);
        return v_fallback_3792_;
    } else {
        let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3797_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
            v_inst_3788_,
            v_inst_3789_,
            v_m_3790_,
            v_a_3791_,
            v_fallback_3792_,
        );
        return v___x_3797_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKeyD___redArg___boxed(
    mut v_inst_3798_: *mut crate::leanh::LeanObject,
    mut v_inst_3799_: *mut crate::leanh::LeanObject,
    mut v_m_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_fallback_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Std_DHashMap_Raw_getKeyD___redArg(
        v_inst_3798_,
        v_inst_3799_,
        v_m_3800_,
        v_a_3801_,
        v_fallback_3802_,
    );
    crate::leanh::lean_dec(v_fallback_3802_);
    crate::leanh::lean_dec_ref(v_m_3800_);
    return v_res_3803_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKeyD(
    mut v_00_u03b1_3804_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3805_: *mut crate::leanh::LeanObject,
    mut v_inst_3806_: *mut crate::leanh::LeanObject,
    mut v_inst_3807_: *mut crate::leanh::LeanObject,
    mut v_m_3808_: *mut crate::leanh::LeanObject,
    mut v_a_3809_: *mut crate::leanh::LeanObject,
    mut v_fallback_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    v_buckets_3811_ = crate::leanh::lean_ctor_get(v_m_3808_, 1);
    v___x_3812_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3813_ = lean_array_get_size(v_buckets_3811_);
    v___x_3814_ = lean_nat_dec_lt(v___x_3812_, v___x_3813_);
    if v___x_3814_ == 0 {
        crate::leanh::lean_dec(v_a_3809_);
        crate::leanh::lean_dec_ref(v_inst_3807_);
        crate::leanh::lean_dec_ref(v_inst_3806_);
        crate::leanh::lean_inc(v_fallback_3810_);
        return v_fallback_3810_;
    } else {
        let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3815_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
            v_inst_3806_,
            v_inst_3807_,
            v_m_3808_,
            v_a_3809_,
            v_fallback_3810_,
        );
        return v___x_3815_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKeyD___boxed(
    mut v_00_u03b1_3816_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3817_: *mut crate::leanh::LeanObject,
    mut v_inst_3818_: *mut crate::leanh::LeanObject,
    mut v_inst_3819_: *mut crate::leanh::LeanObject,
    mut v_m_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
    mut v_fallback_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Std_DHashMap_Raw_getKeyD(
        v_00_u03b1_3816_,
        v_00_u03b2_3817_,
        v_inst_3818_,
        v_inst_3819_,
        v_m_3820_,
        v_a_3821_,
        v_fallback_3822_,
    );
    crate::leanh::lean_dec(v_fallback_3822_);
    crate::leanh::lean_dec_ref(v_m_3820_);
    return v_res_3823_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x21___redArg(
    mut v_inst_3824_: *mut crate::leanh::LeanObject,
    mut v_inst_3825_: *mut crate::leanh::LeanObject,
    mut v_inst_3826_: *mut crate::leanh::LeanObject,
    mut v_m_3827_: *mut crate::leanh::LeanObject,
    mut v_a_3828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: u8 = 0;
    v_buckets_3829_ = crate::leanh::lean_ctor_get(v_m_3827_, 1);
    v___x_3830_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3831_ = lean_array_get_size(v_buckets_3829_);
    v___x_3832_ = lean_nat_dec_lt(v___x_3830_, v___x_3831_);
    if v___x_3832_ == 0 {
        crate::leanh::lean_dec(v_a_3828_);
        crate::leanh::lean_dec_ref(v_inst_3825_);
        crate::leanh::lean_dec_ref(v_inst_3824_);
        crate::leanh::lean_inc(v_inst_3826_);
        return v_inst_3826_;
    } else {
        let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3833_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
            v_inst_3824_,
            v_inst_3825_,
            v_inst_3826_,
            v_m_3827_,
            v_a_3828_,
        );
        return v___x_3833_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(
    mut v_inst_3834_: *mut crate::leanh::LeanObject,
    mut v_inst_3835_: *mut crate::leanh::LeanObject,
    mut v_inst_3836_: *mut crate::leanh::LeanObject,
    mut v_m_3837_: *mut crate::leanh::LeanObject,
    mut v_a_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Std_DHashMap_Raw_getKey_x21___redArg(
        v_inst_3834_,
        v_inst_3835_,
        v_inst_3836_,
        v_m_3837_,
        v_a_3838_,
    );
    crate::leanh::lean_dec_ref(v_m_3837_);
    crate::leanh::lean_dec(v_inst_3836_);
    return v_res_3839_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x21(
    mut v_00_u03b1_3840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3841_: *mut crate::leanh::LeanObject,
    mut v_inst_3842_: *mut crate::leanh::LeanObject,
    mut v_inst_3843_: *mut crate::leanh::LeanObject,
    mut v_inst_3844_: *mut crate::leanh::LeanObject,
    mut v_m_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: u8 = 0;
    v_buckets_3847_ = crate::leanh::lean_ctor_get(v_m_3845_, 1);
    v___x_3848_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3849_ = lean_array_get_size(v_buckets_3847_);
    v___x_3850_ = lean_nat_dec_lt(v___x_3848_, v___x_3849_);
    if v___x_3850_ == 0 {
        crate::leanh::lean_dec(v_a_3846_);
        crate::leanh::lean_dec_ref(v_inst_3843_);
        crate::leanh::lean_dec_ref(v_inst_3842_);
        crate::leanh::lean_inc(v_inst_3844_);
        return v_inst_3844_;
    } else {
        let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3851_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
            v_inst_3842_,
            v_inst_3843_,
            v_inst_3844_,
            v_m_3845_,
            v_a_3846_,
        );
        return v___x_3851_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x21___boxed(
    mut v_00_u03b1_3852_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3853_: *mut crate::leanh::LeanObject,
    mut v_inst_3854_: *mut crate::leanh::LeanObject,
    mut v_inst_3855_: *mut crate::leanh::LeanObject,
    mut v_inst_3856_: *mut crate::leanh::LeanObject,
    mut v_m_3857_: *mut crate::leanh::LeanObject,
    mut v_a_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Std_DHashMap_Raw_getKey_x21(
        v_00_u03b1_3852_,
        v_00_u03b2_3853_,
        v_inst_3854_,
        v_inst_3855_,
        v_inst_3856_,
        v_m_3857_,
        v_a_3858_,
    );
    crate::leanh::lean_dec_ref(v_m_3857_);
    crate::leanh::lean_dec(v_inst_3856_);
    return v_res_3859_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x3f___redArg(
    mut v_inst_3860_: *mut crate::leanh::LeanObject,
    mut v_inst_3861_: *mut crate::leanh::LeanObject,
    mut v_m_3862_: *mut crate::leanh::LeanObject,
    mut v_a_3863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    v_buckets_3864_ = crate::leanh::lean_ctor_get(v_m_3862_, 1);
    v___x_3865_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3866_ = lean_array_get_size(v_buckets_3864_);
    v___x_3867_ = lean_nat_dec_lt(v___x_3865_, v___x_3866_);
    if v___x_3867_ == 0 {
        let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3863_);
        crate::leanh::lean_dec_ref(v_inst_3861_);
        crate::leanh::lean_dec_ref(v_inst_3860_);
        v___x_3868_ = crate::leanh::lean_box(0);
        return v___x_3868_;
    } else {
        let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3869_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
            v_inst_3860_,
            v_inst_3861_,
            v_m_3862_,
            v_a_3863_,
        );
        return v___x_3869_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(
    mut v_inst_3870_: *mut crate::leanh::LeanObject,
    mut v_inst_3871_: *mut crate::leanh::LeanObject,
    mut v_m_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3874_ =
        l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_3870_, v_inst_3871_, v_m_3872_, v_a_3873_);
    crate::leanh::lean_dec_ref(v_m_3872_);
    return v_res_3874_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x3f(
    mut v_00_u03b1_3875_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3876_: *mut crate::leanh::LeanObject,
    mut v_inst_3877_: *mut crate::leanh::LeanObject,
    mut v_inst_3878_: *mut crate::leanh::LeanObject,
    mut v_m_3879_: *mut crate::leanh::LeanObject,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: u8 = 0;
    v_buckets_3881_ = crate::leanh::lean_ctor_get(v_m_3879_, 1);
    v___x_3882_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3883_ = lean_array_get_size(v_buckets_3881_);
    v___x_3884_ = lean_nat_dec_lt(v___x_3882_, v___x_3883_);
    if v___x_3884_ == 0 {
        let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3880_);
        crate::leanh::lean_dec_ref(v_inst_3878_);
        crate::leanh::lean_dec_ref(v_inst_3877_);
        v___x_3885_ = crate::leanh::lean_box(0);
        return v___x_3885_;
    } else {
        let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3886_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
            v_inst_3877_,
            v_inst_3878_,
            v_m_3879_,
            v_a_3880_,
        );
        return v___x_3886_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x3f___boxed(
    mut v_00_u03b1_3887_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3888_: *mut crate::leanh::LeanObject,
    mut v_inst_3889_: *mut crate::leanh::LeanObject,
    mut v_inst_3890_: *mut crate::leanh::LeanObject,
    mut v_m_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3893_ = l_Std_DHashMap_Raw_getEntry_x3f(
        v_00_u03b1_3887_,
        v_00_u03b2_3888_,
        v_inst_3889_,
        v_inst_3890_,
        v_m_3891_,
        v_a_3892_,
    );
    crate::leanh::lean_dec_ref(v_m_3891_);
    return v_res_3893_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry___redArg(
    mut v_inst_3894_: *mut crate::leanh::LeanObject,
    mut v_inst_3895_: *mut crate::leanh::LeanObject,
    mut v_m_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3898_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_inst_3894_,
        v_inst_3895_,
        v_m_3896_,
        v_a_3897_,
    );
    return v___x_3898_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry___redArg___boxed(
    mut v_inst_3899_: *mut crate::leanh::LeanObject,
    mut v_inst_3900_: *mut crate::leanh::LeanObject,
    mut v_m_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ =
        l_Std_DHashMap_Raw_getEntry___redArg(v_inst_3899_, v_inst_3900_, v_m_3901_, v_a_3902_);
    crate::leanh::lean_dec_ref(v_m_3901_);
    return v_res_3903_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry(
    mut v_00_u03b1_3904_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3905_: *mut crate::leanh::LeanObject,
    mut v_inst_3906_: *mut crate::leanh::LeanObject,
    mut v_inst_3907_: *mut crate::leanh::LeanObject,
    mut v_m_3908_: *mut crate::leanh::LeanObject,
    mut v_a_3909_: *mut crate::leanh::LeanObject,
    mut v_h_3910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3911_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_inst_3906_,
        v_inst_3907_,
        v_m_3908_,
        v_a_3909_,
    );
    return v___x_3911_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry___boxed(
    mut v_00_u03b1_3912_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3913_: *mut crate::leanh::LeanObject,
    mut v_inst_3914_: *mut crate::leanh::LeanObject,
    mut v_inst_3915_: *mut crate::leanh::LeanObject,
    mut v_m_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
    mut v_h_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Std_DHashMap_Raw_getEntry(
        v_00_u03b1_3912_,
        v_00_u03b2_3913_,
        v_inst_3914_,
        v_inst_3915_,
        v_m_3916_,
        v_a_3917_,
        v_h_3918_,
    );
    crate::leanh::lean_dec_ref(v_m_3916_);
    return v_res_3919_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntryD___redArg(
    mut v_inst_3920_: *mut crate::leanh::LeanObject,
    mut v_inst_3921_: *mut crate::leanh::LeanObject,
    mut v_m_3922_: *mut crate::leanh::LeanObject,
    mut v_a_3923_: *mut crate::leanh::LeanObject,
    mut v_fallback_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    v_buckets_3925_ = crate::leanh::lean_ctor_get(v_m_3922_, 1);
    v___x_3926_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3927_ = lean_array_get_size(v_buckets_3925_);
    v___x_3928_ = lean_nat_dec_lt(v___x_3926_, v___x_3927_);
    if v___x_3928_ == 0 {
        crate::leanh::lean_dec(v_a_3923_);
        crate::leanh::lean_dec_ref(v_inst_3921_);
        crate::leanh::lean_dec_ref(v_inst_3920_);
        crate::leanh::lean_inc_ref(v_fallback_3924_);
        return v_fallback_3924_;
    } else {
        let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3929_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(
            v_inst_3920_,
            v_inst_3921_,
            v_m_3922_,
            v_a_3923_,
            v_fallback_3924_,
        );
        return v___x_3929_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getEntryD___redArg___boxed(
    mut v_inst_3930_: *mut crate::leanh::LeanObject,
    mut v_inst_3931_: *mut crate::leanh::LeanObject,
    mut v_m_3932_: *mut crate::leanh::LeanObject,
    mut v_a_3933_: *mut crate::leanh::LeanObject,
    mut v_fallback_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_Std_DHashMap_Raw_getEntryD___redArg(
        v_inst_3930_,
        v_inst_3931_,
        v_m_3932_,
        v_a_3933_,
        v_fallback_3934_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3934_);
    crate::leanh::lean_dec_ref(v_m_3932_);
    return v_res_3935_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntryD(
    mut v_00_u03b1_3936_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3937_: *mut crate::leanh::LeanObject,
    mut v_inst_3938_: *mut crate::leanh::LeanObject,
    mut v_inst_3939_: *mut crate::leanh::LeanObject,
    mut v_m_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_fallback_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: u8 = 0;
    v_buckets_3943_ = crate::leanh::lean_ctor_get(v_m_3940_, 1);
    v___x_3944_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3945_ = lean_array_get_size(v_buckets_3943_);
    v___x_3946_ = lean_nat_dec_lt(v___x_3944_, v___x_3945_);
    if v___x_3946_ == 0 {
        crate::leanh::lean_dec(v_a_3941_);
        crate::leanh::lean_dec_ref(v_inst_3939_);
        crate::leanh::lean_dec_ref(v_inst_3938_);
        crate::leanh::lean_inc_ref(v_fallback_3942_);
        return v_fallback_3942_;
    } else {
        let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3947_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(
            v_inst_3938_,
            v_inst_3939_,
            v_m_3940_,
            v_a_3941_,
            v_fallback_3942_,
        );
        return v___x_3947_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getEntryD___boxed(
    mut v_00_u03b1_3948_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3949_: *mut crate::leanh::LeanObject,
    mut v_inst_3950_: *mut crate::leanh::LeanObject,
    mut v_inst_3951_: *mut crate::leanh::LeanObject,
    mut v_m_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_fallback_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3955_ = l_Std_DHashMap_Raw_getEntryD(
        v_00_u03b1_3948_,
        v_00_u03b2_3949_,
        v_inst_3950_,
        v_inst_3951_,
        v_m_3952_,
        v_a_3953_,
        v_fallback_3954_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3954_);
    crate::leanh::lean_dec_ref(v_m_3952_);
    return v_res_3955_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x21___redArg(
    mut v_inst_3956_: *mut crate::leanh::LeanObject,
    mut v_inst_3957_: *mut crate::leanh::LeanObject,
    mut v_inst_3958_: *mut crate::leanh::LeanObject,
    mut v_m_3959_: *mut crate::leanh::LeanObject,
    mut v_a_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    v_buckets_3961_ = crate::leanh::lean_ctor_get(v_m_3959_, 1);
    v___x_3962_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3963_ = lean_array_get_size(v_buckets_3961_);
    v___x_3964_ = lean_nat_dec_lt(v___x_3962_, v___x_3963_);
    if v___x_3964_ == 0 {
        crate::leanh::lean_dec(v_a_3960_);
        crate::leanh::lean_dec_ref(v_inst_3957_);
        crate::leanh::lean_dec_ref(v_inst_3956_);
        crate::leanh::lean_inc_ref(v_inst_3958_);
        return v_inst_3958_;
    } else {
        let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3965_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(
            v_inst_3956_,
            v_inst_3957_,
            v_m_3959_,
            v_a_3960_,
            v_inst_3958_,
        );
        return v___x_3965_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(
    mut v_inst_3966_: *mut crate::leanh::LeanObject,
    mut v_inst_3967_: *mut crate::leanh::LeanObject,
    mut v_inst_3968_: *mut crate::leanh::LeanObject,
    mut v_m_3969_: *mut crate::leanh::LeanObject,
    mut v_a_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(
        v_inst_3966_,
        v_inst_3967_,
        v_inst_3968_,
        v_m_3969_,
        v_a_3970_,
    );
    crate::leanh::lean_dec_ref(v_m_3969_);
    crate::leanh::lean_dec_ref(v_inst_3968_);
    return v_res_3971_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x21(
    mut v_00_u03b1_3972_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3973_: *mut crate::leanh::LeanObject,
    mut v_inst_3974_: *mut crate::leanh::LeanObject,
    mut v_inst_3975_: *mut crate::leanh::LeanObject,
    mut v_inst_3976_: *mut crate::leanh::LeanObject,
    mut v_m_3977_: *mut crate::leanh::LeanObject,
    mut v_a_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    v_buckets_3979_ = crate::leanh::lean_ctor_get(v_m_3977_, 1);
    v___x_3980_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3981_ = lean_array_get_size(v_buckets_3979_);
    v___x_3982_ = lean_nat_dec_lt(v___x_3980_, v___x_3981_);
    if v___x_3982_ == 0 {
        crate::leanh::lean_dec(v_a_3978_);
        crate::leanh::lean_dec_ref(v_inst_3975_);
        crate::leanh::lean_dec_ref(v_inst_3974_);
        crate::leanh::lean_inc_ref(v_inst_3976_);
        return v_inst_3976_;
    } else {
        let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(
            v_inst_3974_,
            v_inst_3975_,
            v_m_3977_,
            v_a_3978_,
            v_inst_3976_,
        );
        return v___x_3983_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x21___boxed(
    mut v_00_u03b1_3984_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3985_: *mut crate::leanh::LeanObject,
    mut v_inst_3986_: *mut crate::leanh::LeanObject,
    mut v_inst_3987_: *mut crate::leanh::LeanObject,
    mut v_inst_3988_: *mut crate::leanh::LeanObject,
    mut v_m_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3991_ = l_Std_DHashMap_Raw_getEntry_x21(
        v_00_u03b1_3984_,
        v_00_u03b2_3985_,
        v_inst_3986_,
        v_inst_3987_,
        v_inst_3988_,
        v_m_3989_,
        v_a_3990_,
    );
    crate::leanh::lean_dec_ref(v_m_3989_);
    crate::leanh::lean_dec_ref(v_inst_3988_);
    return v_res_3991_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty___redArg(
    mut v_m_3992_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    v_size_3993_ = crate::leanh::lean_ctor_get(v_m_3992_, 0);
    v___x_3994_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3995_ = lean_nat_dec_eq(v_size_3993_, v___x_3994_);
    return v___x_3995_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty___redArg___boxed(
    mut v_m_3996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3997_: u8 = 0;
    let mut v_r_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3997_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_3996_);
    crate::leanh::lean_dec_ref(v_m_3996_);
    v_r_3998_ = crate::leanh::lean_box((v_res_3997_) as usize);
    return v_r_3998_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty(
    mut v_00_u03b1_3999_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4000_: *mut crate::leanh::LeanObject,
    mut v_m_4001_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: u8 = 0;
    v_size_4002_ = crate::leanh::lean_ctor_get(v_m_4001_, 0);
    v___x_4003_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4004_ = lean_nat_dec_eq(v_size_4002_, v___x_4003_);
    return v___x_4004_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty___boxed(
    mut v_00_u03b1_4005_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4006_: *mut crate::leanh::LeanObject,
    mut v_m_4007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4008_: u8 = 0;
    let mut v_r_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4008_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_4005_, v_00_u03b2_4006_, v_m_4007_);
    crate::leanh::lean_dec_ref(v_m_4007_);
    v_r_4009_ = crate::leanh::lean_box((v_res_4008_) as usize);
    return v_r_4009_;
}
pub unsafe fn l_Std_DHashMap_Raw_modify___redArg(
    mut v_inst_4010_: *mut crate::leanh::LeanObject,
    mut v_inst_4011_: *mut crate::leanh::LeanObject,
    mut v_m_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
    mut v_f_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: u8 = 0;
    v_buckets_4015_ = crate::leanh::lean_ctor_get(v_m_4012_, 1);
    v___x_4016_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4017_ = lean_array_get_size(v_buckets_4015_);
    v___x_4018_ = lean_nat_dec_lt(v___x_4016_, v___x_4017_);
    if v___x_4018_ == 0 {
        let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_4014_);
        crate::leanh::lean_dec(v_a_4013_);
        crate::leanh::lean_dec_ref(v_m_4012_);
        crate::leanh::lean_dec_ref(v_inst_4011_);
        crate::leanh::lean_dec_ref(v_inst_4010_);
        v___x_4019_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4019_;
    } else {
        let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4020_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
            v_inst_4010_,
            v_inst_4011_,
            v_m_4012_,
            v_a_4013_,
            v_f_4014_,
        );
        return v___x_4020_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_modify(
    mut v_00_u03b1_4021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4022_: *mut crate::leanh::LeanObject,
    mut v_inst_4023_: *mut crate::leanh::LeanObject,
    mut v_inst_4024_: *mut crate::leanh::LeanObject,
    mut v_inst_4025_: *mut crate::leanh::LeanObject,
    mut v_m_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
    mut v_f_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: u8 = 0;
    v_buckets_4029_ = crate::leanh::lean_ctor_get(v_m_4026_, 1);
    v___x_4030_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4031_ = lean_array_get_size(v_buckets_4029_);
    v___x_4032_ = lean_nat_dec_lt(v___x_4030_, v___x_4031_);
    if v___x_4032_ == 0 {
        let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_4028_);
        crate::leanh::lean_dec(v_a_4027_);
        crate::leanh::lean_dec_ref(v_m_4026_);
        crate::leanh::lean_dec_ref(v_inst_4025_);
        crate::leanh::lean_dec_ref(v_inst_4023_);
        v___x_4033_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4033_;
    } else {
        let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4034_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
            v_inst_4023_,
            v_inst_4025_,
            v_m_4026_,
            v_a_4027_,
            v_f_4028_,
        );
        return v___x_4034_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_modify___redArg(
    mut v_inst_4035_: *mut crate::leanh::LeanObject,
    mut v_inst_4036_: *mut crate::leanh::LeanObject,
    mut v_m_4037_: *mut crate::leanh::LeanObject,
    mut v_a_4038_: *mut crate::leanh::LeanObject,
    mut v_f_4039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u8 = 0;
    v_buckets_4040_ = crate::leanh::lean_ctor_get(v_m_4037_, 1);
    v___x_4041_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4042_ = lean_array_get_size(v_buckets_4040_);
    v___x_4043_ = lean_nat_dec_lt(v___x_4041_, v___x_4042_);
    if v___x_4043_ == 0 {
        let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_4039_);
        crate::leanh::lean_dec(v_a_4038_);
        crate::leanh::lean_dec_ref(v_m_4037_);
        crate::leanh::lean_dec_ref(v_inst_4036_);
        crate::leanh::lean_dec_ref(v_inst_4035_);
        v___x_4044_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4044_;
    } else {
        let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
            v_inst_4035_,
            v_inst_4036_,
            v_m_4037_,
            v_a_4038_,
            v_f_4039_,
        );
        return v___x_4045_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_modify(
    mut v_00_u03b1_4046_: *mut crate::leanh::LeanObject,
    mut v_inst_4047_: *mut crate::leanh::LeanObject,
    mut v_inst_4048_: *mut crate::leanh::LeanObject,
    mut v_inst_4049_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4050_: *mut crate::leanh::LeanObject,
    mut v_m_4051_: *mut crate::leanh::LeanObject,
    mut v_a_4052_: *mut crate::leanh::LeanObject,
    mut v_f_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: u8 = 0;
    v_buckets_4054_ = crate::leanh::lean_ctor_get(v_m_4051_, 1);
    v___x_4055_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4056_ = lean_array_get_size(v_buckets_4054_);
    v___x_4057_ = lean_nat_dec_lt(v___x_4055_, v___x_4056_);
    if v___x_4057_ == 0 {
        let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_4053_);
        crate::leanh::lean_dec(v_a_4052_);
        crate::leanh::lean_dec_ref(v_m_4051_);
        crate::leanh::lean_dec_ref(v_inst_4049_);
        crate::leanh::lean_dec_ref(v_inst_4047_);
        v___x_4058_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4058_;
    } else {
        let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
            v_inst_4047_,
            v_inst_4049_,
            v_m_4051_,
            v_a_4052_,
            v_f_4053_,
        );
        return v___x_4059_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_alter___redArg(
    mut v_inst_4060_: *mut crate::leanh::LeanObject,
    mut v_inst_4061_: *mut crate::leanh::LeanObject,
    mut v_m_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_f_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: u8 = 0;
    v_buckets_4065_ = crate::leanh::lean_ctor_get(v_m_4062_, 1);
    v___x_4066_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4067_ = lean_array_get_size(v_buckets_4065_);
    v___x_4068_ = lean_nat_dec_lt(v___x_4066_, v___x_4067_);
    if v___x_4068_ == 0 {
        let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_4064_);
        crate::leanh::lean_dec(v_a_4063_);
        crate::leanh::lean_dec_ref(v_m_4062_);
        crate::leanh::lean_dec_ref(v_inst_4061_);
        crate::leanh::lean_dec_ref(v_inst_4060_);
        v___x_4069_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4069_;
    } else {
        let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4070_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
            v_inst_4060_,
            v_inst_4061_,
            v_m_4062_,
            v_a_4063_,
            v_f_4064_,
        );
        return v___x_4070_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_alter(
    mut v_00_u03b1_4071_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4072_: *mut crate::leanh::LeanObject,
    mut v_inst_4073_: *mut crate::leanh::LeanObject,
    mut v_inst_4074_: *mut crate::leanh::LeanObject,
    mut v_inst_4075_: *mut crate::leanh::LeanObject,
    mut v_m_4076_: *mut crate::leanh::LeanObject,
    mut v_a_4077_: *mut crate::leanh::LeanObject,
    mut v_f_4078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    v_buckets_4079_ = crate::leanh::lean_ctor_get(v_m_4076_, 1);
    v___x_4080_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4081_ = lean_array_get_size(v_buckets_4079_);
    v___x_4082_ = lean_nat_dec_lt(v___x_4080_, v___x_4081_);
    if v___x_4082_ == 0 {
        let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_4078_);
        crate::leanh::lean_dec(v_a_4077_);
        crate::leanh::lean_dec_ref(v_m_4076_);
        crate::leanh::lean_dec_ref(v_inst_4075_);
        crate::leanh::lean_dec_ref(v_inst_4073_);
        v___x_4083_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4083_;
    } else {
        let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4084_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
            v_inst_4073_,
            v_inst_4075_,
            v_m_4076_,
            v_a_4077_,
            v_f_4078_,
        );
        return v___x_4084_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_alter___redArg(
    mut v_inst_4085_: *mut crate::leanh::LeanObject,
    mut v_inst_4086_: *mut crate::leanh::LeanObject,
    mut v_m_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
    mut v_f_4089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: u8 = 0;
    v_buckets_4090_ = crate::leanh::lean_ctor_get(v_m_4087_, 1);
    v___x_4091_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4092_ = lean_array_get_size(v_buckets_4090_);
    v___x_4093_ = lean_nat_dec_lt(v___x_4091_, v___x_4092_);
    if v___x_4093_ == 0 {
        let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_4089_);
        crate::leanh::lean_dec(v_a_4088_);
        crate::leanh::lean_dec_ref(v_m_4087_);
        crate::leanh::lean_dec_ref(v_inst_4086_);
        crate::leanh::lean_dec_ref(v_inst_4085_);
        v___x_4094_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4094_;
    } else {
        let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4095_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
            v_inst_4085_,
            v_inst_4086_,
            v_m_4087_,
            v_a_4088_,
            v_f_4089_,
        );
        return v___x_4095_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_alter(
    mut v_00_u03b1_4096_: *mut crate::leanh::LeanObject,
    mut v_inst_4097_: *mut crate::leanh::LeanObject,
    mut v_inst_4098_: *mut crate::leanh::LeanObject,
    mut v_inst_4099_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4100_: *mut crate::leanh::LeanObject,
    mut v_m_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_f_4103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: u8 = 0;
    v_buckets_4104_ = crate::leanh::lean_ctor_get(v_m_4101_, 1);
    v___x_4105_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4106_ = lean_array_get_size(v_buckets_4104_);
    v___x_4107_ = lean_nat_dec_lt(v___x_4105_, v___x_4106_);
    if v___x_4107_ == 0 {
        let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_4103_);
        crate::leanh::lean_dec(v_a_4102_);
        crate::leanh::lean_dec_ref(v_m_4101_);
        crate::leanh::lean_dec_ref(v_inst_4099_);
        crate::leanh::lean_dec_ref(v_inst_4097_);
        v___x_4108_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4108_;
    } else {
        let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
            v_inst_4097_,
            v_inst_4099_,
            v_m_4101_,
            v_a_4102_,
            v_f_4103_,
        );
        return v___x_4109_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0(
    mut v_f_4110_: *mut crate::leanh::LeanObject,
    mut v_a_4111_: *mut crate::leanh::LeanObject,
    mut v_b_4112_: *mut crate::leanh::LeanObject,
    mut v_d_4113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = crate::leanh::lean_apply_3(v_f_4110_, v_d_4113_, v_a_4111_, v_b_4112_);
    return v___x_4114_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(
    mut v_inst_4115_: *mut crate::leanh::LeanObject,
    mut v___f_4116_: *mut crate::leanh::LeanObject,
    mut v_l_4117_: *mut crate::leanh::LeanObject,
    mut v_acc_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v_inst_4115_,
        v___f_4116_,
        v_acc_4118_,
        v_l_4117_,
    );
    return v___x_4119_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRevM___redArg(
    mut v_inst_4120_: *mut crate::leanh::LeanObject,
    mut v_f_4121_: *mut crate::leanh::LeanObject,
    mut v_init_4122_: *mut crate::leanh::LeanObject,
    mut v_b_4123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    v_buckets_4124_ = crate::leanh::lean_ctor_get(v_b_4123_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4124_);
    crate::leanh::lean_dec_ref(v_b_4123_);
    v___x_4125_ = lean_array_get_size(v_buckets_4124_);
    v___x_4126_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4127_ = lean_nat_dec_lt(v___x_4126_, v___x_4125_);
    if v___x_4127_ == 0 {
        let mut v_toApplicative_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4124_);
        crate::leanh::lean_dec(v_f_4121_);
        v_toApplicative_4128_ = crate::leanh::lean_ctor_get(v_inst_4120_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4128_);
        crate::leanh::lean_dec_ref(v_inst_4120_);
        v_toPure_4129_ = crate::leanh::lean_ctor_get(v_toApplicative_4128_, 1);
        crate::leanh::lean_inc(v_toPure_4129_);
        crate::leanh::lean_dec_ref(v_toApplicative_4128_);
        v___x_4130_ =
            crate::leanh::lean_apply_2(v_toPure_4129_, crate::leanh::lean_box(0), v_init_4122_);
        return v___x_4130_;
    } else {
        let mut v___f_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4133_: usize = 0;
        let mut v___x_4134_: usize = 0;
        let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4131_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4131_, 0, v_f_4121_);
        crate::leanh::lean_inc_ref(v_inst_4120_);
        v___f_4132_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4132_, 0, v_inst_4120_);
        crate::leanh::lean_closure_set(v___f_4132_, 1, v___f_4131_);
        v___x_4133_ = lean_usize_of_nat(v___x_4125_);
        v___x_4134_ = 0usize;
        v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_4120_,
            v___f_4132_,
            v_buckets_4124_,
            v___x_4133_,
            v___x_4134_,
            v_init_4122_,
        );
        return v___x_4135_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRevM(
    mut v_00_u03b1_4136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4137_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4138_: *mut crate::leanh::LeanObject,
    mut v_m_4139_: *mut crate::leanh::LeanObject,
    mut v_inst_4140_: *mut crate::leanh::LeanObject,
    mut v_f_4141_: *mut crate::leanh::LeanObject,
    mut v_init_4142_: *mut crate::leanh::LeanObject,
    mut v_b_4143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    v_buckets_4144_ = crate::leanh::lean_ctor_get(v_b_4143_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4144_);
    crate::leanh::lean_dec_ref(v_b_4143_);
    v___x_4145_ = lean_array_get_size(v_buckets_4144_);
    v___x_4146_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4147_ = lean_nat_dec_lt(v___x_4146_, v___x_4145_);
    if v___x_4147_ == 0 {
        let mut v_toApplicative_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4144_);
        crate::leanh::lean_dec(v_f_4141_);
        v_toApplicative_4148_ = crate::leanh::lean_ctor_get(v_inst_4140_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4148_);
        crate::leanh::lean_dec_ref(v_inst_4140_);
        v_toPure_4149_ = crate::leanh::lean_ctor_get(v_toApplicative_4148_, 1);
        crate::leanh::lean_inc(v_toPure_4149_);
        crate::leanh::lean_dec_ref(v_toApplicative_4148_);
        v___x_4150_ =
            crate::leanh::lean_apply_2(v_toPure_4149_, crate::leanh::lean_box(0), v_init_4142_);
        return v___x_4150_;
    } else {
        let mut v___f_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4153_: usize = 0;
        let mut v___x_4154_: usize = 0;
        let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4151_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4151_, 0, v_f_4141_);
        crate::leanh::lean_inc_ref(v_inst_4140_);
        v___f_4152_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4152_, 0, v_inst_4140_);
        crate::leanh::lean_closure_set(v___f_4152_, 1, v___f_4151_);
        v___x_4153_ = lean_usize_of_nat(v___x_4145_);
        v___x_4154_ = 0usize;
        v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_4140_,
            v___f_4152_,
            v_buckets_4144_,
            v___x_4153_,
            v___x_4154_,
            v_init_4142_,
        );
        return v___x_4155_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1(
    mut v___x_4156_: *mut crate::leanh::LeanObject,
    mut v___f_4157_: *mut crate::leanh::LeanObject,
    mut v_l_4158_: *mut crate::leanh::LeanObject,
    mut v_acc_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_4156_,
        v___f_4157_,
        v_acc_4159_,
        v_l_4158_,
    );
    return v___x_4160_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRev___redArg(
    mut v_f_4180_: *mut crate::leanh::LeanObject,
    mut v_init_4181_: *mut crate::leanh::LeanObject,
    mut v_b_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: u8 = 0;
    v___x_4183_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4184_ = crate::leanh::lean_ctor_get(v_b_4182_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4184_);
    crate::leanh::lean_dec_ref(v_b_4182_);
    v___x_4185_ = lean_array_get_size(v_buckets_4184_);
    v___x_4186_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4187_ = lean_nat_dec_lt(v___x_4186_, v___x_4185_);
    if v___x_4187_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4184_);
        crate::leanh::lean_dec(v_f_4180_);
        return v_init_4181_;
    } else {
        let mut v___f_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4190_: usize = 0;
        let mut v___x_4191_: usize = 0;
        let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4188_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4188_, 0, v_f_4180_);
        v___f_4189_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4189_, 0, v___x_4183_);
        crate::leanh::lean_closure_set(v___f_4189_, 1, v___f_4188_);
        v___x_4190_ = lean_usize_of_nat(v___x_4185_);
        v___x_4191_ = 0usize;
        v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4183_,
            v___f_4189_,
            v_buckets_4184_,
            v___x_4190_,
            v___x_4191_,
            v_init_4181_,
        );
        return v___x_4192_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRev(
    mut v_00_u03b1_4193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4194_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4195_: *mut crate::leanh::LeanObject,
    mut v_f_4196_: *mut crate::leanh::LeanObject,
    mut v_init_4197_: *mut crate::leanh::LeanObject,
    mut v_b_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u8 = 0;
    v___x_4199_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4200_ = crate::leanh::lean_ctor_get(v_b_4198_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4200_);
    crate::leanh::lean_dec_ref(v_b_4198_);
    v___x_4201_ = lean_array_get_size(v_buckets_4200_);
    v___x_4202_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4203_ = lean_nat_dec_lt(v___x_4202_, v___x_4201_);
    if v___x_4203_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4200_);
        crate::leanh::lean_dec(v_f_4196_);
        return v_init_4197_;
    } else {
        let mut v___f_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4206_: usize = 0;
        let mut v___x_4207_: usize = 0;
        let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4204_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4204_, 0, v_f_4196_);
        v___f_4205_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4205_, 0, v___x_4199_);
        crate::leanh::lean_closure_set(v___f_4205_, 1, v___f_4204_);
        v___x_4206_ = lean_usize_of_nat(v___x_4201_);
        v___x_4207_ = 0usize;
        v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4199_,
            v___f_4205_,
            v_buckets_4200_,
            v___x_4206_,
            v___x_4207_,
            v_init_4197_,
        );
        return v___x_4208_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_foldRevM___redArg(
    mut v_inst_4209_: *mut crate::leanh::LeanObject,
    mut v_f_4210_: *mut crate::leanh::LeanObject,
    mut v_init_4211_: *mut crate::leanh::LeanObject,
    mut v_b_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: u8 = 0;
    v_buckets_4213_ = crate::leanh::lean_ctor_get(v_b_4212_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4213_);
    crate::leanh::lean_dec_ref(v_b_4212_);
    v___x_4214_ = lean_array_get_size(v_buckets_4213_);
    v___x_4215_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4216_ = lean_nat_dec_lt(v___x_4215_, v___x_4214_);
    if v___x_4216_ == 0 {
        let mut v_toApplicative_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4213_);
        crate::leanh::lean_dec(v_f_4210_);
        v_toApplicative_4217_ = crate::leanh::lean_ctor_get(v_inst_4209_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4217_);
        crate::leanh::lean_dec_ref(v_inst_4209_);
        v_toPure_4218_ = crate::leanh::lean_ctor_get(v_toApplicative_4217_, 1);
        crate::leanh::lean_inc(v_toPure_4218_);
        crate::leanh::lean_dec_ref(v_toApplicative_4217_);
        v___x_4219_ =
            crate::leanh::lean_apply_2(v_toPure_4218_, crate::leanh::lean_box(0), v_init_4211_);
        return v___x_4219_;
    } else {
        let mut v___f_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4222_: usize = 0;
        let mut v___x_4223_: usize = 0;
        let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4220_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4220_, 0, v_f_4210_);
        crate::leanh::lean_inc_ref(v_inst_4209_);
        v___f_4221_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4221_, 0, v_inst_4209_);
        crate::leanh::lean_closure_set(v___f_4221_, 1, v___f_4220_);
        v___x_4222_ = lean_usize_of_nat(v___x_4214_);
        v___x_4223_ = 0usize;
        v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_4209_,
            v___f_4221_,
            v_buckets_4213_,
            v___x_4222_,
            v___x_4223_,
            v_init_4211_,
        );
        return v___x_4224_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_foldRevM(
    mut v_00_u03b1_4225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4226_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4227_: *mut crate::leanh::LeanObject,
    mut v_m_4228_: *mut crate::leanh::LeanObject,
    mut v_inst_4229_: *mut crate::leanh::LeanObject,
    mut v_f_4230_: *mut crate::leanh::LeanObject,
    mut v_init_4231_: *mut crate::leanh::LeanObject,
    mut v_b_4232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    v_buckets_4233_ = crate::leanh::lean_ctor_get(v_b_4232_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4233_);
    crate::leanh::lean_dec_ref(v_b_4232_);
    v___x_4234_ = lean_array_get_size(v_buckets_4233_);
    v___x_4235_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4236_ = lean_nat_dec_lt(v___x_4235_, v___x_4234_);
    if v___x_4236_ == 0 {
        let mut v_toApplicative_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4233_);
        crate::leanh::lean_dec(v_f_4230_);
        v_toApplicative_4237_ = crate::leanh::lean_ctor_get(v_inst_4229_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4237_);
        crate::leanh::lean_dec_ref(v_inst_4229_);
        v_toPure_4238_ = crate::leanh::lean_ctor_get(v_toApplicative_4237_, 1);
        crate::leanh::lean_inc(v_toPure_4238_);
        crate::leanh::lean_dec_ref(v_toApplicative_4237_);
        v___x_4239_ =
            crate::leanh::lean_apply_2(v_toPure_4238_, crate::leanh::lean_box(0), v_init_4231_);
        return v___x_4239_;
    } else {
        let mut v___f_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4242_: usize = 0;
        let mut v___x_4243_: usize = 0;
        let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4240_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4240_, 0, v_f_4230_);
        crate::leanh::lean_inc_ref(v_inst_4229_);
        v___f_4241_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4241_, 0, v_inst_4229_);
        crate::leanh::lean_closure_set(v___f_4241_, 1, v___f_4240_);
        v___x_4242_ = lean_usize_of_nat(v___x_4234_);
        v___x_4243_ = 0usize;
        v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_4229_,
            v___f_4241_,
            v_buckets_4233_,
            v___x_4242_,
            v___x_4243_,
            v_init_4231_,
        );
        return v___x_4244_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_foldRev___redArg(
    mut v_f_4245_: *mut crate::leanh::LeanObject,
    mut v_init_4246_: *mut crate::leanh::LeanObject,
    mut v_b_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    v___x_4248_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4249_ = crate::leanh::lean_ctor_get(v_b_4247_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4249_);
    crate::leanh::lean_dec_ref(v_b_4247_);
    v___x_4250_ = lean_array_get_size(v_buckets_4249_);
    v___x_4251_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4252_ = lean_nat_dec_lt(v___x_4251_, v___x_4250_);
    if v___x_4252_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4249_);
        crate::leanh::lean_dec(v_f_4245_);
        return v_init_4246_;
    } else {
        let mut v___f_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4255_: usize = 0;
        let mut v___x_4256_: usize = 0;
        let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4253_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4253_, 0, v_f_4245_);
        v___f_4254_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4254_, 0, v___x_4248_);
        crate::leanh::lean_closure_set(v___f_4254_, 1, v___f_4253_);
        v___x_4255_ = lean_usize_of_nat(v___x_4250_);
        v___x_4256_ = 0usize;
        v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4248_,
            v___f_4254_,
            v_buckets_4249_,
            v___x_4255_,
            v___x_4256_,
            v_init_4246_,
        );
        return v___x_4257_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_foldRev(
    mut v_00_u03b1_4258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4260_: *mut crate::leanh::LeanObject,
    mut v_f_4261_: *mut crate::leanh::LeanObject,
    mut v_init_4262_: *mut crate::leanh::LeanObject,
    mut v_b_4263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    v___x_4264_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4265_ = crate::leanh::lean_ctor_get(v_b_4263_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4265_);
    crate::leanh::lean_dec_ref(v_b_4263_);
    v___x_4266_ = lean_array_get_size(v_buckets_4265_);
    v___x_4267_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4268_ = lean_nat_dec_lt(v___x_4267_, v___x_4266_);
    if v___x_4268_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4265_);
        crate::leanh::lean_dec(v_f_4261_);
        return v_init_4262_;
    } else {
        let mut v___f_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4271_: usize = 0;
        let mut v___x_4272_: usize = 0;
        let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4269_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4269_, 0, v_f_4261_);
        v___f_4270_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4270_, 0, v___x_4264_);
        crate::leanh::lean_closure_set(v___f_4270_, 1, v___f_4269_);
        v___x_4271_ = lean_usize_of_nat(v___x_4266_);
        v___x_4272_ = 0usize;
        v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4264_,
            v___f_4270_,
            v_buckets_4265_,
            v___x_4271_,
            v___x_4272_,
            v_init_4262_,
        );
        return v___x_4273_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(
    mut v_f_4274_: *mut crate::leanh::LeanObject,
    mut v_x_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4278_, 0, v___y_4276_);
    crate::leanh::lean_ctor_set(v___x_4278_, 1, v___y_4277_);
    v___x_4279_ = crate::leanh::lean_apply_1(v_f_4274_, v___x_4278_);
    return v___x_4279_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(
    mut v_inst_4280_: *mut crate::leanh::LeanObject,
    mut v___f_4281_: *mut crate::leanh::LeanObject,
    mut v_x_4282_: *mut crate::leanh::LeanObject,
    mut v___y_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = crate::leanh::lean_box(0);
    v___x_4285_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_4280_,
        v___f_4281_,
        v___x_4284_,
        v___y_4283_,
    );
    return v___x_4285_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forMUncurried___redArg(
    mut v_inst_4286_: *mut crate::leanh::LeanObject,
    mut v_f_4287_: *mut crate::leanh::LeanObject,
    mut v_b_4288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    v_buckets_4289_ = crate::leanh::lean_ctor_get(v_b_4288_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4289_);
    crate::leanh::lean_dec_ref(v_b_4288_);
    v___x_4290_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4291_ = lean_array_get_size(v_buckets_4289_);
    v___x_4292_ = crate::leanh::lean_box(0);
    v___x_4293_ = lean_nat_dec_lt(v___x_4290_, v___x_4291_);
    if v___x_4293_ == 0 {
        let mut v_toApplicative_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4289_);
        crate::leanh::lean_dec(v_f_4287_);
        v_toApplicative_4294_ = crate::leanh::lean_ctor_get(v_inst_4286_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4294_);
        crate::leanh::lean_dec_ref(v_inst_4286_);
        v_toPure_4295_ = crate::leanh::lean_ctor_get(v_toApplicative_4294_, 1);
        crate::leanh::lean_inc(v_toPure_4295_);
        crate::leanh::lean_dec_ref(v_toApplicative_4294_);
        v___x_4296_ =
            crate::leanh::lean_apply_2(v_toPure_4295_, crate::leanh::lean_box(0), v___x_4292_);
        return v___x_4296_;
    } else {
        let mut v___f_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: u8 = 0;
        v___f_4297_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4297_, 0, v_f_4287_);
        crate::leanh::lean_inc_ref(v_inst_4286_);
        v___f_4298_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4298_, 0, v_inst_4286_);
        crate::leanh::lean_closure_set(v___f_4298_, 1, v___f_4297_);
        v___x_4299_ = lean_nat_dec_le(v___x_4291_, v___x_4291_);
        if v___x_4299_ == 0 {
            if v___x_4293_ == 0 {
                let mut v_toApplicative_4300_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4298_);
                crate::leanh::lean_dec_ref(v_buckets_4289_);
                v_toApplicative_4300_ = crate::leanh::lean_ctor_get(v_inst_4286_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4300_);
                crate::leanh::lean_dec_ref(v_inst_4286_);
                v_toPure_4301_ = crate::leanh::lean_ctor_get(v_toApplicative_4300_, 1);
                crate::leanh::lean_inc(v_toPure_4301_);
                crate::leanh::lean_dec_ref(v_toApplicative_4300_);
                v___x_4302_ = crate::leanh::lean_apply_2(
                    v_toPure_4301_,
                    crate::leanh::lean_box(0),
                    v___x_4292_,
                );
                return v___x_4302_;
            } else {
                let mut v___x_4303_: usize = 0;
                let mut v___x_4304_: usize = 0;
                let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4303_ = 0usize;
                v___x_4304_ = lean_usize_of_nat(v___x_4291_);
                v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4286_,
                    v___f_4298_,
                    v_buckets_4289_,
                    v___x_4303_,
                    v___x_4304_,
                    v___x_4292_,
                );
                return v___x_4305_;
            }
        } else {
            let mut v___x_4306_: usize = 0;
            let mut v___x_4307_: usize = 0;
            let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4306_ = 0usize;
            v___x_4307_ = lean_usize_of_nat(v___x_4291_);
            v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4286_,
                v___f_4298_,
                v_buckets_4289_,
                v___x_4306_,
                v___x_4307_,
                v___x_4292_,
            );
            return v___x_4308_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forMUncurried(
    mut v_00_u03b1_4309_: *mut crate::leanh::LeanObject,
    mut v_m_4310_: *mut crate::leanh::LeanObject,
    mut v_inst_4311_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4312_: *mut crate::leanh::LeanObject,
    mut v_f_4313_: *mut crate::leanh::LeanObject,
    mut v_b_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    v_buckets_4315_ = crate::leanh::lean_ctor_get(v_b_4314_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4315_);
    crate::leanh::lean_dec_ref(v_b_4314_);
    v___x_4316_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4317_ = lean_array_get_size(v_buckets_4315_);
    v___x_4318_ = crate::leanh::lean_box(0);
    v___x_4319_ = lean_nat_dec_lt(v___x_4316_, v___x_4317_);
    if v___x_4319_ == 0 {
        let mut v_toApplicative_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4315_);
        crate::leanh::lean_dec(v_f_4313_);
        v_toApplicative_4320_ = crate::leanh::lean_ctor_get(v_inst_4311_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4320_);
        crate::leanh::lean_dec_ref(v_inst_4311_);
        v_toPure_4321_ = crate::leanh::lean_ctor_get(v_toApplicative_4320_, 1);
        crate::leanh::lean_inc(v_toPure_4321_);
        crate::leanh::lean_dec_ref(v_toApplicative_4320_);
        v___x_4322_ =
            crate::leanh::lean_apply_2(v_toPure_4321_, crate::leanh::lean_box(0), v___x_4318_);
        return v___x_4322_;
    } else {
        let mut v___f_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4325_: u8 = 0;
        v___f_4323_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4323_, 0, v_f_4313_);
        crate::leanh::lean_inc_ref(v_inst_4311_);
        v___f_4324_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4324_, 0, v_inst_4311_);
        crate::leanh::lean_closure_set(v___f_4324_, 1, v___f_4323_);
        v___x_4325_ = lean_nat_dec_le(v___x_4317_, v___x_4317_);
        if v___x_4325_ == 0 {
            if v___x_4319_ == 0 {
                let mut v_toApplicative_4326_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4324_);
                crate::leanh::lean_dec_ref(v_buckets_4315_);
                v_toApplicative_4326_ = crate::leanh::lean_ctor_get(v_inst_4311_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4326_);
                crate::leanh::lean_dec_ref(v_inst_4311_);
                v_toPure_4327_ = crate::leanh::lean_ctor_get(v_toApplicative_4326_, 1);
                crate::leanh::lean_inc(v_toPure_4327_);
                crate::leanh::lean_dec_ref(v_toApplicative_4326_);
                v___x_4328_ = crate::leanh::lean_apply_2(
                    v_toPure_4327_,
                    crate::leanh::lean_box(0),
                    v___x_4318_,
                );
                return v___x_4328_;
            } else {
                let mut v___x_4329_: usize = 0;
                let mut v___x_4330_: usize = 0;
                let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4329_ = 0usize;
                v___x_4330_ = lean_usize_of_nat(v___x_4317_);
                v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4311_,
                    v___f_4324_,
                    v_buckets_4315_,
                    v___x_4329_,
                    v___x_4330_,
                    v___x_4318_,
                );
                return v___x_4331_;
            }
        } else {
            let mut v___x_4332_: usize = 0;
            let mut v___x_4333_: usize = 0;
            let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4332_ = 0usize;
            v___x_4333_ = lean_usize_of_nat(v___x_4317_);
            v___x_4334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4311_,
                v___f_4324_,
                v_buckets_4315_,
                v___x_4332_,
                v___x_4333_,
                v___x_4318_,
            );
            return v___x_4334_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(
    mut v_f_4335_: *mut crate::leanh::LeanObject,
    mut v_a_4336_: *mut crate::leanh::LeanObject,
    mut v_b_4337_: *mut crate::leanh::LeanObject,
    mut v_d_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4339_, 0, v_a_4336_);
    crate::leanh::lean_ctor_set(v___x_4339_, 1, v_b_4337_);
    v___x_4340_ = crate::leanh::lean_apply_2(v_f_4335_, v___x_4339_, v_d_4338_);
    return v___x_4340_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(
    mut v_inst_4341_: *mut crate::leanh::LeanObject,
    mut v___f_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
    mut v_x_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_4341_, v___f_4342_, v_a_4343_, v___y_4345_);
    return v___x_4346_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forInUncurried___redArg(
    mut v_inst_4347_: *mut crate::leanh::LeanObject,
    mut v_f_4348_: *mut crate::leanh::LeanObject,
    mut v_init_4349_: *mut crate::leanh::LeanObject,
    mut v_b_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4354_: usize = 0;
    let mut v___x_4355_: usize = 0;
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4351_ = crate::leanh::lean_ctor_get(v_b_4350_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4351_);
    crate::leanh::lean_dec_ref(v_b_4350_);
    v___f_4352_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4352_, 0, v_f_4348_);
    crate::leanh::lean_inc_ref(v_inst_4347_);
    v___f_4353_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4353_, 0, v_inst_4347_);
    crate::leanh::lean_closure_set(v___f_4353_, 1, v___f_4352_);
    v_sz_4354_ = lean_array_size(v_buckets_4351_);
    v___x_4355_ = 0usize;
    v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4347_,
        v_buckets_4351_,
        v___f_4353_,
        v_sz_4354_,
        v___x_4355_,
        v_init_4349_,
    );
    return v___x_4356_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forInUncurried(
    mut v_00_u03b1_4357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4358_: *mut crate::leanh::LeanObject,
    mut v_m_4359_: *mut crate::leanh::LeanObject,
    mut v_inst_4360_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4361_: *mut crate::leanh::LeanObject,
    mut v_f_4362_: *mut crate::leanh::LeanObject,
    mut v_init_4363_: *mut crate::leanh::LeanObject,
    mut v_b_4364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4368_: usize = 0;
    let mut v___x_4369_: usize = 0;
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4365_ = crate::leanh::lean_ctor_get(v_b_4364_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4365_);
    crate::leanh::lean_dec_ref(v_b_4364_);
    v___f_4366_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4366_, 0, v_f_4362_);
    crate::leanh::lean_inc_ref(v_inst_4360_);
    v___f_4367_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4367_, 0, v_inst_4360_);
    crate::leanh::lean_closure_set(v___f_4367_, 1, v___f_4366_);
    v_sz_4368_ = lean_array_size(v_buckets_4365_);
    v___x_4369_ = 0usize;
    v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4360_,
        v_buckets_4365_,
        v___f_4367_,
        v_sz_4368_,
        v___x_4369_,
        v_init_4363_,
    );
    return v___x_4370_;
}
pub unsafe fn l_Std_DHashMap_Raw_filterMap___redArg(
    mut v_f_4371_: *mut crate::leanh::LeanObject,
    mut v_m_4372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    v_buckets_4373_ = crate::leanh::lean_ctor_get(v_m_4372_, 1);
    v___x_4374_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4375_ = lean_array_get_size(v_buckets_4373_);
    v___x_4376_ = lean_nat_dec_lt(v___x_4374_, v___x_4375_);
    if v___x_4376_ == 0 {
        let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4372_);
        crate::leanh::lean_dec_ref(v_f_4371_);
        v___x_4377_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4377_;
    } else {
        let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4378_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4371_, v_m_4372_);
        return v___x_4378_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_filterMap(
    mut v_00_u03b1_4379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4380_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4381_: *mut crate::leanh::LeanObject,
    mut v_f_4382_: *mut crate::leanh::LeanObject,
    mut v_m_4383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    v_buckets_4384_ = crate::leanh::lean_ctor_get(v_m_4383_, 1);
    v___x_4385_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4386_ = lean_array_get_size(v_buckets_4384_);
    v___x_4387_ = lean_nat_dec_lt(v___x_4385_, v___x_4386_);
    if v___x_4387_ == 0 {
        let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4383_);
        crate::leanh::lean_dec_ref(v_f_4382_);
        v___x_4388_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4388_;
    } else {
        let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4389_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4382_, v_m_4383_);
        return v___x_4389_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_map___redArg(
    mut v_f_4390_: *mut crate::leanh::LeanObject,
    mut v_m_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: u8 = 0;
    v_buckets_4392_ = crate::leanh::lean_ctor_get(v_m_4391_, 1);
    v___x_4393_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4394_ = lean_array_get_size(v_buckets_4392_);
    v___x_4395_ = lean_nat_dec_lt(v___x_4393_, v___x_4394_);
    if v___x_4395_ == 0 {
        let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4391_);
        crate::leanh::lean_dec(v_f_4390_);
        v___x_4396_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4396_;
    } else {
        let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4397_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4390_, v_m_4391_);
        return v___x_4397_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_map(
    mut v_00_u03b1_4398_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4400_: *mut crate::leanh::LeanObject,
    mut v_f_4401_: *mut crate::leanh::LeanObject,
    mut v_m_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: u8 = 0;
    v_buckets_4403_ = crate::leanh::lean_ctor_get(v_m_4402_, 1);
    v___x_4404_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4405_ = lean_array_get_size(v_buckets_4403_);
    v___x_4406_ = lean_nat_dec_lt(v___x_4404_, v___x_4405_);
    if v___x_4406_ == 0 {
        let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4402_);
        crate::leanh::lean_dec(v_f_4401_);
        v___x_4407_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4407_;
    } else {
        let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4408_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4401_, v_m_4402_);
        return v___x_4408_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_filter___redArg(
    mut v_f_4409_: *mut crate::leanh::LeanObject,
    mut v_m_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    v_buckets_4411_ = crate::leanh::lean_ctor_get(v_m_4410_, 1);
    v___x_4412_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4413_ = lean_array_get_size(v_buckets_4411_);
    v___x_4414_ = lean_nat_dec_lt(v___x_4412_, v___x_4413_);
    if v___x_4414_ == 0 {
        let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4410_);
        crate::leanh::lean_dec_ref(v_f_4409_);
        v___x_4415_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4415_;
    } else {
        let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4416_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4409_, v_m_4410_);
        return v___x_4416_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_filter(
    mut v_00_u03b1_4417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4418_: *mut crate::leanh::LeanObject,
    mut v_f_4419_: *mut crate::leanh::LeanObject,
    mut v_m_4420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: u8 = 0;
    v_buckets_4421_ = crate::leanh::lean_ctor_get(v_m_4420_, 1);
    v___x_4422_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4423_ = lean_array_get_size(v_buckets_4421_);
    v___x_4424_ = lean_nat_dec_lt(v___x_4422_, v___x_4423_);
    if v___x_4424_ == 0 {
        let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4420_);
        crate::leanh::lean_dec_ref(v_f_4419_);
        v___x_4425_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4425_;
    } else {
        let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4426_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4419_, v_m_4420_);
        return v___x_4426_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_toArray___redArg___lam__0(
    mut v_x1_4427_: *mut crate::leanh::LeanObject,
    mut v_x2_4428_: *mut crate::leanh::LeanObject,
    mut v_x3_4429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4430_, 0, v_x2_4428_);
    crate::leanh::lean_ctor_set(v___x_4430_, 1, v_x3_4429_);
    v___x_4431_ = lean_array_push(v_x1_4427_, v___x_4430_);
    return v___x_4431_;
}
pub unsafe fn l_Std_DHashMap_Raw_toArray___redArg___lam__1(
    mut v___x_4432_: *mut crate::leanh::LeanObject,
    mut v___f_4433_: *mut crate::leanh::LeanObject,
    mut v_acc_4434_: *mut crate::leanh::LeanObject,
    mut v_l_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4436_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4432_,
        v___f_4433_,
        v_acc_4434_,
        v_l_4435_,
    );
    return v___x_4436_;
}
pub unsafe fn l_Std_DHashMap_Raw_toArray___redArg(
    mut v_m_4441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    v_size_4442_ = crate::leanh::lean_ctor_get(v_m_4441_, 0);
    crate::leanh::lean_inc(v_size_4442_);
    v_buckets_4443_ = crate::leanh::lean_ctor_get(v_m_4441_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4443_);
    crate::leanh::lean_dec_ref(v_m_4441_);
    v___x_4444_ = lean_mk_empty_array_with_capacity(v_size_4442_);
    crate::leanh::lean_dec(v_size_4442_);
    v___x_4445_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4446_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4447_ = lean_array_get_size(v_buckets_4443_);
    v___x_4448_ = lean_nat_dec_lt(v___x_4446_, v___x_4447_);
    if v___x_4448_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4443_);
        return v___x_4444_;
    } else {
        let mut v___f_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4450_: u8 = 0;
        v___f_4449_ = l_Std_DHashMap_Raw_toArray___redArg___closed__1;
        v___x_4450_ = lean_nat_dec_le(v___x_4447_, v___x_4447_);
        if v___x_4450_ == 0 {
            if v___x_4448_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4443_);
                return v___x_4444_;
            } else {
                let mut v___x_4451_: usize = 0;
                let mut v___x_4452_: usize = 0;
                let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4451_ = 0usize;
                v___x_4452_ = lean_usize_of_nat(v___x_4447_);
                v___x_4453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4445_,
                    v___f_4449_,
                    v_buckets_4443_,
                    v___x_4451_,
                    v___x_4452_,
                    v___x_4444_,
                );
                return v___x_4453_;
            }
        } else {
            let mut v___x_4454_: usize = 0;
            let mut v___x_4455_: usize = 0;
            let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4454_ = 0usize;
            v___x_4455_ = lean_usize_of_nat(v___x_4447_);
            v___x_4456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4445_,
                v___f_4449_,
                v_buckets_4443_,
                v___x_4454_,
                v___x_4455_,
                v___x_4444_,
            );
            return v___x_4456_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_toArray(
    mut v_00_u03b1_4457_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4458_: *mut crate::leanh::LeanObject,
    mut v_m_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: u8 = 0;
    v_size_4460_ = crate::leanh::lean_ctor_get(v_m_4459_, 0);
    crate::leanh::lean_inc(v_size_4460_);
    v_buckets_4461_ = crate::leanh::lean_ctor_get(v_m_4459_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4461_);
    crate::leanh::lean_dec_ref(v_m_4459_);
    v___x_4462_ = lean_mk_empty_array_with_capacity(v_size_4460_);
    crate::leanh::lean_dec(v_size_4460_);
    v___x_4463_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4464_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4465_ = lean_array_get_size(v_buckets_4461_);
    v___x_4466_ = lean_nat_dec_lt(v___x_4464_, v___x_4465_);
    if v___x_4466_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4461_);
        return v___x_4462_;
    } else {
        let mut v___f_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4468_: u8 = 0;
        v___f_4467_ = l_Std_DHashMap_Raw_toArray___redArg___closed__1;
        v___x_4468_ = lean_nat_dec_le(v___x_4465_, v___x_4465_);
        if v___x_4468_ == 0 {
            if v___x_4466_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4461_);
                return v___x_4462_;
            } else {
                let mut v___x_4469_: usize = 0;
                let mut v___x_4470_: usize = 0;
                let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4469_ = 0usize;
                v___x_4470_ = lean_usize_of_nat(v___x_4465_);
                v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4463_,
                    v___f_4467_,
                    v_buckets_4461_,
                    v___x_4469_,
                    v___x_4470_,
                    v___x_4462_,
                );
                return v___x_4471_;
            }
        } else {
            let mut v___x_4472_: usize = 0;
            let mut v___x_4473_: usize = 0;
            let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4472_ = 0usize;
            v___x_4473_ = lean_usize_of_nat(v___x_4465_);
            v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4463_,
                v___f_4467_,
                v_buckets_4461_,
                v___x_4472_,
                v___x_4473_,
                v___x_4462_,
            );
            return v___x_4474_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(
    mut v_x1_4475_: *mut crate::leanh::LeanObject,
    mut v_x2_4476_: *mut crate::leanh::LeanObject,
    mut v_x3_4477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4478_, 0, v_x2_4476_);
    crate::leanh::lean_ctor_set(v___x_4478_, 1, v_x3_4477_);
    v___x_4479_ = lean_array_push(v_x1_4475_, v___x_4478_);
    return v___x_4479_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(
    mut v___x_4480_: *mut crate::leanh::LeanObject,
    mut v___f_4481_: *mut crate::leanh::LeanObject,
    mut v_acc_4482_: *mut crate::leanh::LeanObject,
    mut v_l_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4480_,
        v___f_4481_,
        v_acc_4482_,
        v_l_4483_,
    );
    return v___x_4484_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toArray___redArg(
    mut v_m_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    v_size_4490_ = crate::leanh::lean_ctor_get(v_m_4489_, 0);
    crate::leanh::lean_inc(v_size_4490_);
    v_buckets_4491_ = crate::leanh::lean_ctor_get(v_m_4489_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4491_);
    crate::leanh::lean_dec_ref(v_m_4489_);
    v___x_4492_ = lean_mk_empty_array_with_capacity(v_size_4490_);
    crate::leanh::lean_dec(v_size_4490_);
    v___x_4493_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4494_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4495_ = lean_array_get_size(v_buckets_4491_);
    v___x_4496_ = lean_nat_dec_lt(v___x_4494_, v___x_4495_);
    if v___x_4496_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4491_);
        return v___x_4492_;
    } else {
        let mut v___f_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4498_: u8 = 0;
        v___f_4497_ = l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1;
        v___x_4498_ = lean_nat_dec_le(v___x_4495_, v___x_4495_);
        if v___x_4498_ == 0 {
            if v___x_4496_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4491_);
                return v___x_4492_;
            } else {
                let mut v___x_4499_: usize = 0;
                let mut v___x_4500_: usize = 0;
                let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4499_ = 0usize;
                v___x_4500_ = lean_usize_of_nat(v___x_4495_);
                v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4493_,
                    v___f_4497_,
                    v_buckets_4491_,
                    v___x_4499_,
                    v___x_4500_,
                    v___x_4492_,
                );
                return v___x_4501_;
            }
        } else {
            let mut v___x_4502_: usize = 0;
            let mut v___x_4503_: usize = 0;
            let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4502_ = 0usize;
            v___x_4503_ = lean_usize_of_nat(v___x_4495_);
            v___x_4504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4493_,
                v___f_4497_,
                v_buckets_4491_,
                v___x_4502_,
                v___x_4503_,
                v___x_4492_,
            );
            return v___x_4504_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toArray(
    mut v_00_u03b1_4505_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4506_: *mut crate::leanh::LeanObject,
    mut v_m_4507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    v_size_4508_ = crate::leanh::lean_ctor_get(v_m_4507_, 0);
    crate::leanh::lean_inc(v_size_4508_);
    v_buckets_4509_ = crate::leanh::lean_ctor_get(v_m_4507_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4509_);
    crate::leanh::lean_dec_ref(v_m_4507_);
    v___x_4510_ = lean_mk_empty_array_with_capacity(v_size_4508_);
    crate::leanh::lean_dec(v_size_4508_);
    v___x_4511_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4512_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4513_ = lean_array_get_size(v_buckets_4509_);
    v___x_4514_ = lean_nat_dec_lt(v___x_4512_, v___x_4513_);
    if v___x_4514_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4509_);
        return v___x_4510_;
    } else {
        let mut v___f_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4516_: u8 = 0;
        v___f_4515_ = l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1;
        v___x_4516_ = lean_nat_dec_le(v___x_4513_, v___x_4513_);
        if v___x_4516_ == 0 {
            if v___x_4514_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4509_);
                return v___x_4510_;
            } else {
                let mut v___x_4517_: usize = 0;
                let mut v___x_4518_: usize = 0;
                let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4517_ = 0usize;
                v___x_4518_ = lean_usize_of_nat(v___x_4513_);
                v___x_4519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4511_,
                    v___f_4515_,
                    v_buckets_4509_,
                    v___x_4517_,
                    v___x_4518_,
                    v___x_4510_,
                );
                return v___x_4519_;
            }
        } else {
            let mut v___x_4520_: usize = 0;
            let mut v___x_4521_: usize = 0;
            let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4520_ = 0usize;
            v___x_4521_ = lean_usize_of_nat(v___x_4513_);
            v___x_4522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4511_,
                v___f_4515_,
                v_buckets_4509_,
                v___x_4520_,
                v___x_4521_,
                v___x_4510_,
            );
            return v___x_4522_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray___redArg___lam__0(
    mut v_x1_4523_: *mut crate::leanh::LeanObject,
    mut v_x2_4524_: *mut crate::leanh::LeanObject,
    mut v_x3_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = lean_array_push(v_x1_4523_, v_x2_4524_);
    return v___x_4526_;
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(
    mut v_x1_4527_: *mut crate::leanh::LeanObject,
    mut v_x2_4528_: *mut crate::leanh::LeanObject,
    mut v_x3_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4530_ =
        l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_4527_, v_x2_4528_, v_x3_4529_);
    crate::leanh::lean_dec(v_x3_4529_);
    return v_res_4530_;
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray___redArg___lam__1(
    mut v___x_4531_: *mut crate::leanh::LeanObject,
    mut v___f_4532_: *mut crate::leanh::LeanObject,
    mut v_acc_4533_: *mut crate::leanh::LeanObject,
    mut v_l_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4531_,
        v___f_4532_,
        v_acc_4533_,
        v_l_4534_,
    );
    return v___x_4535_;
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray___redArg(
    mut v_m_4540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    v_size_4541_ = crate::leanh::lean_ctor_get(v_m_4540_, 0);
    crate::leanh::lean_inc(v_size_4541_);
    v_buckets_4542_ = crate::leanh::lean_ctor_get(v_m_4540_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4542_);
    crate::leanh::lean_dec_ref(v_m_4540_);
    v___x_4543_ = lean_mk_empty_array_with_capacity(v_size_4541_);
    crate::leanh::lean_dec(v_size_4541_);
    v___x_4544_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4545_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4546_ = lean_array_get_size(v_buckets_4542_);
    v___x_4547_ = lean_nat_dec_lt(v___x_4545_, v___x_4546_);
    if v___x_4547_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4542_);
        return v___x_4543_;
    } else {
        let mut v___f_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4549_: u8 = 0;
        v___f_4548_ = l_Std_DHashMap_Raw_keysArray___redArg___closed__1;
        v___x_4549_ = lean_nat_dec_le(v___x_4546_, v___x_4546_);
        if v___x_4549_ == 0 {
            if v___x_4547_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4542_);
                return v___x_4543_;
            } else {
                let mut v___x_4550_: usize = 0;
                let mut v___x_4551_: usize = 0;
                let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4550_ = 0usize;
                v___x_4551_ = lean_usize_of_nat(v___x_4546_);
                v___x_4552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4544_,
                    v___f_4548_,
                    v_buckets_4542_,
                    v___x_4550_,
                    v___x_4551_,
                    v___x_4543_,
                );
                return v___x_4552_;
            }
        } else {
            let mut v___x_4553_: usize = 0;
            let mut v___x_4554_: usize = 0;
            let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4553_ = 0usize;
            v___x_4554_ = lean_usize_of_nat(v___x_4546_);
            v___x_4555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4544_,
                v___f_4548_,
                v_buckets_4542_,
                v___x_4553_,
                v___x_4554_,
                v___x_4543_,
            );
            return v___x_4555_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray(
    mut v_00_u03b1_4556_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4557_: *mut crate::leanh::LeanObject,
    mut v_m_4558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: u8 = 0;
    v_size_4559_ = crate::leanh::lean_ctor_get(v_m_4558_, 0);
    crate::leanh::lean_inc(v_size_4559_);
    v_buckets_4560_ = crate::leanh::lean_ctor_get(v_m_4558_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4560_);
    crate::leanh::lean_dec_ref(v_m_4558_);
    v___x_4561_ = lean_mk_empty_array_with_capacity(v_size_4559_);
    crate::leanh::lean_dec(v_size_4559_);
    v___x_4562_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4563_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4564_ = lean_array_get_size(v_buckets_4560_);
    v___x_4565_ = lean_nat_dec_lt(v___x_4563_, v___x_4564_);
    if v___x_4565_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4560_);
        return v___x_4561_;
    } else {
        let mut v___f_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4567_: u8 = 0;
        v___f_4566_ = l_Std_DHashMap_Raw_keysArray___redArg___closed__1;
        v___x_4567_ = lean_nat_dec_le(v___x_4564_, v___x_4564_);
        if v___x_4567_ == 0 {
            if v___x_4565_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4560_);
                return v___x_4561_;
            } else {
                let mut v___x_4568_: usize = 0;
                let mut v___x_4569_: usize = 0;
                let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4568_ = 0usize;
                v___x_4569_ = lean_usize_of_nat(v___x_4564_);
                v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4562_,
                    v___f_4566_,
                    v_buckets_4560_,
                    v___x_4568_,
                    v___x_4569_,
                    v___x_4561_,
                );
                return v___x_4570_;
            }
        } else {
            let mut v___x_4571_: usize = 0;
            let mut v___x_4572_: usize = 0;
            let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4571_ = 0usize;
            v___x_4572_ = lean_usize_of_nat(v___x_4564_);
            v___x_4573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4562_,
                v___f_4566_,
                v_buckets_4560_,
                v___x_4571_,
                v___x_4572_,
                v___x_4561_,
            );
            return v___x_4573_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_union___redArg___lam__0(
    mut v_inst_4574_: *mut crate::leanh::LeanObject,
    mut v_inst_4575_: *mut crate::leanh::LeanObject,
    mut v_a_4576_: *mut crate::leanh::LeanObject,
    mut v_b_4577_: *mut crate::leanh::LeanObject,
    mut v_acc_4578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_4579_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_4574_,
        v_inst_4575_,
        v_acc_4578_,
        v_a_4576_,
        v_b_4577_,
    );
    v___x_4580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4580_, 0, v_r_4579_);
    return v___x_4580_;
}
pub unsafe fn l_Std_DHashMap_Raw_union___redArg___lam__1(
    mut v___x_4581_: *mut crate::leanh::LeanObject,
    mut v___f_4582_: *mut crate::leanh::LeanObject,
    mut v_a_4583_: *mut crate::leanh::LeanObject,
    mut v_x_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4586_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_4581_, v___f_4582_, v_a_4583_, v___y_4585_);
    return v___x_4586_;
}
pub unsafe fn l_Std_DHashMap_Raw_union___redArg(
    mut v_inst_4589_: *mut crate::leanh::LeanObject,
    mut v_inst_4590_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4591_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: u8 = 0;
    v_size_4593_ = crate::leanh::lean_ctor_get(v_m_u2081_4591_, 0);
    v_buckets_4594_ = crate::leanh::lean_ctor_get(v_m_u2081_4591_, 1);
    v___x_4595_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4596_ = lean_array_get_size(v_buckets_4594_);
    v___x_4597_ = lean_nat_dec_lt(v___x_4595_, v___x_4596_);
    if v___x_4597_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_4591_);
        crate::leanh::lean_dec_ref(v_inst_4590_);
        crate::leanh::lean_dec_ref(v_inst_4589_);
        return v_m_u2082_4592_;
    } else {
        let mut v_size_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4601_: u8 = 0;
        v_size_4598_ = crate::leanh::lean_ctor_get(v_m_u2082_4592_, 0);
        v_buckets_4599_ = crate::leanh::lean_ctor_get(v_m_u2082_4592_, 1);
        v___x_4600_ = lean_array_get_size(v_buckets_4599_);
        v___x_4601_ = lean_nat_dec_lt(v___x_4595_, v___x_4600_);
        if v___x_4601_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4592_);
            crate::leanh::lean_dec_ref(v_inst_4590_);
            crate::leanh::lean_dec_ref(v_inst_4589_);
            return v_m_u2081_4591_;
        } else {
            let mut v___x_4602_: u8 = 0;
            v___x_4602_ = lean_nat_dec_le(v_size_4593_, v_size_4598_);
            if v___x_4602_ == 0 {
                let mut v___f_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_4603_ = l_Std_DHashMap_Raw_union___redArg___closed__0;
                v___x_4604_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
                    v___f_4603_,
                    v_inst_4589_,
                    v_inst_4590_,
                    v_m_u2081_4591_,
                    v_m_u2082_4592_,
                );
                return v___x_4604_;
            } else {
                let mut v___f_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_4608_: usize = 0;
                let mut v___x_4609_: usize = 0;
                let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_buckets_4594_);
                crate::leanh::lean_dec_ref(v_m_u2081_4591_);
                v___f_4605_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4605_, 0, v_inst_4589_);
                crate::leanh::lean_closure_set(v___f_4605_, 1, v_inst_4590_);
                v___x_4606_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
                v___f_4607_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4607_, 0, v___x_4606_);
                crate::leanh::lean_closure_set(v___f_4607_, 1, v___f_4605_);
                v_sz_4608_ = lean_array_size(v_buckets_4594_);
                v___x_4609_ = 0usize;
                v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4606_,
                    v_buckets_4594_,
                    v___f_4607_,
                    v_sz_4608_,
                    v___x_4609_,
                    v_m_u2082_4592_,
                );
                return v___x_4610_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_union(
    mut v_00_u03b1_4611_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4612_: *mut crate::leanh::LeanObject,
    mut v_inst_4613_: *mut crate::leanh::LeanObject,
    mut v_inst_4614_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4615_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    v_size_4617_ = crate::leanh::lean_ctor_get(v_m_u2081_4615_, 0);
    v_buckets_4618_ = crate::leanh::lean_ctor_get(v_m_u2081_4615_, 1);
    v___x_4619_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4620_ = lean_array_get_size(v_buckets_4618_);
    v___x_4621_ = lean_nat_dec_lt(v___x_4619_, v___x_4620_);
    if v___x_4621_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_4615_);
        crate::leanh::lean_dec_ref(v_inst_4614_);
        crate::leanh::lean_dec_ref(v_inst_4613_);
        return v_m_u2082_4616_;
    } else {
        let mut v_size_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4625_: u8 = 0;
        v_size_4622_ = crate::leanh::lean_ctor_get(v_m_u2082_4616_, 0);
        v_buckets_4623_ = crate::leanh::lean_ctor_get(v_m_u2082_4616_, 1);
        v___x_4624_ = lean_array_get_size(v_buckets_4623_);
        v___x_4625_ = lean_nat_dec_lt(v___x_4619_, v___x_4624_);
        if v___x_4625_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4616_);
            crate::leanh::lean_dec_ref(v_inst_4614_);
            crate::leanh::lean_dec_ref(v_inst_4613_);
            return v_m_u2081_4615_;
        } else {
            let mut v___x_4626_: u8 = 0;
            v___x_4626_ = lean_nat_dec_le(v_size_4617_, v_size_4622_);
            if v___x_4626_ == 0 {
                let mut v___f_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_4627_ = l_Std_DHashMap_Raw_union___redArg___closed__0;
                v___x_4628_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
                    v___f_4627_,
                    v_inst_4613_,
                    v_inst_4614_,
                    v_m_u2081_4615_,
                    v_m_u2082_4616_,
                );
                return v___x_4628_;
            } else {
                let mut v___f_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_4632_: usize = 0;
                let mut v___x_4633_: usize = 0;
                let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_buckets_4618_);
                crate::leanh::lean_dec_ref(v_m_u2081_4615_);
                v___f_4629_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4629_, 0, v_inst_4613_);
                crate::leanh::lean_closure_set(v___f_4629_, 1, v_inst_4614_);
                v___x_4630_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
                v___f_4631_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4631_, 0, v___x_4630_);
                crate::leanh::lean_closure_set(v___f_4631_, 1, v___f_4629_);
                v_sz_4632_ = lean_array_size(v_buckets_4618_);
                v___x_4633_ = 0usize;
                v___x_4634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4630_,
                    v_buckets_4618_,
                    v___f_4631_,
                    v_sz_4632_,
                    v___x_4633_,
                    v_m_u2082_4616_,
                );
                return v___x_4634_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(
    mut v_inst_4635_: *mut crate::leanh::LeanObject,
    mut v_inst_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4637_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4637_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4637_, 2, v_inst_4635_);
    crate::leanh::lean_closure_set(v___x_4637_, 3, v_inst_4636_);
    return v___x_4637_;
}
pub unsafe fn l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(
    mut v_00_u03b1_4638_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4639_: *mut crate::leanh::LeanObject,
    mut v_inst_4640_: *mut crate::leanh::LeanObject,
    mut v_inst_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4642_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4642_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4642_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4642_, 2, v_inst_4640_);
    crate::leanh::lean_closure_set(v___x_4642_, 3, v_inst_4641_);
    return v___x_4642_;
}
pub unsafe fn l_Std_DHashMap_Raw_inter___redArg(
    mut v_inst_4643_: *mut crate::leanh::LeanObject,
    mut v_inst_4644_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4645_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: u8 = 0;
    v_buckets_4647_ = crate::leanh::lean_ctor_get(v_m_u2081_4645_, 1);
    v___x_4648_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4649_ = lean_array_get_size(v_buckets_4647_);
    v___x_4650_ = lean_nat_dec_lt(v___x_4648_, v___x_4649_);
    if v___x_4650_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_4645_);
        crate::leanh::lean_dec_ref(v_inst_4644_);
        crate::leanh::lean_dec_ref(v_inst_4643_);
        return v_m_u2082_4646_;
    } else {
        let mut v_buckets_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4653_: u8 = 0;
        v_buckets_4651_ = crate::leanh::lean_ctor_get(v_m_u2082_4646_, 1);
        v___x_4652_ = lean_array_get_size(v_buckets_4651_);
        v___x_4653_ = lean_nat_dec_lt(v___x_4648_, v___x_4652_);
        if v___x_4653_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4646_);
            crate::leanh::lean_dec_ref(v_inst_4644_);
            crate::leanh::lean_dec_ref(v_inst_4643_);
            return v_m_u2081_4645_;
        } else {
            let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4654_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
                v_inst_4643_,
                v_inst_4644_,
                v_m_u2081_4645_,
                v_m_u2082_4646_,
            );
            return v___x_4654_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_inter(
    mut v_00_u03b1_4655_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4656_: *mut crate::leanh::LeanObject,
    mut v_inst_4657_: *mut crate::leanh::LeanObject,
    mut v_inst_4658_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4659_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: u8 = 0;
    v_buckets_4661_ = crate::leanh::lean_ctor_get(v_m_u2081_4659_, 1);
    v___x_4662_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4663_ = lean_array_get_size(v_buckets_4661_);
    v___x_4664_ = lean_nat_dec_lt(v___x_4662_, v___x_4663_);
    if v___x_4664_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_4659_);
        crate::leanh::lean_dec_ref(v_inst_4658_);
        crate::leanh::lean_dec_ref(v_inst_4657_);
        return v_m_u2082_4660_;
    } else {
        let mut v_buckets_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4667_: u8 = 0;
        v_buckets_4665_ = crate::leanh::lean_ctor_get(v_m_u2082_4660_, 1);
        v___x_4666_ = lean_array_get_size(v_buckets_4665_);
        v___x_4667_ = lean_nat_dec_lt(v___x_4662_, v___x_4666_);
        if v___x_4667_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4660_);
            crate::leanh::lean_dec_ref(v_inst_4658_);
            crate::leanh::lean_dec_ref(v_inst_4657_);
            return v_m_u2081_4659_;
        } else {
            let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4668_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
                v_inst_4657_,
                v_inst_4658_,
                v_m_u2081_4659_,
                v_m_u2082_4660_,
            );
            return v___x_4668_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(
    mut v_inst_4669_: *mut crate::leanh::LeanObject,
    mut v_inst_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4671_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4671_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4671_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4671_, 2, v_inst_4669_);
    crate::leanh::lean_closure_set(v___x_4671_, 3, v_inst_4670_);
    return v___x_4671_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInterOfBEqOfHashable(
    mut v_00_u03b1_4672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4673_: *mut crate::leanh::LeanObject,
    mut v_inst_4674_: *mut crate::leanh::LeanObject,
    mut v_inst_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4676_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4676_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4676_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4676_, 2, v_inst_4674_);
    crate::leanh::lean_closure_set(v___x_4676_, 3, v_inst_4675_);
    return v___x_4676_;
}
pub unsafe fn l_Std_DHashMap_Raw_beq___redArg(
    mut v_inst_4677_: *mut crate::leanh::LeanObject,
    mut v_inst_4678_: *mut crate::leanh::LeanObject,
    mut v_inst_4679_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4680_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4681_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: u8 = 0;
    v_buckets_4682_ = crate::leanh::lean_ctor_get(v_m_u2081_4680_, 1);
    v___x_4683_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4684_ = lean_array_get_size(v_buckets_4682_);
    v___x_4685_ = lean_nat_dec_lt(v___x_4683_, v___x_4684_);
    if v___x_4685_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2082_4681_);
        crate::leanh::lean_dec_ref(v_m_u2081_4680_);
        crate::leanh::lean_dec_ref(v_inst_4679_);
        crate::leanh::lean_dec_ref(v_inst_4678_);
        crate::leanh::lean_dec_ref(v_inst_4677_);
        return v___x_4685_;
    } else {
        let mut v_buckets_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4688_: u8 = 0;
        v_buckets_4686_ = crate::leanh::lean_ctor_get(v_m_u2082_4681_, 1);
        v___x_4687_ = lean_array_get_size(v_buckets_4686_);
        v___x_4688_ = lean_nat_dec_lt(v___x_4683_, v___x_4687_);
        if v___x_4688_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4681_);
            crate::leanh::lean_dec_ref(v_m_u2081_4680_);
            crate::leanh::lean_dec_ref(v_inst_4679_);
            crate::leanh::lean_dec_ref(v_inst_4678_);
            crate::leanh::lean_dec_ref(v_inst_4677_);
            return v___x_4688_;
        } else {
            let mut v___x_4689_: u8 = 0;
            v___x_4689_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
                v_inst_4677_,
                v_inst_4678_,
                v_inst_4679_,
                v_m_u2081_4680_,
                v_m_u2082_4681_,
            );
            return v___x_4689_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_beq___redArg___boxed(
    mut v_inst_4690_: *mut crate::leanh::LeanObject,
    mut v_inst_4691_: *mut crate::leanh::LeanObject,
    mut v_inst_4692_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4693_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4695_: u8 = 0;
    let mut v_r_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4695_ = l_Std_DHashMap_Raw_beq___redArg(
        v_inst_4690_,
        v_inst_4691_,
        v_inst_4692_,
        v_m_u2081_4693_,
        v_m_u2082_4694_,
    );
    v_r_4696_ = crate::leanh::lean_box((v_res_4695_) as usize);
    return v_r_4696_;
}
pub unsafe fn l_Std_DHashMap_Raw_beq(
    mut v_00_u03b1_4697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4698_: *mut crate::leanh::LeanObject,
    mut v_inst_4699_: *mut crate::leanh::LeanObject,
    mut v_inst_4700_: *mut crate::leanh::LeanObject,
    mut v_inst_4701_: *mut crate::leanh::LeanObject,
    mut v_inst_4702_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4703_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4704_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4705_: u8 = 0;
    v___x_4705_ = l_Std_DHashMap_Raw_beq___redArg(
        v_inst_4699_,
        v_inst_4700_,
        v_inst_4702_,
        v_m_u2081_4703_,
        v_m_u2082_4704_,
    );
    return v___x_4705_;
}
pub unsafe fn l_Std_DHashMap_Raw_beq___boxed(
    mut v_00_u03b1_4706_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4707_: *mut crate::leanh::LeanObject,
    mut v_inst_4708_: *mut crate::leanh::LeanObject,
    mut v_inst_4709_: *mut crate::leanh::LeanObject,
    mut v_inst_4710_: *mut crate::leanh::LeanObject,
    mut v_inst_4711_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4712_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4714_: u8 = 0;
    let mut v_r_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4714_ = l_Std_DHashMap_Raw_beq(
        v_00_u03b1_4706_,
        v_00_u03b2_4707_,
        v_inst_4708_,
        v_inst_4709_,
        v_inst_4710_,
        v_inst_4711_,
        v_m_u2081_4712_,
        v_m_u2082_4713_,
    );
    v_r_4715_ = crate::leanh::lean_box((v_res_4714_) as usize);
    return v_r_4715_;
}
pub unsafe fn l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(
    mut v_inst_4716_: *mut crate::leanh::LeanObject,
    mut v_inst_4717_: *mut crate::leanh::LeanObject,
    mut v_inst_4718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4719_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_4719_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4719_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4719_, 2, v_inst_4716_);
    crate::leanh::lean_closure_set(v___x_4719_, 3, v_inst_4717_);
    crate::leanh::lean_closure_set(v___x_4719_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4719_, 5, v_inst_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(
    mut v_00_u03b1_4720_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4721_: *mut crate::leanh::LeanObject,
    mut v_inst_4722_: *mut crate::leanh::LeanObject,
    mut v_inst_4723_: *mut crate::leanh::LeanObject,
    mut v_inst_4724_: *mut crate::leanh::LeanObject,
    mut v_inst_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4726_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_4726_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4726_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4726_, 2, v_inst_4722_);
    crate::leanh::lean_closure_set(v___x_4726_, 3, v_inst_4723_);
    crate::leanh::lean_closure_set(v___x_4726_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4726_, 5, v_inst_4725_);
    return v___x_4726_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_beq___redArg(
    mut v_inst_4727_: *mut crate::leanh::LeanObject,
    mut v_inst_4728_: *mut crate::leanh::LeanObject,
    mut v_inst_4729_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4730_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4731_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: u8 = 0;
    v_buckets_4732_ = crate::leanh::lean_ctor_get(v_m_u2081_4730_, 1);
    v___x_4733_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4734_ = lean_array_get_size(v_buckets_4732_);
    v___x_4735_ = lean_nat_dec_lt(v___x_4733_, v___x_4734_);
    if v___x_4735_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2082_4731_);
        crate::leanh::lean_dec_ref(v_m_u2081_4730_);
        crate::leanh::lean_dec_ref(v_inst_4729_);
        crate::leanh::lean_dec_ref(v_inst_4728_);
        crate::leanh::lean_dec_ref(v_inst_4727_);
        return v___x_4735_;
    } else {
        let mut v_buckets_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4738_: u8 = 0;
        v_buckets_4736_ = crate::leanh::lean_ctor_get(v_m_u2082_4731_, 1);
        v___x_4737_ = lean_array_get_size(v_buckets_4736_);
        v___x_4738_ = lean_nat_dec_lt(v___x_4733_, v___x_4737_);
        if v___x_4738_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4731_);
            crate::leanh::lean_dec_ref(v_m_u2081_4730_);
            crate::leanh::lean_dec_ref(v_inst_4729_);
            crate::leanh::lean_dec_ref(v_inst_4728_);
            crate::leanh::lean_dec_ref(v_inst_4727_);
            return v___x_4738_;
        } else {
            let mut v___x_4739_: u8 = 0;
            v___x_4739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
                v_inst_4727_,
                v_inst_4728_,
                v_inst_4729_,
                v_m_u2081_4730_,
                v_m_u2082_4731_,
            );
            return v___x_4739_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_beq___redArg___boxed(
    mut v_inst_4740_: *mut crate::leanh::LeanObject,
    mut v_inst_4741_: *mut crate::leanh::LeanObject,
    mut v_inst_4742_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4743_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4745_: u8 = 0;
    let mut v_r_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4745_ = l_Std_DHashMap_Raw_Const_beq___redArg(
        v_inst_4740_,
        v_inst_4741_,
        v_inst_4742_,
        v_m_u2081_4743_,
        v_m_u2082_4744_,
    );
    v_r_4746_ = crate::leanh::lean_box((v_res_4745_) as usize);
    return v_r_4746_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_beq(
    mut v_00_u03b1_4747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4748_: *mut crate::leanh::LeanObject,
    mut v_inst_4749_: *mut crate::leanh::LeanObject,
    mut v_inst_4750_: *mut crate::leanh::LeanObject,
    mut v_inst_4751_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4752_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4753_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4754_: u8 = 0;
    v___x_4754_ = l_Std_DHashMap_Raw_Const_beq___redArg(
        v_inst_4749_,
        v_inst_4750_,
        v_inst_4751_,
        v_m_u2081_4752_,
        v_m_u2082_4753_,
    );
    return v___x_4754_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_beq___boxed(
    mut v_00_u03b1_4755_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4756_: *mut crate::leanh::LeanObject,
    mut v_inst_4757_: *mut crate::leanh::LeanObject,
    mut v_inst_4758_: *mut crate::leanh::LeanObject,
    mut v_inst_4759_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4760_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4762_: u8 = 0;
    let mut v_r_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4762_ = l_Std_DHashMap_Raw_Const_beq(
        v_00_u03b1_4755_,
        v_00_u03b2_4756_,
        v_inst_4757_,
        v_inst_4758_,
        v_inst_4759_,
        v_m_u2081_4760_,
        v_m_u2082_4761_,
    );
    v_r_4763_ = crate::leanh::lean_box((v_res_4762_) as usize);
    return v_r_4763_;
}
pub unsafe fn l_Std_DHashMap_Raw_diff___redArg___lam__0(
    mut v_inst_4764_: *mut crate::leanh::LeanObject,
    mut v_inst_4765_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4766_: *mut crate::leanh::LeanObject,
    mut v___x_4767_: u8,
    mut v_k_4768_: *mut crate::leanh::LeanObject,
    mut v_x_4769_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4770_: u8 = 0;
    v___x_4770_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_4764_,
        v_inst_4765_,
        v_m_u2082_4766_,
        v_k_4768_,
    );
    if v___x_4770_ == 0 {
        return v___x_4767_;
    } else {
        let mut v___x_4771_: u8 = 0;
        v___x_4771_ = 0;
        return v___x_4771_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(
    mut v_inst_4772_: *mut crate::leanh::LeanObject,
    mut v_inst_4773_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4774_: *mut crate::leanh::LeanObject,
    mut v___x_4775_: *mut crate::leanh::LeanObject,
    mut v_k_4776_: *mut crate::leanh::LeanObject,
    mut v_x_4777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_92__boxed_4778_: u8 = 0;
    let mut v_res_4779_: u8 = 0;
    let mut v_r_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_92__boxed_4778_ = (crate::leanh::lean_unbox(v___x_4775_) as u8);
    v_res_4779_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(
        v_inst_4772_,
        v_inst_4773_,
        v_m_u2082_4774_,
        v___x_92__boxed_4778_,
        v_k_4776_,
        v_x_4777_,
    );
    crate::leanh::lean_dec(v_x_4777_);
    crate::leanh::lean_dec_ref(v_m_u2082_4774_);
    v_r_4780_ = crate::leanh::lean_box((v_res_4779_) as usize);
    return v_r_4780_;
}
pub unsafe fn l_Std_DHashMap_Raw_diff___redArg(
    mut v_inst_4781_: *mut crate::leanh::LeanObject,
    mut v_inst_4782_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4783_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: u8 = 0;
    v_size_4785_ = crate::leanh::lean_ctor_get(v_m_u2081_4783_, 0);
    v_buckets_4786_ = crate::leanh::lean_ctor_get(v_m_u2081_4783_, 1);
    v___x_4787_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4788_ = lean_array_get_size(v_buckets_4786_);
    v___x_4789_ = lean_nat_dec_lt(v___x_4787_, v___x_4788_);
    if v___x_4789_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_4783_);
        crate::leanh::lean_dec_ref(v_inst_4782_);
        crate::leanh::lean_dec_ref(v_inst_4781_);
        return v_m_u2082_4784_;
    } else {
        let mut v_size_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4793_: u8 = 0;
        v_size_4790_ = crate::leanh::lean_ctor_get(v_m_u2082_4784_, 0);
        v_buckets_4791_ = crate::leanh::lean_ctor_get(v_m_u2082_4784_, 1);
        v___x_4792_ = lean_array_get_size(v_buckets_4791_);
        v___x_4793_ = lean_nat_dec_lt(v___x_4787_, v___x_4792_);
        if v___x_4793_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4784_);
            crate::leanh::lean_dec_ref(v_inst_4782_);
            crate::leanh::lean_dec_ref(v_inst_4781_);
            return v_m_u2081_4783_;
        } else {
            let mut v___x_4794_: u8 = 0;
            v___x_4794_ = lean_nat_dec_le(v_size_4785_, v_size_4790_);
            if v___x_4794_ == 0 {
                let mut v___f_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_4795_ = l_Std_DHashMap_Raw_union___redArg___closed__0;
                v___x_4796_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
                    v___f_4795_,
                    v_inst_4781_,
                    v_inst_4782_,
                    v_m_u2081_4783_,
                    v_m_u2082_4784_,
                );
                return v___x_4796_;
            } else {
                let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4797_ = crate::leanh::lean_box((v___x_4794_) as usize);
                v___f_4798_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_4798_, 0, v_inst_4781_);
                crate::leanh::lean_closure_set(v___f_4798_, 1, v_inst_4782_);
                crate::leanh::lean_closure_set(v___f_4798_, 2, v_m_u2082_4784_);
                crate::leanh::lean_closure_set(v___f_4798_, 3, v___x_4797_);
                v___x_4799_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4798_, v_m_u2081_4783_);
                return v___x_4799_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_diff(
    mut v_00_u03b1_4800_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4801_: *mut crate::leanh::LeanObject,
    mut v_inst_4802_: *mut crate::leanh::LeanObject,
    mut v_inst_4803_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4804_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    v_size_4806_ = crate::leanh::lean_ctor_get(v_m_u2081_4804_, 0);
    v_buckets_4807_ = crate::leanh::lean_ctor_get(v_m_u2081_4804_, 1);
    v___x_4808_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4809_ = lean_array_get_size(v_buckets_4807_);
    v___x_4810_ = lean_nat_dec_lt(v___x_4808_, v___x_4809_);
    if v___x_4810_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_4804_);
        crate::leanh::lean_dec_ref(v_inst_4803_);
        crate::leanh::lean_dec_ref(v_inst_4802_);
        return v_m_u2082_4805_;
    } else {
        let mut v_size_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4814_: u8 = 0;
        v_size_4811_ = crate::leanh::lean_ctor_get(v_m_u2082_4805_, 0);
        v_buckets_4812_ = crate::leanh::lean_ctor_get(v_m_u2082_4805_, 1);
        v___x_4813_ = lean_array_get_size(v_buckets_4812_);
        v___x_4814_ = lean_nat_dec_lt(v___x_4808_, v___x_4813_);
        if v___x_4814_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_4805_);
            crate::leanh::lean_dec_ref(v_inst_4803_);
            crate::leanh::lean_dec_ref(v_inst_4802_);
            return v_m_u2081_4804_;
        } else {
            let mut v___x_4815_: u8 = 0;
            v___x_4815_ = lean_nat_dec_le(v_size_4806_, v_size_4811_);
            if v___x_4815_ == 0 {
                let mut v___f_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_4816_ = l_Std_DHashMap_Raw_union___redArg___closed__0;
                v___x_4817_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
                    v___f_4816_,
                    v_inst_4802_,
                    v_inst_4803_,
                    v_m_u2081_4804_,
                    v_m_u2082_4805_,
                );
                return v___x_4817_;
            } else {
                let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4818_ = crate::leanh::lean_box((v___x_4815_) as usize);
                v___f_4819_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_4819_, 0, v_inst_4802_);
                crate::leanh::lean_closure_set(v___f_4819_, 1, v_inst_4803_);
                crate::leanh::lean_closure_set(v___f_4819_, 2, v_m_u2082_4805_);
                crate::leanh::lean_closure_set(v___f_4819_, 3, v___x_4818_);
                v___x_4820_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4819_, v_m_u2081_4804_);
                return v___x_4820_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(
    mut v_inst_4821_: *mut crate::leanh::LeanObject,
    mut v_inst_4822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4823_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4823_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4823_, 2, v_inst_4821_);
    crate::leanh::lean_closure_set(v___x_4823_, 3, v_inst_4822_);
    return v___x_4823_;
}
pub unsafe fn l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(
    mut v_00_u03b1_4824_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4825_: *mut crate::leanh::LeanObject,
    mut v_inst_4826_: *mut crate::leanh::LeanObject,
    mut v_inst_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4828_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4828_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4828_, 2, v_inst_4826_);
    crate::leanh::lean_closure_set(v___x_4828_, 3, v_inst_4827_);
    return v___x_4828_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg___lam__0(
    mut v_a_4829_: *mut crate::leanh::LeanObject,
    mut v_b_4830_: *mut crate::leanh::LeanObject,
    mut v_d_4831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4832_, 0, v_b_4830_);
    crate::leanh::lean_ctor_set(v___x_4832_, 1, v_d_4831_);
    return v___x_4832_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(
    mut v_a_4833_: *mut crate::leanh::LeanObject,
    mut v_b_4834_: *mut crate::leanh::LeanObject,
    mut v_d_4835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4836_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_a_4833_, v_b_4834_, v_d_4835_);
    crate::leanh::lean_dec(v_a_4833_);
    return v_res_4836_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg___lam__1(
    mut v___x_4837_: *mut crate::leanh::LeanObject,
    mut v___f_4838_: *mut crate::leanh::LeanObject,
    mut v_l_4839_: *mut crate::leanh::LeanObject,
    mut v_acc_4840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4841_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_4837_,
        v___f_4838_,
        v_acc_4840_,
        v_l_4839_,
    );
    return v___x_4841_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg(
    mut v_m_4846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    v___x_4847_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4848_ = crate::leanh::lean_ctor_get(v_m_4846_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4848_);
    crate::leanh::lean_dec_ref(v_m_4846_);
    v___x_4849_ = crate::leanh::lean_box(0);
    v___x_4850_ = lean_array_get_size(v_buckets_4848_);
    v___x_4851_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4852_ = lean_nat_dec_lt(v___x_4851_, v___x_4850_);
    if v___x_4852_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4848_);
        return v___x_4849_;
    } else {
        let mut v___f_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4854_: usize = 0;
        let mut v___x_4855_: usize = 0;
        let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4853_ = l_Std_DHashMap_Raw_values___redArg___closed__1;
        v___x_4854_ = lean_usize_of_nat(v___x_4850_);
        v___x_4855_ = 0usize;
        v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4847_,
            v___f_4853_,
            v_buckets_4848_,
            v___x_4854_,
            v___x_4855_,
            v___x_4849_,
        );
        return v___x_4856_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_values(
    mut v_00_u03b1_4857_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4858_: *mut crate::leanh::LeanObject,
    mut v_m_4859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: u8 = 0;
    v___x_4860_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4861_ = crate::leanh::lean_ctor_get(v_m_4859_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4861_);
    crate::leanh::lean_dec_ref(v_m_4859_);
    v___x_4862_ = crate::leanh::lean_box(0);
    v___x_4863_ = lean_array_get_size(v_buckets_4861_);
    v___x_4864_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4865_ = lean_nat_dec_lt(v___x_4864_, v___x_4863_);
    if v___x_4865_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4861_);
        return v___x_4862_;
    } else {
        let mut v___f_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4867_: usize = 0;
        let mut v___x_4868_: usize = 0;
        let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4866_ = l_Std_DHashMap_Raw_values___redArg___closed__1;
        v___x_4867_ = lean_usize_of_nat(v___x_4863_);
        v___x_4868_ = 0usize;
        v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4860_,
            v___f_4866_,
            v_buckets_4861_,
            v___x_4867_,
            v___x_4868_,
            v___x_4862_,
        );
        return v___x_4869_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(
    mut v_x1_4870_: *mut crate::leanh::LeanObject,
    mut v_x2_4871_: *mut crate::leanh::LeanObject,
    mut v_x3_4872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4873_ = lean_array_push(v_x1_4870_, v_x3_4872_);
    return v___x_4873_;
}
pub unsafe fn l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(
    mut v_x1_4874_: *mut crate::leanh::LeanObject,
    mut v_x2_4875_: *mut crate::leanh::LeanObject,
    mut v_x3_4876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4877_ =
        l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_4874_, v_x2_4875_, v_x3_4876_);
    crate::leanh::lean_dec(v_x2_4875_);
    return v_res_4877_;
}
pub unsafe fn l_Std_DHashMap_Raw_valuesArray___redArg(
    mut v_m_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: u8 = 0;
    v_size_4883_ = crate::leanh::lean_ctor_get(v_m_4882_, 0);
    crate::leanh::lean_inc(v_size_4883_);
    v_buckets_4884_ = crate::leanh::lean_ctor_get(v_m_4882_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4884_);
    crate::leanh::lean_dec_ref(v_m_4882_);
    v___x_4885_ = lean_mk_empty_array_with_capacity(v_size_4883_);
    crate::leanh::lean_dec(v_size_4883_);
    v___x_4886_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4887_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4888_ = lean_array_get_size(v_buckets_4884_);
    v___x_4889_ = lean_nat_dec_lt(v___x_4887_, v___x_4888_);
    if v___x_4889_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4884_);
        return v___x_4885_;
    } else {
        let mut v___f_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4891_: u8 = 0;
        v___f_4890_ = l_Std_DHashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4891_ = lean_nat_dec_le(v___x_4888_, v___x_4888_);
        if v___x_4891_ == 0 {
            if v___x_4889_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4884_);
                return v___x_4885_;
            } else {
                let mut v___x_4892_: usize = 0;
                let mut v___x_4893_: usize = 0;
                let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4892_ = 0usize;
                v___x_4893_ = lean_usize_of_nat(v___x_4888_);
                v___x_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4886_,
                    v___f_4890_,
                    v_buckets_4884_,
                    v___x_4892_,
                    v___x_4893_,
                    v___x_4885_,
                );
                return v___x_4894_;
            }
        } else {
            let mut v___x_4895_: usize = 0;
            let mut v___x_4896_: usize = 0;
            let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4895_ = 0usize;
            v___x_4896_ = lean_usize_of_nat(v___x_4888_);
            v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4886_,
                v___f_4890_,
                v_buckets_4884_,
                v___x_4895_,
                v___x_4896_,
                v___x_4885_,
            );
            return v___x_4897_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_valuesArray(
    mut v_00_u03b1_4898_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4899_: *mut crate::leanh::LeanObject,
    mut v_m_4900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: u8 = 0;
    v_size_4901_ = crate::leanh::lean_ctor_get(v_m_4900_, 0);
    crate::leanh::lean_inc(v_size_4901_);
    v_buckets_4902_ = crate::leanh::lean_ctor_get(v_m_4900_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4902_);
    crate::leanh::lean_dec_ref(v_m_4900_);
    v___x_4903_ = lean_mk_empty_array_with_capacity(v_size_4901_);
    crate::leanh::lean_dec(v_size_4901_);
    v___x_4904_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4905_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4906_ = lean_array_get_size(v_buckets_4902_);
    v___x_4907_ = lean_nat_dec_lt(v___x_4905_, v___x_4906_);
    if v___x_4907_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4902_);
        return v___x_4903_;
    } else {
        let mut v___f_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4909_: u8 = 0;
        v___f_4908_ = l_Std_DHashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4909_ = lean_nat_dec_le(v___x_4906_, v___x_4906_);
        if v___x_4909_ == 0 {
            if v___x_4907_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4902_);
                return v___x_4903_;
            } else {
                let mut v___x_4910_: usize = 0;
                let mut v___x_4911_: usize = 0;
                let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4910_ = 0usize;
                v___x_4911_ = lean_usize_of_nat(v___x_4906_);
                v___x_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4904_,
                    v___f_4908_,
                    v_buckets_4902_,
                    v___x_4910_,
                    v___x_4911_,
                    v___x_4903_,
                );
                return v___x_4912_;
            }
        } else {
            let mut v___x_4913_: usize = 0;
            let mut v___x_4914_: usize = 0;
            let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4913_ = 0usize;
            v___x_4914_ = lean_usize_of_nat(v___x_4906_);
            v___x_4915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4904_,
                v___f_4908_,
                v_buckets_4902_,
                v___x_4913_,
                v___x_4914_,
                v___x_4903_,
            );
            return v___x_4915_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_insertMany___redArg(
    mut v_inst_4916_: *mut crate::leanh::LeanObject,
    mut v_inst_4917_: *mut crate::leanh::LeanObject,
    mut v_inst_4918_: *mut crate::leanh::LeanObject,
    mut v_m_4919_: *mut crate::leanh::LeanObject,
    mut v_l_4920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: u8 = 0;
    v_buckets_4921_ = crate::leanh::lean_ctor_get(v_m_4919_, 1);
    v___x_4922_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4923_ = lean_array_get_size(v_buckets_4921_);
    v___x_4924_ = lean_nat_dec_lt(v___x_4922_, v___x_4923_);
    if v___x_4924_ == 0 {
        crate::leanh::lean_dec(v_l_4920_);
        crate::leanh::lean_dec(v_inst_4918_);
        crate::leanh::lean_dec_ref(v_inst_4917_);
        crate::leanh::lean_dec_ref(v_inst_4916_);
        return v_m_4919_;
    } else {
        let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4925_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v_inst_4918_,
            v_inst_4916_,
            v_inst_4917_,
            v_m_4919_,
            v_l_4920_,
        );
        return v___x_4925_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_insertMany(
    mut v_00_u03b1_4926_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4927_: *mut crate::leanh::LeanObject,
    mut v_inst_4928_: *mut crate::leanh::LeanObject,
    mut v_inst_4929_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4930_: *mut crate::leanh::LeanObject,
    mut v_inst_4931_: *mut crate::leanh::LeanObject,
    mut v_m_4932_: *mut crate::leanh::LeanObject,
    mut v_l_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u8 = 0;
    v_buckets_4934_ = crate::leanh::lean_ctor_get(v_m_4932_, 1);
    v___x_4935_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4936_ = lean_array_get_size(v_buckets_4934_);
    v___x_4937_ = lean_nat_dec_lt(v___x_4935_, v___x_4936_);
    if v___x_4937_ == 0 {
        crate::leanh::lean_dec(v_l_4933_);
        crate::leanh::lean_dec(v_inst_4931_);
        crate::leanh::lean_dec_ref(v_inst_4929_);
        crate::leanh::lean_dec_ref(v_inst_4928_);
        return v_m_4932_;
    } else {
        let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4938_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v_inst_4931_,
            v_inst_4928_,
            v_inst_4929_,
            v_m_4932_,
            v_l_4933_,
        );
        return v___x_4938_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_eraseManyEntries___redArg(
    mut v_inst_4939_: *mut crate::leanh::LeanObject,
    mut v_inst_4940_: *mut crate::leanh::LeanObject,
    mut v_inst_4941_: *mut crate::leanh::LeanObject,
    mut v_m_4942_: *mut crate::leanh::LeanObject,
    mut v_l_4943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    v_buckets_4944_ = crate::leanh::lean_ctor_get(v_m_4942_, 1);
    v___x_4945_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4946_ = lean_array_get_size(v_buckets_4944_);
    v___x_4947_ = lean_nat_dec_lt(v___x_4945_, v___x_4946_);
    if v___x_4947_ == 0 {
        crate::leanh::lean_dec(v_l_4943_);
        crate::leanh::lean_dec(v_inst_4941_);
        crate::leanh::lean_dec_ref(v_inst_4940_);
        crate::leanh::lean_dec_ref(v_inst_4939_);
        return v_m_4942_;
    } else {
        let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4948_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v_inst_4941_,
            v_inst_4939_,
            v_inst_4940_,
            v_m_4942_,
            v_l_4943_,
        );
        return v___x_4948_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_eraseManyEntries(
    mut v_00_u03b1_4949_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4950_: *mut crate::leanh::LeanObject,
    mut v_inst_4951_: *mut crate::leanh::LeanObject,
    mut v_inst_4952_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4953_: *mut crate::leanh::LeanObject,
    mut v_inst_4954_: *mut crate::leanh::LeanObject,
    mut v_m_4955_: *mut crate::leanh::LeanObject,
    mut v_l_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: u8 = 0;
    v_buckets_4957_ = crate::leanh::lean_ctor_get(v_m_4955_, 1);
    v___x_4958_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4959_ = lean_array_get_size(v_buckets_4957_);
    v___x_4960_ = lean_nat_dec_lt(v___x_4958_, v___x_4959_);
    if v___x_4960_ == 0 {
        crate::leanh::lean_dec(v_l_4956_);
        crate::leanh::lean_dec(v_inst_4954_);
        crate::leanh::lean_dec_ref(v_inst_4952_);
        crate::leanh::lean_dec_ref(v_inst_4951_);
        return v_m_4955_;
    } else {
        let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4961_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v_inst_4954_,
            v_inst_4951_,
            v_inst_4952_,
            v_m_4955_,
            v_l_4956_,
        );
        return v___x_4961_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_insertMany___redArg(
    mut v_inst_4962_: *mut crate::leanh::LeanObject,
    mut v_inst_4963_: *mut crate::leanh::LeanObject,
    mut v_inst_4964_: *mut crate::leanh::LeanObject,
    mut v_m_4965_: *mut crate::leanh::LeanObject,
    mut v_l_4966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: u8 = 0;
    v_buckets_4967_ = crate::leanh::lean_ctor_get(v_m_4965_, 1);
    v___x_4968_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4969_ = lean_array_get_size(v_buckets_4967_);
    v___x_4970_ = lean_nat_dec_lt(v___x_4968_, v___x_4969_);
    if v___x_4970_ == 0 {
        crate::leanh::lean_dec(v_l_4966_);
        crate::leanh::lean_dec(v_inst_4964_);
        crate::leanh::lean_dec_ref(v_inst_4963_);
        crate::leanh::lean_dec_ref(v_inst_4962_);
        return v_m_4965_;
    } else {
        let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v_inst_4964_,
            v_inst_4962_,
            v_inst_4963_,
            v_m_4965_,
            v_l_4966_,
        );
        return v___x_4971_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_insertMany(
    mut v_00_u03b1_4972_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4973_: *mut crate::leanh::LeanObject,
    mut v_inst_4974_: *mut crate::leanh::LeanObject,
    mut v_inst_4975_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4976_: *mut crate::leanh::LeanObject,
    mut v_inst_4977_: *mut crate::leanh::LeanObject,
    mut v_m_4978_: *mut crate::leanh::LeanObject,
    mut v_l_4979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: u8 = 0;
    v_buckets_4980_ = crate::leanh::lean_ctor_get(v_m_4978_, 1);
    v___x_4981_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4982_ = lean_array_get_size(v_buckets_4980_);
    v___x_4983_ = lean_nat_dec_lt(v___x_4981_, v___x_4982_);
    if v___x_4983_ == 0 {
        crate::leanh::lean_dec(v_l_4979_);
        crate::leanh::lean_dec(v_inst_4977_);
        crate::leanh::lean_dec_ref(v_inst_4975_);
        crate::leanh::lean_dec_ref(v_inst_4974_);
        return v_m_4978_;
    } else {
        let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v_inst_4977_,
            v_inst_4974_,
            v_inst_4975_,
            v_m_4978_,
            v_l_4979_,
        );
        return v___x_4984_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(
    mut v_inst_4985_: *mut crate::leanh::LeanObject,
    mut v_inst_4986_: *mut crate::leanh::LeanObject,
    mut v_inst_4987_: *mut crate::leanh::LeanObject,
    mut v_m_4988_: *mut crate::leanh::LeanObject,
    mut v_l_4989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: u8 = 0;
    v_buckets_4990_ = crate::leanh::lean_ctor_get(v_m_4988_, 1);
    v___x_4991_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4992_ = lean_array_get_size(v_buckets_4990_);
    v___x_4993_ = lean_nat_dec_lt(v___x_4991_, v___x_4992_);
    if v___x_4993_ == 0 {
        crate::leanh::lean_dec(v_l_4989_);
        crate::leanh::lean_dec(v_inst_4987_);
        crate::leanh::lean_dec_ref(v_inst_4986_);
        crate::leanh::lean_dec_ref(v_inst_4985_);
        return v_m_4988_;
    } else {
        let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v_inst_4987_,
            v_inst_4985_,
            v_inst_4986_,
            v_m_4988_,
            v_l_4989_,
        );
        return v___x_4994_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(
    mut v_00_u03b1_4995_: *mut crate::leanh::LeanObject,
    mut v_inst_4996_: *mut crate::leanh::LeanObject,
    mut v_inst_4997_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4998_: *mut crate::leanh::LeanObject,
    mut v_inst_4999_: *mut crate::leanh::LeanObject,
    mut v_m_5000_: *mut crate::leanh::LeanObject,
    mut v_l_5001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: u8 = 0;
    v_buckets_5002_ = crate::leanh::lean_ctor_get(v_m_5000_, 1);
    v___x_5003_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5004_ = lean_array_get_size(v_buckets_5002_);
    v___x_5005_ = lean_nat_dec_lt(v___x_5003_, v___x_5004_);
    if v___x_5005_ == 0 {
        crate::leanh::lean_dec(v_l_5001_);
        crate::leanh::lean_dec(v_inst_4999_);
        crate::leanh::lean_dec_ref(v_inst_4997_);
        crate::leanh::lean_dec_ref(v_inst_4996_);
        return v_m_5000_;
    } else {
        let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v_inst_4999_,
            v_inst_4996_,
            v_inst_4997_,
            v_m_5000_,
            v_l_5001_,
        );
        return v___x_5006_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_unitOfArray___redArg(
    mut v_inst_5011_: *mut crate::leanh::LeanObject,
    mut v_inst_5012_: *mut crate::leanh::LeanObject,
    mut v_l_5013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: u8 = 0;
    v___x_5014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5015_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5015_ == 0 {
        crate::leanh::lean_dec_ref(v_l_5013_);
        crate::leanh::lean_dec_ref(v_inst_5012_);
        crate::leanh::lean_dec_ref(v_inst_5011_);
        return v___x_5014_;
    } else {
        let mut v___f_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5016_ = l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1;
        v___x_5017_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_5016_,
            v_inst_5011_,
            v_inst_5012_,
            v___x_5014_,
            v_l_5013_,
        );
        return v___x_5017_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_unitOfArray(
    mut v_00_u03b1_5018_: *mut crate::leanh::LeanObject,
    mut v_inst_5019_: *mut crate::leanh::LeanObject,
    mut v_inst_5020_: *mut crate::leanh::LeanObject,
    mut v_l_5021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: u8 = 0;
    v___x_5022_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5023_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5023_ == 0 {
        crate::leanh::lean_dec_ref(v_l_5021_);
        crate::leanh::lean_dec_ref(v_inst_5020_);
        crate::leanh::lean_dec_ref(v_inst_5019_);
        return v___x_5022_;
    } else {
        let mut v___f_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5024_ = l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1;
        v___x_5025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_5024_,
            v_inst_5019_,
            v_inst_5020_,
            v___x_5022_,
            v_l_5021_,
        );
        return v___x_5025_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_numBuckets___redArg(
    mut v_m_5026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5027_ = crate::leanh::lean_ctor_get(v_m_5026_, 1);
    v___x_5028_ = lean_array_get_size(v_buckets_5027_);
    return v___x_5028_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(
    mut v_m_5029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5030_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_5029_);
    crate::leanh::lean_dec_ref(v_m_5029_);
    return v_res_5030_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_numBuckets(
    mut v_00_u03b1_5031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5032_: *mut crate::leanh::LeanObject,
    mut v_m_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5034_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_5033_);
    return v___x_5034_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_numBuckets___boxed(
    mut v_00_u03b1_5035_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5036_: *mut crate::leanh::LeanObject,
    mut v_m_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5038_ =
        l_Std_DHashMap_Raw_Internal_numBuckets(v_00_u03b1_5035_, v_00_u03b2_5036_, v_m_5037_);
    crate::leanh::lean_dec_ref(v_m_5037_);
    return v_res_5038_;
}
pub unsafe fn l_Std_DHashMap_Raw_toList___redArg___lam__0(
    mut v_a_5039_: *mut crate::leanh::LeanObject,
    mut v_b_5040_: *mut crate::leanh::LeanObject,
    mut v_d_5041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5042_, 0, v_a_5039_);
    crate::leanh::lean_ctor_set(v___x_5042_, 1, v_b_5040_);
    v___x_5043_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5043_, 0, v___x_5042_);
    crate::leanh::lean_ctor_set(v___x_5043_, 1, v_d_5041_);
    return v___x_5043_;
}
pub unsafe fn l_Std_DHashMap_Raw_toList___redArg___lam__1(
    mut v___x_5044_: *mut crate::leanh::LeanObject,
    mut v___f_5045_: *mut crate::leanh::LeanObject,
    mut v_l_5046_: *mut crate::leanh::LeanObject,
    mut v_acc_5047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5048_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_5044_,
        v___f_5045_,
        v_acc_5047_,
        v_l_5046_,
    );
    return v___x_5048_;
}
pub unsafe fn l_Std_DHashMap_Raw_toList___redArg(
    mut v_m_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: u8 = 0;
    v___x_5054_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5055_ = crate::leanh::lean_ctor_get(v_m_5053_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5055_);
    crate::leanh::lean_dec_ref(v_m_5053_);
    v___x_5056_ = crate::leanh::lean_box(0);
    v___x_5057_ = lean_array_get_size(v_buckets_5055_);
    v___x_5058_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5059_ = lean_nat_dec_lt(v___x_5058_, v___x_5057_);
    if v___x_5059_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5055_);
        return v___x_5056_;
    } else {
        let mut v___f_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5061_: usize = 0;
        let mut v___x_5062_: usize = 0;
        let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5060_ = l_Std_DHashMap_Raw_toList___redArg___closed__1;
        v___x_5061_ = lean_usize_of_nat(v___x_5057_);
        v___x_5062_ = 0usize;
        v___x_5063_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5054_,
            v___f_5060_,
            v_buckets_5055_,
            v___x_5061_,
            v___x_5062_,
            v___x_5056_,
        );
        return v___x_5063_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_toList(
    mut v_00_u03b1_5064_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5065_: *mut crate::leanh::LeanObject,
    mut v_m_5066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: u8 = 0;
    v___x_5067_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5068_ = crate::leanh::lean_ctor_get(v_m_5066_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5068_);
    crate::leanh::lean_dec_ref(v_m_5066_);
    v___x_5069_ = crate::leanh::lean_box(0);
    v___x_5070_ = lean_array_get_size(v_buckets_5068_);
    v___x_5071_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5072_ = lean_nat_dec_lt(v___x_5071_, v___x_5070_);
    if v___x_5072_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5068_);
        return v___x_5069_;
    } else {
        let mut v___f_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5074_: usize = 0;
        let mut v___x_5075_: usize = 0;
        let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5073_ = l_Std_DHashMap_Raw_toList___redArg___closed__1;
        v___x_5074_ = lean_usize_of_nat(v___x_5070_);
        v___x_5075_ = 0usize;
        v___x_5076_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5067_,
            v___f_5073_,
            v_buckets_5068_,
            v___x_5074_,
            v___x_5075_,
            v___x_5069_,
        );
        return v___x_5076_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(
    mut v_a_5077_: *mut crate::leanh::LeanObject,
    mut v_b_5078_: *mut crate::leanh::LeanObject,
    mut v_d_5079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5080_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5080_, 0, v_a_5077_);
    crate::leanh::lean_ctor_set(v___x_5080_, 1, v_b_5078_);
    v___x_5081_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5081_, 0, v___x_5080_);
    crate::leanh::lean_ctor_set(v___x_5081_, 1, v_d_5079_);
    return v___x_5081_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toList___redArg___lam__1(
    mut v___x_5082_: *mut crate::leanh::LeanObject,
    mut v___f_5083_: *mut crate::leanh::LeanObject,
    mut v_l_5084_: *mut crate::leanh::LeanObject,
    mut v_acc_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_5082_,
        v___f_5083_,
        v_acc_5085_,
        v_l_5084_,
    );
    return v___x_5086_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toList___redArg(
    mut v_m_5091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: u8 = 0;
    v___x_5092_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5093_ = crate::leanh::lean_ctor_get(v_m_5091_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5093_);
    crate::leanh::lean_dec_ref(v_m_5091_);
    v___x_5094_ = crate::leanh::lean_box(0);
    v___x_5095_ = lean_array_get_size(v_buckets_5093_);
    v___x_5096_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5097_ = lean_nat_dec_lt(v___x_5096_, v___x_5095_);
    if v___x_5097_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5093_);
        return v___x_5094_;
    } else {
        let mut v___f_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5099_: usize = 0;
        let mut v___x_5100_: usize = 0;
        let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5098_ = l_Std_DHashMap_Raw_Const_toList___redArg___closed__1;
        v___x_5099_ = lean_usize_of_nat(v___x_5095_);
        v___x_5100_ = 0usize;
        v___x_5101_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5092_,
            v___f_5098_,
            v_buckets_5093_,
            v___x_5099_,
            v___x_5100_,
            v___x_5094_,
        );
        return v___x_5101_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toList(
    mut v_00_u03b1_5102_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5103_: *mut crate::leanh::LeanObject,
    mut v_m_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    v___x_5105_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5106_ = crate::leanh::lean_ctor_get(v_m_5104_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5106_);
    crate::leanh::lean_dec_ref(v_m_5104_);
    v___x_5107_ = crate::leanh::lean_box(0);
    v___x_5108_ = lean_array_get_size(v_buckets_5106_);
    v___x_5109_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5110_ = lean_nat_dec_lt(v___x_5109_, v___x_5108_);
    if v___x_5110_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5106_);
        return v___x_5107_;
    } else {
        let mut v___f_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5112_: usize = 0;
        let mut v___x_5113_: usize = 0;
        let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5111_ = l_Std_DHashMap_Raw_Const_toList___redArg___closed__1;
        v___x_5112_ = lean_usize_of_nat(v___x_5108_);
        v___x_5113_ = 0usize;
        v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5105_,
            v___f_5111_,
            v_buckets_5106_,
            v___x_5112_,
            v___x_5113_,
            v___x_5107_,
        );
        return v___x_5114_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instRepr___redArg___lam__2(
    mut v___x_5118_: *mut crate::leanh::LeanObject,
    mut v___f_5119_: *mut crate::leanh::LeanObject,
    mut v_m_5120_: *mut crate::leanh::LeanObject,
    mut v_prec_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: u8 = 0;
    let mut v___f_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: usize = 0;
    let mut v___x_5141_: usize = 0;
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5143_: u8 = 0;
    let mut v_unused_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5122_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
                v_buckets_5123_ = crate::leanh::lean_ctor_get(v_m_5120_, 1);
                v_isSharedCheck_5143_ = (!crate::leanh::lean_is_exclusive(v_m_5120_)) as u8;
                if v_isSharedCheck_5143_ == 0 {
                    v_unused_5144_ = crate::leanh::lean_ctor_get(v_m_5120_, 0);
                    crate::leanh::lean_dec(v_unused_5144_);
                    v___x_5125_ = v_m_5120_;
                    v_isShared_5126_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5123_);
                    crate::leanh::lean_dec(v_m_5120_);
                    v___x_5125_ = crate::leanh::lean_box(0);
                    v_isShared_5126_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5127_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1;
                v___x_5135_ = crate::leanh::lean_box(0);
                v___x_5136_ = lean_array_get_size(v_buckets_5123_);
                v___x_5137_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5138_ = lean_nat_dec_lt(v___x_5137_, v___x_5136_);
                if v___x_5138_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_5123_);
                    crate::leanh::lean_dec_ref(v___f_5119_);
                    v___y_5129_ = v___x_5135_;
                    state = 2;
                    continue;
                } else {
                    v___f_5139_ = crate::leanh::lean_alloc_closure(
                        l_Std_DHashMap_Raw_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_5139_, 0, v___x_5122_);
                    crate::leanh::lean_closure_set(v___f_5139_, 1, v___f_5119_);
                    v___x_5140_ = lean_usize_of_nat(v___x_5136_);
                    v___x_5141_ = 0usize;
                    v___x_5142_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5122_,
                        v___f_5139_,
                        v_buckets_5123_,
                        v___x_5140_,
                        v___x_5141_,
                        v___x_5135_,
                    );
                    v___y_5129_ = v___x_5142_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5130_ = l_List_repr___redArg(v___x_5118_, v___y_5129_);
                if v_isShared_5126_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5125_, 5);
                    crate::leanh::lean_ctor_set(v___x_5125_, 1, v___x_5130_);
                    crate::leanh::lean_ctor_set(v___x_5125_, 0, v___x_5127_);
                    v___x_5132_ = v___x_5125_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5134_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 0, v___x_5127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 1, v___x_5130_);
                    v___x_5132_ = v_reuseFailAlloc_5134_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5133_ = l_Repr_addAppParen(v___x_5132_, v_prec_5121_);
                return v___x_5133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed(
    mut v___x_5145_: *mut crate::leanh::LeanObject,
    mut v___f_5146_: *mut crate::leanh::LeanObject,
    mut v_m_5147_: *mut crate::leanh::LeanObject,
    mut v_prec_5148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5149_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2(
        v___x_5145_,
        v___f_5146_,
        v_m_5147_,
        v_prec_5148_,
    );
    crate::leanh::lean_dec(v_prec_5148_);
    return v_res_5149_;
}
pub unsafe fn l_Std_DHashMap_Raw_instRepr___redArg(
    mut v_inst_5150_: *mut crate::leanh::LeanObject,
    mut v_inst_5151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5152_ = l_Std_DHashMap_Raw_toList___redArg___closed__0;
    v___x_5153_ =
        crate::leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5153_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5153_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5153_, 2, v_inst_5150_);
    crate::leanh::lean_closure_set(v___x_5153_, 3, v_inst_5151_);
    v___f_5154_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5154_, 0, v___x_5153_);
    crate::leanh::lean_closure_set(v___f_5154_, 1, v___f_5152_);
    return v___f_5154_;
}
pub unsafe fn l_Std_DHashMap_Raw_instRepr(
    mut v_00_u03b1_5155_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5156_: *mut crate::leanh::LeanObject,
    mut v_inst_5157_: *mut crate::leanh::LeanObject,
    mut v_inst_5158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5159_ = l_Std_DHashMap_Raw_instRepr___redArg(v_inst_5157_, v_inst_5158_);
    return v___x_5159_;
}
pub unsafe fn l_Std_DHashMap_Raw_keys___redArg___lam__0(
    mut v_a_5160_: *mut crate::leanh::LeanObject,
    mut v_b_5161_: *mut crate::leanh::LeanObject,
    mut v_d_5162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5163_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5163_, 0, v_a_5160_);
    crate::leanh::lean_ctor_set(v___x_5163_, 1, v_d_5162_);
    return v___x_5163_;
}
pub unsafe fn l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(
    mut v_a_5164_: *mut crate::leanh::LeanObject,
    mut v_b_5165_: *mut crate::leanh::LeanObject,
    mut v_d_5166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5167_ = l_Std_DHashMap_Raw_keys___redArg___lam__0(v_a_5164_, v_b_5165_, v_d_5166_);
    crate::leanh::lean_dec(v_b_5165_);
    return v_res_5167_;
}
pub unsafe fn l_Std_DHashMap_Raw_keys___redArg(
    mut v_m_5172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: u8 = 0;
    v___x_5173_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5174_ = crate::leanh::lean_ctor_get(v_m_5172_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5174_);
    crate::leanh::lean_dec_ref(v_m_5172_);
    v___x_5175_ = crate::leanh::lean_box(0);
    v___x_5176_ = lean_array_get_size(v_buckets_5174_);
    v___x_5177_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5178_ = lean_nat_dec_lt(v___x_5177_, v___x_5176_);
    if v___x_5178_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5174_);
        return v___x_5175_;
    } else {
        let mut v___f_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5180_: usize = 0;
        let mut v___x_5181_: usize = 0;
        let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5179_ = l_Std_DHashMap_Raw_keys___redArg___closed__1;
        v___x_5180_ = lean_usize_of_nat(v___x_5176_);
        v___x_5181_ = 0usize;
        v___x_5182_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5173_,
            v___f_5179_,
            v_buckets_5174_,
            v___x_5180_,
            v___x_5181_,
            v___x_5175_,
        );
        return v___x_5182_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_keys(
    mut v_00_u03b1_5183_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5184_: *mut crate::leanh::LeanObject,
    mut v_m_5185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: u8 = 0;
    v___x_5186_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5187_ = crate::leanh::lean_ctor_get(v_m_5185_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5187_);
    crate::leanh::lean_dec_ref(v_m_5185_);
    v___x_5188_ = crate::leanh::lean_box(0);
    v___x_5189_ = lean_array_get_size(v_buckets_5187_);
    v___x_5190_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5191_ = lean_nat_dec_lt(v___x_5190_, v___x_5189_);
    if v___x_5191_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5187_);
        return v___x_5188_;
    } else {
        let mut v___f_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5193_: usize = 0;
        let mut v___x_5194_: usize = 0;
        let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5192_ = l_Std_DHashMap_Raw_keys___redArg___closed__1;
        v___x_5193_ = lean_usize_of_nat(v___x_5189_);
        v___x_5194_ = 0usize;
        v___x_5195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5186_,
            v___f_5192_,
            v_buckets_5187_,
            v___x_5193_,
            v___x_5194_,
            v___x_5188_,
        );
        return v___x_5195_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_ofList___redArg(
    mut v_inst_5200_: *mut crate::leanh::LeanObject,
    mut v_inst_5201_: *mut crate::leanh::LeanObject,
    mut v_l_5202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: u8 = 0;
    v___x_5203_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5204_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5204_ == 0 {
        crate::leanh::lean_dec(v_l_5202_);
        crate::leanh::lean_dec_ref(v_inst_5201_);
        crate::leanh::lean_dec_ref(v_inst_5200_);
        return v___x_5203_;
    } else {
        let mut v___f_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5205_ = l_Std_DHashMap_Raw_ofList___redArg___closed__1;
        v___x_5206_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_5205_,
            v_inst_5200_,
            v_inst_5201_,
            v___x_5203_,
            v_l_5202_,
        );
        return v___x_5206_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_ofList(
    mut v_00_u03b1_5207_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5208_: *mut crate::leanh::LeanObject,
    mut v_inst_5209_: *mut crate::leanh::LeanObject,
    mut v_inst_5210_: *mut crate::leanh::LeanObject,
    mut v_l_5211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    v___x_5212_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5213_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5213_ == 0 {
        crate::leanh::lean_dec(v_l_5211_);
        crate::leanh::lean_dec_ref(v_inst_5210_);
        crate::leanh::lean_dec_ref(v_inst_5209_);
        return v___x_5212_;
    } else {
        let mut v___f_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5214_ = l_Std_DHashMap_Raw_ofList___redArg___closed__1;
        v___x_5215_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_5214_,
            v_inst_5209_,
            v_inst_5210_,
            v___x_5212_,
            v_l_5211_,
        );
        return v___x_5215_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_ofArray___redArg(
    mut v_inst_5216_: *mut crate::leanh::LeanObject,
    mut v_inst_5217_: *mut crate::leanh::LeanObject,
    mut v_l_5218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: u8 = 0;
    v___x_5219_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5220_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5220_ == 0 {
        crate::leanh::lean_dec_ref(v_l_5218_);
        crate::leanh::lean_dec_ref(v_inst_5217_);
        crate::leanh::lean_dec_ref(v_inst_5216_);
        return v___x_5219_;
    } else {
        let mut v___f_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5221_ = l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1;
        v___x_5222_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_5221_,
            v_inst_5216_,
            v_inst_5217_,
            v___x_5219_,
            v_l_5218_,
        );
        return v___x_5222_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_ofArray(
    mut v_00_u03b1_5223_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5224_: *mut crate::leanh::LeanObject,
    mut v_inst_5225_: *mut crate::leanh::LeanObject,
    mut v_inst_5226_: *mut crate::leanh::LeanObject,
    mut v_l_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: u8 = 0;
    v___x_5228_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5229_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5229_ == 0 {
        crate::leanh::lean_dec_ref(v_l_5227_);
        crate::leanh::lean_dec_ref(v_inst_5226_);
        crate::leanh::lean_dec_ref(v_inst_5225_);
        return v___x_5228_;
    } else {
        let mut v___f_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5230_ = l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1;
        v___x_5231_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_5230_,
            v_inst_5225_,
            v_inst_5226_,
            v___x_5228_,
            v_l_5227_,
        );
        return v___x_5231_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_ofList___redArg(
    mut v_inst_5232_: *mut crate::leanh::LeanObject,
    mut v_inst_5233_: *mut crate::leanh::LeanObject,
    mut v_l_5234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    v___x_5235_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5236_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5236_ == 0 {
        crate::leanh::lean_dec(v_l_5234_);
        crate::leanh::lean_dec_ref(v_inst_5233_);
        crate::leanh::lean_dec_ref(v_inst_5232_);
        return v___x_5235_;
    } else {
        let mut v___f_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5237_ = l_Std_DHashMap_Raw_ofList___redArg___closed__1;
        v___x_5238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_5237_,
            v_inst_5232_,
            v_inst_5233_,
            v___x_5235_,
            v_l_5234_,
        );
        return v___x_5238_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_ofList(
    mut v_00_u03b1_5239_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5240_: *mut crate::leanh::LeanObject,
    mut v_inst_5241_: *mut crate::leanh::LeanObject,
    mut v_inst_5242_: *mut crate::leanh::LeanObject,
    mut v_l_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    v___x_5244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5245_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5245_ == 0 {
        crate::leanh::lean_dec(v_l_5243_);
        crate::leanh::lean_dec_ref(v_inst_5242_);
        crate::leanh::lean_dec_ref(v_inst_5241_);
        return v___x_5244_;
    } else {
        let mut v___f_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5246_ = l_Std_DHashMap_Raw_ofList___redArg___closed__1;
        v___x_5247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_5246_,
            v_inst_5241_,
            v_inst_5242_,
            v___x_5244_,
            v_l_5243_,
        );
        return v___x_5247_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_ofArray___redArg(
    mut v_inst_5248_: *mut crate::leanh::LeanObject,
    mut v_inst_5249_: *mut crate::leanh::LeanObject,
    mut v_l_5250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    v___x_5251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5252_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5252_ == 0 {
        crate::leanh::lean_dec_ref(v_l_5250_);
        crate::leanh::lean_dec_ref(v_inst_5249_);
        crate::leanh::lean_dec_ref(v_inst_5248_);
        return v___x_5251_;
    } else {
        let mut v___f_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5253_ = l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1;
        v___x_5254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_5253_,
            v_inst_5248_,
            v_inst_5249_,
            v___x_5251_,
            v_l_5250_,
        );
        return v___x_5254_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_ofArray(
    mut v_00_u03b1_5255_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5256_: *mut crate::leanh::LeanObject,
    mut v_inst_5257_: *mut crate::leanh::LeanObject,
    mut v_inst_5258_: *mut crate::leanh::LeanObject,
    mut v_l_5259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    v___x_5260_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5261_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5261_ == 0 {
        crate::leanh::lean_dec_ref(v_l_5259_);
        crate::leanh::lean_dec_ref(v_inst_5258_);
        crate::leanh::lean_dec_ref(v_inst_5257_);
        return v___x_5260_;
    } else {
        let mut v___f_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5262_ = l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1;
        v___x_5263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_5262_,
            v_inst_5257_,
            v_inst_5258_,
            v___x_5260_,
            v_l_5259_,
        );
        return v___x_5263_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_unitOfList___redArg(
    mut v_inst_5264_: *mut crate::leanh::LeanObject,
    mut v_inst_5265_: *mut crate::leanh::LeanObject,
    mut v_l_5266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: u8 = 0;
    v___x_5267_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5268_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5268_ == 0 {
        crate::leanh::lean_dec(v_l_5266_);
        crate::leanh::lean_dec_ref(v_inst_5265_);
        crate::leanh::lean_dec_ref(v_inst_5264_);
        return v___x_5267_;
    } else {
        let mut v___f_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5269_ = l_Std_DHashMap_Raw_ofList___redArg___closed__1;
        v___x_5270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_5269_,
            v_inst_5264_,
            v_inst_5265_,
            v___x_5267_,
            v_l_5266_,
        );
        return v___x_5270_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_unitOfList(
    mut v_00_u03b1_5271_: *mut crate::leanh::LeanObject,
    mut v_inst_5272_: *mut crate::leanh::LeanObject,
    mut v_inst_5273_: *mut crate::leanh::LeanObject,
    mut v_l_5274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    v___x_5275_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5276_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5276_ == 0 {
        crate::leanh::lean_dec(v_l_5274_);
        crate::leanh::lean_dec_ref(v_inst_5273_);
        crate::leanh::lean_dec_ref(v_inst_5272_);
        return v___x_5275_;
    } else {
        let mut v___f_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5277_ = l_Std_DHashMap_Raw_ofList___redArg___closed__1;
        v___x_5278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_5277_,
            v_inst_5272_,
            v_inst_5273_,
            v___x_5275_,
            v_l_5274_,
        );
        return v___x_5278_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Raw(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_LawfulHashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Raw(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_Raw(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_LawfulHashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Raw(builtin);
}
