// Lean compiler output
// Module: Std.Data.DHashMap.Basic
// Imports: Std.Data.DHashMap.Raw Std.Data.DHashMap.Raw
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
    l_Std_DHashMap_Internal_Raw_u2080_modify___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Raw::{
    initialize_Std_Data_DHashMap_Raw, l_Std_DHashMap_Raw_Internal_numBuckets___redArg,
    runtime_initialize_Std_Data_DHashMap_Raw,
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
static mut l_Std_DHashMap_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_instEmptyCollection___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_instEmptyCollection___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DHashMap_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_DHashMap_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_DHashMap_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_DHashMap_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DHashMap_term___x7em___00__closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_DHashMap_term___x7em___00__closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            18035583711357664763 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_DHashMap_term___x7em___00__closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            7703847134268921897 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__4_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_DHashMap_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__6_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_DHashMap_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_DHashMap_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DHashMap_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,18035583711357664763 as *mut crate::leanh::LeanObject] };
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,2784610703921446720 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_keys___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_keys___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_keys___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_keys___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_keys___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_keys___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_DHashMap_keys___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_keys___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_keys___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_keys___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__10_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_DHashMap_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DHashMap_keys___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keys___redArg___closed__11_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_DHashMap_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_keys___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_DHashMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DHashMap_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_toList___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_DHashMap_toList___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_toList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_toList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_toList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Const_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Const_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Const_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Const_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Const_toList___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Const_toList___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Const_toList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Const_toList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Const_toList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_DHashMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DHashMap_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_toArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_DHashMap_toArray___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_toArray___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Const_toArray___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Const_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Const_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Const_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Const_toArray___redArg___closed__1_value:
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
    m_fun: l_Std_DHashMap_Const_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Const_toArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Const_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Const_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keysArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_DHashMap_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DHashMap_keysArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keysArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_keysArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_DHashMap_keysArray___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_keysArray___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_keysArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_keysArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_all___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_DHashMap_all___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_all___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_union___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_union___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_union___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_partition___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_partition___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DHashMap_values___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_DHashMap_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DHashMap_values___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_values___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_values___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_DHashMap_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_values___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_values___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_values___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_valuesArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_valuesArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_valuesArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_valuesArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_valuesArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_valuesArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_valuesArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Const_unitOfArray___redArg___closed__0_value:
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
        core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Const_unitOfArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Const_unitOfArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Const_unitOfArray___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Std_DHashMap_Const_unitOfArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Const_unitOfArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Const_unitOfArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_instRepr___redArg___lam__2___closed__0_value:
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
        83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Std_DHashMap_instRepr___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_instRepr___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_DHashMap_instRepr___redArg___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_instRepr___redArg___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_instRepr___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_ofList___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_ofList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_ofList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_ofList___redArg___closed__1_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_ofList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_ofList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_ofList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_emptyWithCapacity___redArg(
    mut v_capacity_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2765_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2766_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2767_ = lean_nat_mul(v_capacity_2764_, v___x_2766_);
    v___x_2768_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2769_ = lean_nat_div(v___x_2767_, v___x_2768_);
    crate::leanh::lean_dec(v___x_2767_);
    v___x_2770_ = l_Nat_nextPowerOfTwo(v___x_2769_);
    crate::leanh::lean_dec(v___x_2769_);
    v___x_2771_ = crate::leanh::lean_box(0);
    v___x_2772_ = lean_mk_array(v___x_2770_, v___x_2771_);
    v___x_2773_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2773_, 0, v___x_2765_);
    crate::leanh::lean_ctor_set(v___x_2773_, 1, v___x_2772_);
    return v___x_2773_;
}
pub unsafe fn l_Std_DHashMap_emptyWithCapacity___redArg___boxed(
    mut v_capacity_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_Std_DHashMap_emptyWithCapacity___redArg(v_capacity_2774_);
    crate::leanh::lean_dec(v_capacity_2774_);
    return v_res_2775_;
}
pub unsafe fn l_Std_DHashMap_emptyWithCapacity(
    mut v_00_u03b1_2776_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2777_: *mut crate::leanh::LeanObject,
    mut v_inst_2778_: *mut crate::leanh::LeanObject,
    mut v_inst_2779_: *mut crate::leanh::LeanObject,
    mut v_capacity_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2781_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2782_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2783_ = lean_nat_mul(v_capacity_2780_, v___x_2782_);
    v___x_2784_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2785_ = lean_nat_div(v___x_2783_, v___x_2784_);
    crate::leanh::lean_dec(v___x_2783_);
    v___x_2786_ = l_Nat_nextPowerOfTwo(v___x_2785_);
    crate::leanh::lean_dec(v___x_2785_);
    v___x_2787_ = crate::leanh::lean_box(0);
    v___x_2788_ = lean_mk_array(v___x_2786_, v___x_2787_);
    v___x_2789_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2789_, 0, v___x_2781_);
    crate::leanh::lean_ctor_set(v___x_2789_, 1, v___x_2788_);
    return v___x_2789_;
}
pub unsafe fn l_Std_DHashMap_emptyWithCapacity___boxed(
    mut v_00_u03b1_2790_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2791_: *mut crate::leanh::LeanObject,
    mut v_inst_2792_: *mut crate::leanh::LeanObject,
    mut v_inst_2793_: *mut crate::leanh::LeanObject,
    mut v_capacity_2794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2795_ = l_Std_DHashMap_emptyWithCapacity(
        v_00_u03b1_2790_,
        v_00_u03b2_2791_,
        v_inst_2792_,
        v_inst_2793_,
        v_capacity_2794_,
    );
    crate::leanh::lean_dec(v_capacity_2794_);
    crate::leanh::lean_dec_ref(v_inst_2793_);
    crate::leanh::lean_dec_ref(v_inst_2792_);
    return v_res_2795_;
}
pub unsafe fn _init_l_Std_DHashMap_instEmptyCollection___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2796_ = crate::leanh::lean_box(0);
    v___x_2797_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2798_ = lean_mk_array(v___x_2797_, v___x_2796_);
    return v___x_2798_;
}
pub unsafe fn _init_l_Std_DHashMap_instEmptyCollection___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2799_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__0_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__0,
    );
    v___x_2800_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2801_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2801_, 0, v___x_2800_);
    crate::leanh::lean_ctor_set(v___x_2801_, 1, v___x_2799_);
    return v___x_2801_;
}
pub unsafe fn l_Std_DHashMap_instEmptyCollection(
    mut v_00_u03b1_2802_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2803_: *mut crate::leanh::LeanObject,
    mut v_inst_2804_: *mut crate::leanh::LeanObject,
    mut v_inst_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    return v___x_2806_;
}
pub unsafe fn l_Std_DHashMap_instEmptyCollection___boxed(
    mut v_00_u03b1_2807_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2808_: *mut crate::leanh::LeanObject,
    mut v_inst_2809_: *mut crate::leanh::LeanObject,
    mut v_inst_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2811_ = l_Std_DHashMap_instEmptyCollection(
        v_00_u03b1_2807_,
        v_00_u03b2_2808_,
        v_inst_2809_,
        v_inst_2810_,
    );
    crate::leanh::lean_dec_ref(v_inst_2810_);
    crate::leanh::lean_dec_ref(v_inst_2809_);
    return v_res_2811_;
}
pub unsafe fn l_Std_DHashMap_instInhabited(
    mut v_00_u03b1_2812_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2813_: *mut crate::leanh::LeanObject,
    mut v_inst_2814_: *mut crate::leanh::LeanObject,
    mut v_inst_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    return v___x_2816_;
}
pub unsafe fn l_Std_DHashMap_instInhabited___boxed(
    mut v_00_u03b1_2817_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2818_: *mut crate::leanh::LeanObject,
    mut v_inst_2819_: *mut crate::leanh::LeanObject,
    mut v_inst_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2821_ = l_Std_DHashMap_instInhabited(
        v_00_u03b1_2817_,
        v_00_u03b2_2818_,
        v_inst_2819_,
        v_inst_2820_,
    );
    crate::leanh::lean_dec_ref(v_inst_2820_);
    crate::leanh::lean_dec_ref(v_inst_2819_);
    return v_res_2821_;
}
pub unsafe fn _init_l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__5;
    v___x_2861_ = l_String_toRawSubstring_x27(v___x_2860_);
    return v___x_2861_;
}
pub unsafe fn l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1(
    mut v_x_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
    mut v_a_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    v___x_2885_ = l_Std_DHashMap_term___x7em___00__closed__3;
    crate::leanh::lean_inc(v_x_2882_);
    v___x_2886_ = l_Lean_Syntax_isOfKind(v_x_2882_, v___x_2885_);
    if v___x_2886_ == 0 {
        let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2882_);
        v___x_2887_ = crate::leanh::lean_box(1);
        v___x_2888_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2887_);
        crate::leanh::lean_ctor_set(v___x_2888_, 1, v_a_2884_);
        return v___x_2888_;
    } else {
        let mut v_quotContext_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: u8 = 0;
        let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2889_ = crate::leanh::lean_ctor_get(v_a_2883_, 1);
        v_currMacroScope_2890_ = crate::leanh::lean_ctor_get(v_a_2883_, 2);
        v_ref_2891_ = crate::leanh::lean_ctor_get(v_a_2883_, 5);
        v___x_2892_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2893_ = l_Lean_Syntax_getArg(v_x_2882_, v___x_2892_);
        v___x_2894_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2895_ = l_Lean_Syntax_getArg(v_x_2882_, v___x_2894_);
        crate::leanh::lean_dec(v_x_2882_);
        v___x_2896_ = 0;
        v___x_2897_ = l_Lean_SourceInfo_fromRef(v_ref_2891_, v___x_2896_);
        v___x_2898_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4;
        v___x_2899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__6_once), _init_l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__6);
        v___x_2900_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_2890_);
        crate::leanh::lean_inc(v_quotContext_2889_);
        v___x_2901_ =
            l_Lean_addMacroScope(v_quotContext_2889_, v___x_2900_, v_currMacroScope_2890_);
        v___x_2902_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__12;
        crate::leanh::lean_inc_n(v___x_2897_, 2);
        v___x_2903_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2897_);
        crate::leanh::lean_ctor_set(v___x_2903_, 1, v___x_2899_);
        crate::leanh::lean_ctor_set(v___x_2903_, 2, v___x_2901_);
        crate::leanh::lean_ctor_set(v___x_2903_, 3, v___x_2902_);
        v___x_2904_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__14;
        v___x_2905_ = l_Lean_Syntax_node2(v___x_2897_, v___x_2904_, v___x_2893_, v___x_2895_);
        v___x_2906_ = l_Lean_Syntax_node2(v___x_2897_, v___x_2898_, v___x_2903_, v___x_2905_);
        v___x_2907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2907_, 0, v___x_2906_);
        crate::leanh::lean_ctor_set(v___x_2907_, 1, v_a_2884_);
        return v___x_2907_;
    }
}
pub unsafe fn l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___boxed(
    mut v_x_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2911_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1(v_x_2908_, v_a_2909_, v_a_2910_);
    crate::leanh::lean_dec_ref(v_a_2909_);
    return v_res_2911_;
}
pub unsafe fn l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1(
    mut v_x_2915_: *mut crate::leanh::LeanObject,
    mut v_a_2916_: *mut crate::leanh::LeanObject,
    mut v_a_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: u8 = 0;
    v___x_2918_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______macroRules__Std__DHashMap__term___x7em____1___closed__4;
    crate::leanh::lean_inc(v_x_2915_);
    v___x_2919_ = l_Lean_Syntax_isOfKind(v_x_2915_, v___x_2918_);
    if v___x_2919_ == 0 {
        let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2915_);
        v___x_2920_ = crate::leanh::lean_box(0);
        v___x_2921_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2921_, 0, v___x_2920_);
        crate::leanh::lean_ctor_set(v___x_2921_, 1, v_a_2917_);
        return v___x_2921_;
    } else {
        let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2925_: u8 = 0;
        v___x_2922_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2923_ = l_Lean_Syntax_getArg(v_x_2915_, v___x_2922_);
        v___x_2924_ = l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_2923_);
        v___x_2925_ = l_Lean_Syntax_isOfKind(v___x_2923_, v___x_2924_);
        if v___x_2925_ == 0 {
            let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2923_);
            crate::leanh::lean_dec(v_x_2915_);
            v___x_2926_ = crate::leanh::lean_box(0);
            v___x_2927_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2927_, 0, v___x_2926_);
            crate::leanh::lean_ctor_set(v___x_2927_, 1, v_a_2917_);
            return v___x_2927_;
        } else {
            let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2931_: u8 = 0;
            v___x_2928_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2929_ = l_Lean_Syntax_getArg(v_x_2915_, v___x_2928_);
            crate::leanh::lean_dec(v_x_2915_);
            v___x_2930_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_2929_);
            v___x_2931_ = l_Lean_Syntax_matchesNull(v___x_2929_, v___x_2930_);
            if v___x_2931_ == 0 {
                let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2929_);
                crate::leanh::lean_dec(v___x_2923_);
                v___x_2932_ = crate::leanh::lean_box(0);
                v___x_2933_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2932_);
                crate::leanh::lean_ctor_set(v___x_2933_, 1, v_a_2917_);
                return v___x_2933_;
            } else {
                let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2937_: u8 = 0;
                let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2934_ = l_Lean_Syntax_getArg(v___x_2929_, v___x_2922_);
                v___x_2935_ = l_Lean_Syntax_getArg(v___x_2929_, v___x_2928_);
                crate::leanh::lean_dec(v___x_2929_);
                v_ref_2936_ = l_Lean_replaceRef(v___x_2923_, v_a_2916_);
                crate::leanh::lean_dec(v___x_2923_);
                v___x_2937_ = 0;
                v___x_2938_ = l_Lean_SourceInfo_fromRef(v_ref_2936_, v___x_2937_);
                crate::leanh::lean_dec(v_ref_2936_);
                v___x_2939_ = l_Std_DHashMap_term___x7em___00__closed__3;
                v___x_2940_ = l_Std_DHashMap_term___x7em___00__closed__6;
                crate::leanh::lean_inc(v___x_2938_);
                v___x_2941_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2941_, 0, v___x_2938_);
                crate::leanh::lean_ctor_set(v___x_2941_, 1, v___x_2940_);
                v___x_2942_ = l_Lean_Syntax_node3(
                    v___x_2938_,
                    v___x_2939_,
                    v___x_2934_,
                    v___x_2941_,
                    v___x_2935_,
                );
                v___x_2943_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2943_, 0, v___x_2942_);
                crate::leanh::lean_ctor_set(v___x_2943_, 1, v_a_2917_);
                return v___x_2943_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1___boxed(
    mut v_x_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2947_ =
        l_Std_DHashMap___aux__Std__Data__DHashMap__Basic______unexpand__Std__DHashMap__Equiv__1(
            v_x_2944_, v_a_2945_, v_a_2946_,
        );
    crate::leanh::lean_dec(v_a_2945_);
    return v_res_2947_;
}
pub unsafe fn l_Std_DHashMap_insert___redArg(
    mut v_x_2948_: *mut crate::leanh::LeanObject,
    mut v_x_2949_: *mut crate::leanh::LeanObject,
    mut v_m_2950_: *mut crate::leanh::LeanObject,
    mut v_a_2951_: *mut crate::leanh::LeanObject,
    mut v_b_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2948_, v_x_2949_, v_m_2950_, v_a_2951_, v_b_2952_,
    );
    return v___x_2953_;
}
pub unsafe fn l_Std_DHashMap_insert(
    mut v_00_u03b1_2954_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2955_: *mut crate::leanh::LeanObject,
    mut v_x_2956_: *mut crate::leanh::LeanObject,
    mut v_x_2957_: *mut crate::leanh::LeanObject,
    mut v_m_2958_: *mut crate::leanh::LeanObject,
    mut v_a_2959_: *mut crate::leanh::LeanObject,
    mut v_b_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2956_, v_x_2957_, v_m_2958_, v_a_2959_, v_b_2960_,
    );
    return v___x_2961_;
}
pub unsafe fn l_Std_DHashMap_instSingletonSigma___redArg___lam__0(
    mut v_x_2962_: *mut crate::leanh::LeanObject,
    mut v_x_2963_: *mut crate::leanh::LeanObject,
    mut v_x_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2965_ = crate::leanh::lean_ctor_get(v_x_2964_, 0);
    crate::leanh::lean_inc(v_fst_2965_);
    v_snd_2966_ = crate::leanh::lean_ctor_get(v_x_2964_, 1);
    crate::leanh::lean_inc(v_snd_2966_);
    crate::leanh::lean_dec_ref(v_x_2964_);
    v___x_2967_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_2968_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2962_,
        v_x_2963_,
        v___x_2967_,
        v_fst_2965_,
        v_snd_2966_,
    );
    return v___x_2968_;
}
pub unsafe fn l_Std_DHashMap_instSingletonSigma___redArg(
    mut v_x_2969_: *mut crate::leanh::LeanObject,
    mut v_x_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2971_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instSingletonSigma___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2971_, 0, v_x_2969_);
    crate::leanh::lean_closure_set(v___f_2971_, 1, v_x_2970_);
    return v___f_2971_;
}
pub unsafe fn l_Std_DHashMap_instSingletonSigma(
    mut v_00_u03b1_2972_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2973_: *mut crate::leanh::LeanObject,
    mut v_x_2974_: *mut crate::leanh::LeanObject,
    mut v_x_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2976_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instSingletonSigma___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2976_, 0, v_x_2974_);
    crate::leanh::lean_closure_set(v___f_2976_, 1, v_x_2975_);
    return v___f_2976_;
}
pub unsafe fn l_Std_DHashMap_instInsertSigma___redArg___lam__0(
    mut v_x_2977_: *mut crate::leanh::LeanObject,
    mut v_x_2978_: *mut crate::leanh::LeanObject,
    mut v_x_2979_: *mut crate::leanh::LeanObject,
    mut v_s_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2981_ = crate::leanh::lean_ctor_get(v_x_2979_, 0);
    crate::leanh::lean_inc(v_fst_2981_);
    v_snd_2982_ = crate::leanh::lean_ctor_get(v_x_2979_, 1);
    crate::leanh::lean_inc(v_snd_2982_);
    crate::leanh::lean_dec_ref(v_x_2979_);
    v___x_2983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2977_,
        v_x_2978_,
        v_s_2980_,
        v_fst_2981_,
        v_snd_2982_,
    );
    return v___x_2983_;
}
pub unsafe fn l_Std_DHashMap_instInsertSigma___redArg(
    mut v_x_2984_: *mut crate::leanh::LeanObject,
    mut v_x_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2986_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instInsertSigma___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2986_, 0, v_x_2984_);
    crate::leanh::lean_closure_set(v___f_2986_, 1, v_x_2985_);
    return v___f_2986_;
}
pub unsafe fn l_Std_DHashMap_instInsertSigma(
    mut v_00_u03b1_2987_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2988_: *mut crate::leanh::LeanObject,
    mut v_x_2989_: *mut crate::leanh::LeanObject,
    mut v_x_2990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2991_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instInsertSigma___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2991_, 0, v_x_2989_);
    crate::leanh::lean_closure_set(v___f_2991_, 1, v_x_2990_);
    return v___f_2991_;
}
pub unsafe fn l_Std_DHashMap_insertIfNew___redArg(
    mut v_x_2992_: *mut crate::leanh::LeanObject,
    mut v_x_2993_: *mut crate::leanh::LeanObject,
    mut v_m_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_b_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2997_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2992_, v_x_2993_, v_m_2994_, v_a_2995_, v_b_2996_,
    );
    return v___x_2997_;
}
pub unsafe fn l_Std_DHashMap_insertIfNew(
    mut v_00_u03b1_2998_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2999_: *mut crate::leanh::LeanObject,
    mut v_x_3000_: *mut crate::leanh::LeanObject,
    mut v_x_3001_: *mut crate::leanh::LeanObject,
    mut v_m_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_b_3004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3005_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_3000_, v_x_3001_, v_m_3002_, v_a_3003_, v_b_3004_,
    );
    return v___x_3005_;
}
pub unsafe fn l_Std_DHashMap_containsThenInsert___redArg(
    mut v_x_3006_: *mut crate::leanh::LeanObject,
    mut v_x_3007_: *mut crate::leanh::LeanObject,
    mut v_m_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
    mut v_b_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: u64 = 0;
    let mut v___x_3019_: u64 = 0;
    let mut v___x_3020_: u64 = 0;
    let mut v___x_3021_: u64 = 0;
    let mut v_fold_3022_: u64 = 0;
    let mut v___x_3023_: u64 = 0;
    let mut v___x_3024_: u64 = 0;
    let mut v___x_3025_: u64 = 0;
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: usize = 0;
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: usize = 0;
    let mut v_bkt_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    let mut v_val_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3011_ = crate::leanh::lean_ctor_get(v_m_3008_, 0);
                v_buckets_3012_ = crate::leanh::lean_ctor_get(v_m_3008_, 1);
                v_isSharedCheck_3063_ = (!crate::leanh::lean_is_exclusive(v_m_3008_)) as u8;
                if v_isSharedCheck_3063_ == 0 {
                    v___x_3014_ = v_m_3008_;
                    v_isShared_3015_ = v_isSharedCheck_3063_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3012_);
                    crate::leanh::lean_inc(v_size_3011_);
                    crate::leanh::lean_dec(v_m_3008_);
                    v___x_3014_ = crate::leanh::lean_box(0);
                    v_isShared_3015_ = v_isSharedCheck_3063_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3016_ = lean_array_get_size(v_buckets_3012_);
                crate::leanh::lean_inc_ref(v_x_3007_);
                crate::leanh::lean_inc_n(v_a_3009_, 2);
                v___x_3017_ = crate::leanh::lean_apply_1(v_x_3007_, v_a_3009_);
                v___x_3018_ = 32u64;
                v___x_3019_ = crate::leanh::lean_unbox_uint64(v___x_3017_);
                v___x_3020_ = lean_uint64_shift_right(v___x_3019_, v___x_3018_);
                v___x_3021_ = crate::leanh::lean_unbox_uint64(v___x_3017_);
                crate::leanh::lean_dec_ref(v___x_3017_);
                v_fold_3022_ = lean_uint64_xor(v___x_3021_, v___x_3020_);
                v___x_3023_ = 16u64;
                v___x_3024_ = lean_uint64_shift_right(v_fold_3022_, v___x_3023_);
                v___x_3025_ = lean_uint64_xor(v_fold_3022_, v___x_3024_);
                v___x_3026_ = lean_uint64_to_usize(v___x_3025_);
                v___x_3027_ = lean_usize_of_nat(v___x_3016_);
                v___x_3028_ = 1usize;
                v___x_3029_ = lean_usize_sub(v___x_3027_, v___x_3028_);
                v___x_3030_ = lean_usize_land(v___x_3026_, v___x_3029_);
                v_bkt_3031_ = lean_array_uget_borrowed(v_buckets_3012_, v___x_3030_);
                crate::leanh::lean_inc(v_bkt_3031_);
                crate::leanh::lean_inc_ref(v_x_3006_);
                v___x_3032_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_3006_,
                    v_a_3009_,
                    v_bkt_3031_,
                );
                if v___x_3032_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_3006_);
                    v___x_3033_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3034_ = lean_nat_add(v_size_3011_, v___x_3033_);
                    crate::leanh::lean_dec(v_size_3011_);
                    crate::leanh::lean_inc(v_bkt_3031_);
                    v___x_3035_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3035_, 0, v_a_3009_);
                    crate::leanh::lean_ctor_set(v___x_3035_, 1, v_b_3010_);
                    crate::leanh::lean_ctor_set(v___x_3035_, 2, v_bkt_3031_);
                    v_buckets_x27_3036_ =
                        lean_array_uset(v_buckets_3012_, v___x_3030_, v___x_3035_);
                    v___x_3037_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3038_ = lean_nat_mul(v_size_x27_3034_, v___x_3037_);
                    v___x_3039_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3040_ = lean_nat_div(v___x_3038_, v___x_3039_);
                    crate::leanh::lean_dec(v___x_3038_);
                    v___x_3041_ = lean_array_get_size(v_buckets_x27_3036_);
                    v___x_3042_ = lean_nat_dec_le(v___x_3040_, v___x_3041_);
                    crate::leanh::lean_dec(v___x_3040_);
                    if v___x_3042_ == 0 {
                        v_val_3043_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_3007_,
                            v_buckets_x27_3036_,
                        );
                        if v_isShared_3015_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3014_, 1, v_val_3043_);
                            crate::leanh::lean_ctor_set(v___x_3014_, 0, v_size_x27_3034_);
                            v___x_3045_ = v___x_3014_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3048_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3048_,
                                0,
                                v_size_x27_3034_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_val_3043_);
                            v___x_3045_ = v_reuseFailAlloc_3048_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3007_);
                        if v_isShared_3015_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3014_, 1, v_buckets_x27_3036_);
                            crate::leanh::lean_ctor_set(v___x_3014_, 0, v_size_x27_3034_);
                            v___x_3050_ = v___x_3014_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3053_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3053_,
                                0,
                                v_size_x27_3034_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3053_,
                                1,
                                v_buckets_x27_3036_,
                            );
                            v___x_3050_ = v_reuseFailAlloc_3053_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3031_);
                    crate::leanh::lean_dec_ref(v_x_3007_);
                    v___x_3054_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3055_ =
                        lean_array_uset(v_buckets_3012_, v___x_3030_, v___x_3054_);
                    v___x_3056_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_3006_,
                        v_a_3009_,
                        v_b_3010_,
                        v_bkt_3031_,
                    );
                    v___x_3057_ = lean_array_uset(v_buckets_x27_3055_, v___x_3030_, v___x_3056_);
                    if v_isShared_3015_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3014_, 1, v___x_3057_);
                        v___x_3059_ = v___x_3014_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3062_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_size_3011_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3057_);
                        v___x_3059_ = v_reuseFailAlloc_3062_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3046_ = crate::leanh::lean_box((v___x_3032_) as usize);
                v___x_3047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3047_, 0, v___x_3046_);
                crate::leanh::lean_ctor_set(v___x_3047_, 1, v___x_3045_);
                return v___x_3047_;
            }
            3 => {
                v___x_3051_ = crate::leanh::lean_box((v___x_3032_) as usize);
                v___x_3052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3051_);
                crate::leanh::lean_ctor_set(v___x_3052_, 1, v___x_3050_);
                return v___x_3052_;
            }
            4 => {
                v___x_3060_ = crate::leanh::lean_box((v___x_3032_) as usize);
                v___x_3061_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3060_);
                crate::leanh::lean_ctor_set(v___x_3061_, 1, v___x_3059_);
                return v___x_3061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_containsThenInsert(
    mut v_00_u03b1_3064_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3065_: *mut crate::leanh::LeanObject,
    mut v_x_3066_: *mut crate::leanh::LeanObject,
    mut v_x_3067_: *mut crate::leanh::LeanObject,
    mut v_m_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
    mut v_b_3070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3075_: u8 = 0;
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u64 = 0;
    let mut v___x_3079_: u64 = 0;
    let mut v___x_3080_: u64 = 0;
    let mut v___x_3081_: u64 = 0;
    let mut v_fold_3082_: u64 = 0;
    let mut v___x_3083_: u64 = 0;
    let mut v___x_3084_: u64 = 0;
    let mut v___x_3085_: u64 = 0;
    let mut v___x_3086_: usize = 0;
    let mut v___x_3087_: usize = 0;
    let mut v___x_3088_: usize = 0;
    let mut v___x_3089_: usize = 0;
    let mut v___x_3090_: usize = 0;
    let mut v_bkt_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v_val_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3071_ = crate::leanh::lean_ctor_get(v_m_3068_, 0);
                v_buckets_3072_ = crate::leanh::lean_ctor_get(v_m_3068_, 1);
                v_isSharedCheck_3123_ = (!crate::leanh::lean_is_exclusive(v_m_3068_)) as u8;
                if v_isSharedCheck_3123_ == 0 {
                    v___x_3074_ = v_m_3068_;
                    v_isShared_3075_ = v_isSharedCheck_3123_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3072_);
                    crate::leanh::lean_inc(v_size_3071_);
                    crate::leanh::lean_dec(v_m_3068_);
                    v___x_3074_ = crate::leanh::lean_box(0);
                    v_isShared_3075_ = v_isSharedCheck_3123_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3076_ = lean_array_get_size(v_buckets_3072_);
                crate::leanh::lean_inc_ref(v_x_3067_);
                crate::leanh::lean_inc_n(v_a_3069_, 2);
                v___x_3077_ = crate::leanh::lean_apply_1(v_x_3067_, v_a_3069_);
                v___x_3078_ = 32u64;
                v___x_3079_ = crate::leanh::lean_unbox_uint64(v___x_3077_);
                v___x_3080_ = lean_uint64_shift_right(v___x_3079_, v___x_3078_);
                v___x_3081_ = crate::leanh::lean_unbox_uint64(v___x_3077_);
                crate::leanh::lean_dec_ref(v___x_3077_);
                v_fold_3082_ = lean_uint64_xor(v___x_3081_, v___x_3080_);
                v___x_3083_ = 16u64;
                v___x_3084_ = lean_uint64_shift_right(v_fold_3082_, v___x_3083_);
                v___x_3085_ = lean_uint64_xor(v_fold_3082_, v___x_3084_);
                v___x_3086_ = lean_uint64_to_usize(v___x_3085_);
                v___x_3087_ = lean_usize_of_nat(v___x_3076_);
                v___x_3088_ = 1usize;
                v___x_3089_ = lean_usize_sub(v___x_3087_, v___x_3088_);
                v___x_3090_ = lean_usize_land(v___x_3086_, v___x_3089_);
                v_bkt_3091_ = lean_array_uget_borrowed(v_buckets_3072_, v___x_3090_);
                crate::leanh::lean_inc(v_bkt_3091_);
                crate::leanh::lean_inc_ref(v_x_3066_);
                v___x_3092_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_3066_,
                    v_a_3069_,
                    v_bkt_3091_,
                );
                if v___x_3092_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_3066_);
                    v___x_3093_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3094_ = lean_nat_add(v_size_3071_, v___x_3093_);
                    crate::leanh::lean_dec(v_size_3071_);
                    crate::leanh::lean_inc(v_bkt_3091_);
                    v___x_3095_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3095_, 0, v_a_3069_);
                    crate::leanh::lean_ctor_set(v___x_3095_, 1, v_b_3070_);
                    crate::leanh::lean_ctor_set(v___x_3095_, 2, v_bkt_3091_);
                    v_buckets_x27_3096_ =
                        lean_array_uset(v_buckets_3072_, v___x_3090_, v___x_3095_);
                    v___x_3097_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3098_ = lean_nat_mul(v_size_x27_3094_, v___x_3097_);
                    v___x_3099_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3100_ = lean_nat_div(v___x_3098_, v___x_3099_);
                    crate::leanh::lean_dec(v___x_3098_);
                    v___x_3101_ = lean_array_get_size(v_buckets_x27_3096_);
                    v___x_3102_ = lean_nat_dec_le(v___x_3100_, v___x_3101_);
                    crate::leanh::lean_dec(v___x_3100_);
                    if v___x_3102_ == 0 {
                        v_val_3103_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_3067_,
                            v_buckets_x27_3096_,
                        );
                        if v_isShared_3075_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3074_, 1, v_val_3103_);
                            crate::leanh::lean_ctor_set(v___x_3074_, 0, v_size_x27_3094_);
                            v___x_3105_ = v___x_3074_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3108_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3108_,
                                0,
                                v_size_x27_3094_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_val_3103_);
                            v___x_3105_ = v_reuseFailAlloc_3108_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3067_);
                        if v_isShared_3075_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3074_, 1, v_buckets_x27_3096_);
                            crate::leanh::lean_ctor_set(v___x_3074_, 0, v_size_x27_3094_);
                            v___x_3110_ = v___x_3074_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3113_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3113_,
                                0,
                                v_size_x27_3094_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3113_,
                                1,
                                v_buckets_x27_3096_,
                            );
                            v___x_3110_ = v_reuseFailAlloc_3113_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3091_);
                    crate::leanh::lean_dec_ref(v_x_3067_);
                    v___x_3114_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3115_ =
                        lean_array_uset(v_buckets_3072_, v___x_3090_, v___x_3114_);
                    v___x_3116_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_3066_,
                        v_a_3069_,
                        v_b_3070_,
                        v_bkt_3091_,
                    );
                    v___x_3117_ = lean_array_uset(v_buckets_x27_3115_, v___x_3090_, v___x_3116_);
                    if v_isShared_3075_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3074_, 1, v___x_3117_);
                        v___x_3119_ = v___x_3074_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_size_3071_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3117_);
                        v___x_3119_ = v_reuseFailAlloc_3122_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3106_ = crate::leanh::lean_box((v___x_3092_) as usize);
                v___x_3107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3107_, 0, v___x_3106_);
                crate::leanh::lean_ctor_set(v___x_3107_, 1, v___x_3105_);
                return v___x_3107_;
            }
            3 => {
                v___x_3111_ = crate::leanh::lean_box((v___x_3092_) as usize);
                v___x_3112_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3112_, 0, v___x_3111_);
                crate::leanh::lean_ctor_set(v___x_3112_, 1, v___x_3110_);
                return v___x_3112_;
            }
            4 => {
                v___x_3120_ = crate::leanh::lean_box((v___x_3092_) as usize);
                v___x_3121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3121_, 0, v___x_3120_);
                crate::leanh::lean_ctor_set(v___x_3121_, 1, v___x_3119_);
                return v___x_3121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_containsThenInsertIfNew___redArg(
    mut v_x_3124_: *mut crate::leanh::LeanObject,
    mut v_x_3125_: *mut crate::leanh::LeanObject,
    mut v_m_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_b_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: u64 = 0;
    let mut v___x_3134_: u64 = 0;
    let mut v___x_3135_: u64 = 0;
    let mut v___x_3136_: u64 = 0;
    let mut v_fold_3137_: u64 = 0;
    let mut v___x_3138_: u64 = 0;
    let mut v___x_3139_: u64 = 0;
    let mut v___x_3140_: u64 = 0;
    let mut v___x_3141_: usize = 0;
    let mut v___x_3142_: usize = 0;
    let mut v___x_3143_: usize = 0;
    let mut v___x_3144_: usize = 0;
    let mut v___x_3145_: usize = 0;
    let mut v_bkt_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3150_: u8 = 0;
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: u8 = 0;
    let mut v_val_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3172_: u8 = 0;
    let mut v_unused_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3129_ = crate::leanh::lean_ctor_get(v_m_3126_, 0);
                v_buckets_3130_ = crate::leanh::lean_ctor_get(v_m_3126_, 1);
                v___x_3131_ = lean_array_get_size(v_buckets_3130_);
                crate::leanh::lean_inc_ref(v_x_3125_);
                crate::leanh::lean_inc_n(v_a_3127_, 2);
                v___x_3132_ = crate::leanh::lean_apply_1(v_x_3125_, v_a_3127_);
                v___x_3133_ = 32u64;
                v___x_3134_ = crate::leanh::lean_unbox_uint64(v___x_3132_);
                v___x_3135_ = lean_uint64_shift_right(v___x_3134_, v___x_3133_);
                v___x_3136_ = crate::leanh::lean_unbox_uint64(v___x_3132_);
                crate::leanh::lean_dec_ref(v___x_3132_);
                v_fold_3137_ = lean_uint64_xor(v___x_3136_, v___x_3135_);
                v___x_3138_ = 16u64;
                v___x_3139_ = lean_uint64_shift_right(v_fold_3137_, v___x_3138_);
                v___x_3140_ = lean_uint64_xor(v_fold_3137_, v___x_3139_);
                v___x_3141_ = lean_uint64_to_usize(v___x_3140_);
                v___x_3142_ = lean_usize_of_nat(v___x_3131_);
                v___x_3143_ = 1usize;
                v___x_3144_ = lean_usize_sub(v___x_3142_, v___x_3143_);
                v___x_3145_ = lean_usize_land(v___x_3141_, v___x_3144_);
                v_bkt_3146_ = lean_array_uget_borrowed(v_buckets_3130_, v___x_3145_);
                crate::leanh::lean_inc(v_bkt_3146_);
                v___x_3147_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_3124_,
                    v_a_3127_,
                    v_bkt_3146_,
                );
                if v___x_3147_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3130_);
                    crate::leanh::lean_inc(v_size_3129_);
                    v_isSharedCheck_3172_ = (!crate::leanh::lean_is_exclusive(v_m_3126_)) as u8;
                    if v_isSharedCheck_3172_ == 0 {
                        v_unused_3173_ = crate::leanh::lean_ctor_get(v_m_3126_, 1);
                        crate::leanh::lean_dec(v_unused_3173_);
                        v_unused_3174_ = crate::leanh::lean_ctor_get(v_m_3126_, 0);
                        crate::leanh::lean_dec(v_unused_3174_);
                        v___x_3149_ = v_m_3126_;
                        v_isShared_3150_ = v_isSharedCheck_3172_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3126_);
                        v___x_3149_ = crate::leanh::lean_box(0);
                        v_isShared_3150_ = v_isSharedCheck_3172_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3128_);
                    crate::leanh::lean_dec(v_a_3127_);
                    crate::leanh::lean_dec_ref(v_x_3125_);
                    v___x_3175_ = crate::leanh::lean_box((v___x_3147_) as usize);
                    v___x_3176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3176_, 0, v___x_3175_);
                    crate::leanh::lean_ctor_set(v___x_3176_, 1, v_m_3126_);
                    return v___x_3176_;
                }
            }
            1 => {
                v___x_3151_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3152_ = lean_nat_add(v_size_3129_, v___x_3151_);
                crate::leanh::lean_dec(v_size_3129_);
                crate::leanh::lean_inc(v_bkt_3146_);
                v___x_3153_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3153_, 0, v_a_3127_);
                crate::leanh::lean_ctor_set(v___x_3153_, 1, v_b_3128_);
                crate::leanh::lean_ctor_set(v___x_3153_, 2, v_bkt_3146_);
                v_buckets_x27_3154_ = lean_array_uset(v_buckets_3130_, v___x_3145_, v___x_3153_);
                v___x_3155_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3156_ = lean_nat_mul(v_size_x27_3152_, v___x_3155_);
                v___x_3157_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3158_ = lean_nat_div(v___x_3156_, v___x_3157_);
                crate::leanh::lean_dec(v___x_3156_);
                v___x_3159_ = lean_array_get_size(v_buckets_x27_3154_);
                v___x_3160_ = lean_nat_dec_le(v___x_3158_, v___x_3159_);
                crate::leanh::lean_dec(v___x_3158_);
                if v___x_3160_ == 0 {
                    v_val_3161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_3125_,
                        v_buckets_x27_3154_,
                    );
                    if v_isShared_3150_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3149_, 1, v_val_3161_);
                        crate::leanh::lean_ctor_set(v___x_3149_, 0, v_size_x27_3152_);
                        v___x_3163_ = v___x_3149_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3166_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_size_x27_3152_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_val_3161_);
                        v___x_3163_ = v_reuseFailAlloc_3166_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3125_);
                    if v_isShared_3150_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3149_, 1, v_buckets_x27_3154_);
                        crate::leanh::lean_ctor_set(v___x_3149_, 0, v_size_x27_3152_);
                        v___x_3168_ = v___x_3149_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3171_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_size_x27_3152_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_buckets_x27_3154_);
                        v___x_3168_ = v_reuseFailAlloc_3171_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3164_ = crate::leanh::lean_box((v___x_3147_) as usize);
                v___x_3165_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3165_, 0, v___x_3164_);
                crate::leanh::lean_ctor_set(v___x_3165_, 1, v___x_3163_);
                return v___x_3165_;
            }
            3 => {
                v___x_3169_ = crate::leanh::lean_box((v___x_3147_) as usize);
                v___x_3170_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3169_);
                crate::leanh::lean_ctor_set(v___x_3170_, 1, v___x_3168_);
                return v___x_3170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_containsThenInsertIfNew(
    mut v_00_u03b1_3177_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3178_: *mut crate::leanh::LeanObject,
    mut v_x_3179_: *mut crate::leanh::LeanObject,
    mut v_x_3180_: *mut crate::leanh::LeanObject,
    mut v_m_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_b_3183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: u64 = 0;
    let mut v___x_3189_: u64 = 0;
    let mut v___x_3190_: u64 = 0;
    let mut v___x_3191_: u64 = 0;
    let mut v_fold_3192_: u64 = 0;
    let mut v___x_3193_: u64 = 0;
    let mut v___x_3194_: u64 = 0;
    let mut v___x_3195_: u64 = 0;
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: usize = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: usize = 0;
    let mut v___x_3200_: usize = 0;
    let mut v_bkt_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v_val_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3227_: u8 = 0;
    let mut v_unused_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3184_ = crate::leanh::lean_ctor_get(v_m_3181_, 0);
                v_buckets_3185_ = crate::leanh::lean_ctor_get(v_m_3181_, 1);
                v___x_3186_ = lean_array_get_size(v_buckets_3185_);
                crate::leanh::lean_inc_ref(v_x_3180_);
                crate::leanh::lean_inc_n(v_a_3182_, 2);
                v___x_3187_ = crate::leanh::lean_apply_1(v_x_3180_, v_a_3182_);
                v___x_3188_ = 32u64;
                v___x_3189_ = crate::leanh::lean_unbox_uint64(v___x_3187_);
                v___x_3190_ = lean_uint64_shift_right(v___x_3189_, v___x_3188_);
                v___x_3191_ = crate::leanh::lean_unbox_uint64(v___x_3187_);
                crate::leanh::lean_dec_ref(v___x_3187_);
                v_fold_3192_ = lean_uint64_xor(v___x_3191_, v___x_3190_);
                v___x_3193_ = 16u64;
                v___x_3194_ = lean_uint64_shift_right(v_fold_3192_, v___x_3193_);
                v___x_3195_ = lean_uint64_xor(v_fold_3192_, v___x_3194_);
                v___x_3196_ = lean_uint64_to_usize(v___x_3195_);
                v___x_3197_ = lean_usize_of_nat(v___x_3186_);
                v___x_3198_ = 1usize;
                v___x_3199_ = lean_usize_sub(v___x_3197_, v___x_3198_);
                v___x_3200_ = lean_usize_land(v___x_3196_, v___x_3199_);
                v_bkt_3201_ = lean_array_uget_borrowed(v_buckets_3185_, v___x_3200_);
                crate::leanh::lean_inc(v_bkt_3201_);
                v___x_3202_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_3179_,
                    v_a_3182_,
                    v_bkt_3201_,
                );
                if v___x_3202_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3185_);
                    crate::leanh::lean_inc(v_size_3184_);
                    v_isSharedCheck_3227_ = (!crate::leanh::lean_is_exclusive(v_m_3181_)) as u8;
                    if v_isSharedCheck_3227_ == 0 {
                        v_unused_3228_ = crate::leanh::lean_ctor_get(v_m_3181_, 1);
                        crate::leanh::lean_dec(v_unused_3228_);
                        v_unused_3229_ = crate::leanh::lean_ctor_get(v_m_3181_, 0);
                        crate::leanh::lean_dec(v_unused_3229_);
                        v___x_3204_ = v_m_3181_;
                        v_isShared_3205_ = v_isSharedCheck_3227_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3181_);
                        v___x_3204_ = crate::leanh::lean_box(0);
                        v_isShared_3205_ = v_isSharedCheck_3227_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3183_);
                    crate::leanh::lean_dec(v_a_3182_);
                    crate::leanh::lean_dec_ref(v_x_3180_);
                    v___x_3230_ = crate::leanh::lean_box((v___x_3202_) as usize);
                    v___x_3231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3231_, 0, v___x_3230_);
                    crate::leanh::lean_ctor_set(v___x_3231_, 1, v_m_3181_);
                    return v___x_3231_;
                }
            }
            1 => {
                v___x_3206_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3207_ = lean_nat_add(v_size_3184_, v___x_3206_);
                crate::leanh::lean_dec(v_size_3184_);
                crate::leanh::lean_inc(v_bkt_3201_);
                v___x_3208_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3208_, 0, v_a_3182_);
                crate::leanh::lean_ctor_set(v___x_3208_, 1, v_b_3183_);
                crate::leanh::lean_ctor_set(v___x_3208_, 2, v_bkt_3201_);
                v_buckets_x27_3209_ = lean_array_uset(v_buckets_3185_, v___x_3200_, v___x_3208_);
                v___x_3210_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3211_ = lean_nat_mul(v_size_x27_3207_, v___x_3210_);
                v___x_3212_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3213_ = lean_nat_div(v___x_3211_, v___x_3212_);
                crate::leanh::lean_dec(v___x_3211_);
                v___x_3214_ = lean_array_get_size(v_buckets_x27_3209_);
                v___x_3215_ = lean_nat_dec_le(v___x_3213_, v___x_3214_);
                crate::leanh::lean_dec(v___x_3213_);
                if v___x_3215_ == 0 {
                    v_val_3216_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_3180_,
                        v_buckets_x27_3209_,
                    );
                    if v_isShared_3205_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3204_, 1, v_val_3216_);
                        crate::leanh::lean_ctor_set(v___x_3204_, 0, v_size_x27_3207_);
                        v___x_3218_ = v___x_3204_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_size_x27_3207_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_val_3216_);
                        v___x_3218_ = v_reuseFailAlloc_3221_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3180_);
                    if v_isShared_3205_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3204_, 1, v_buckets_x27_3209_);
                        crate::leanh::lean_ctor_set(v___x_3204_, 0, v_size_x27_3207_);
                        v___x_3223_ = v___x_3204_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_size_x27_3207_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_buckets_x27_3209_);
                        v___x_3223_ = v_reuseFailAlloc_3226_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3219_ = crate::leanh::lean_box((v___x_3202_) as usize);
                v___x_3220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3220_, 0, v___x_3219_);
                crate::leanh::lean_ctor_set(v___x_3220_, 1, v___x_3218_);
                return v___x_3220_;
            }
            3 => {
                v___x_3224_ = crate::leanh::lean_box((v___x_3202_) as usize);
                v___x_3225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3225_, 0, v___x_3224_);
                crate::leanh::lean_ctor_set(v___x_3225_, 1, v___x_3223_);
                return v___x_3225_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_getThenInsertIfNew_x3f___redArg(
    mut v_x_3232_: *mut crate::leanh::LeanObject,
    mut v_x_3233_: *mut crate::leanh::LeanObject,
    mut v_m_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_b_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: u64 = 0;
    let mut v___x_3242_: u64 = 0;
    let mut v___x_3243_: u64 = 0;
    let mut v___x_3244_: u64 = 0;
    let mut v_fold_3245_: u64 = 0;
    let mut v___x_3246_: u64 = 0;
    let mut v___x_3247_: u64 = 0;
    let mut v___x_3248_: u64 = 0;
    let mut v___x_3249_: usize = 0;
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v___x_3253_: usize = 0;
    let mut v_bkt_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v_val_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3278_: u8 = 0;
    let mut v_unused_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3237_ = crate::leanh::lean_ctor_get(v_m_3234_, 0);
                v_buckets_3238_ = crate::leanh::lean_ctor_get(v_m_3234_, 1);
                v___x_3239_ = lean_array_get_size(v_buckets_3238_);
                crate::leanh::lean_inc_ref(v_x_3233_);
                crate::leanh::lean_inc_n(v_a_3235_, 2);
                v___x_3240_ = crate::leanh::lean_apply_1(v_x_3233_, v_a_3235_);
                v___x_3241_ = 32u64;
                v___x_3242_ = crate::leanh::lean_unbox_uint64(v___x_3240_);
                v___x_3243_ = lean_uint64_shift_right(v___x_3242_, v___x_3241_);
                v___x_3244_ = crate::leanh::lean_unbox_uint64(v___x_3240_);
                crate::leanh::lean_dec_ref(v___x_3240_);
                v_fold_3245_ = lean_uint64_xor(v___x_3244_, v___x_3243_);
                v___x_3246_ = 16u64;
                v___x_3247_ = lean_uint64_shift_right(v_fold_3245_, v___x_3246_);
                v___x_3248_ = lean_uint64_xor(v_fold_3245_, v___x_3247_);
                v___x_3249_ = lean_uint64_to_usize(v___x_3248_);
                v___x_3250_ = lean_usize_of_nat(v___x_3239_);
                v___x_3251_ = 1usize;
                v___x_3252_ = lean_usize_sub(v___x_3250_, v___x_3251_);
                v___x_3253_ = lean_usize_land(v___x_3249_, v___x_3252_);
                v_bkt_3254_ = lean_array_uget_borrowed(v_buckets_3238_, v___x_3253_);
                crate::leanh::lean_inc(v_bkt_3254_);
                v___x_3255_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_3232_,
                    v_a_3235_,
                    v_bkt_3254_,
                );
                if crate::leanh::lean_obj_tag(v___x_3255_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3238_);
                    crate::leanh::lean_inc(v_size_3237_);
                    v_isSharedCheck_3278_ = (!crate::leanh::lean_is_exclusive(v_m_3234_)) as u8;
                    if v_isSharedCheck_3278_ == 0 {
                        v_unused_3279_ = crate::leanh::lean_ctor_get(v_m_3234_, 1);
                        crate::leanh::lean_dec(v_unused_3279_);
                        v_unused_3280_ = crate::leanh::lean_ctor_get(v_m_3234_, 0);
                        crate::leanh::lean_dec(v_unused_3280_);
                        v___x_3257_ = v_m_3234_;
                        v_isShared_3258_ = v_isSharedCheck_3278_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3234_);
                        v___x_3257_ = crate::leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3278_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3236_);
                    crate::leanh::lean_dec(v_a_3235_);
                    crate::leanh::lean_dec_ref(v_x_3233_);
                    v___x_3281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3281_, 0, v___x_3255_);
                    crate::leanh::lean_ctor_set(v___x_3281_, 1, v_m_3234_);
                    return v___x_3281_;
                }
            }
            1 => {
                v___x_3259_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3260_ = lean_nat_add(v_size_3237_, v___x_3259_);
                crate::leanh::lean_dec(v_size_3237_);
                crate::leanh::lean_inc(v_bkt_3254_);
                v___x_3261_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3261_, 0, v_a_3235_);
                crate::leanh::lean_ctor_set(v___x_3261_, 1, v_b_3236_);
                crate::leanh::lean_ctor_set(v___x_3261_, 2, v_bkt_3254_);
                v_buckets_x27_3262_ = lean_array_uset(v_buckets_3238_, v___x_3253_, v___x_3261_);
                v___x_3263_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3264_ = lean_nat_mul(v_size_x27_3260_, v___x_3263_);
                v___x_3265_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3266_ = lean_nat_div(v___x_3264_, v___x_3265_);
                crate::leanh::lean_dec(v___x_3264_);
                v___x_3267_ = lean_array_get_size(v_buckets_x27_3262_);
                v___x_3268_ = lean_nat_dec_le(v___x_3266_, v___x_3267_);
                crate::leanh::lean_dec(v___x_3266_);
                if v___x_3268_ == 0 {
                    v_val_3269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_3233_,
                        v_buckets_x27_3262_,
                    );
                    if v_isShared_3258_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3257_, 1, v_val_3269_);
                        crate::leanh::lean_ctor_set(v___x_3257_, 0, v_size_x27_3260_);
                        v___x_3271_ = v___x_3257_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_size_x27_3260_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_val_3269_);
                        v___x_3271_ = v_reuseFailAlloc_3273_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3233_);
                    if v_isShared_3258_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3257_, 1, v_buckets_x27_3262_);
                        crate::leanh::lean_ctor_set(v___x_3257_, 0, v_size_x27_3260_);
                        v___x_3275_ = v___x_3257_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3277_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_size_x27_3260_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_buckets_x27_3262_);
                        v___x_3275_ = v_reuseFailAlloc_3277_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3272_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3272_, 0, v___x_3255_);
                crate::leanh::lean_ctor_set(v___x_3272_, 1, v___x_3271_);
                return v___x_3272_;
            }
            3 => {
                v___x_3276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3276_, 0, v___x_3255_);
                crate::leanh::lean_ctor_set(v___x_3276_, 1, v___x_3275_);
                return v___x_3276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_3282_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3283_: *mut crate::leanh::LeanObject,
    mut v_x_3284_: *mut crate::leanh::LeanObject,
    mut v_x_3285_: *mut crate::leanh::LeanObject,
    mut v_inst_3286_: *mut crate::leanh::LeanObject,
    mut v_m_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
    mut v_b_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: u64 = 0;
    let mut v___x_3295_: u64 = 0;
    let mut v___x_3296_: u64 = 0;
    let mut v___x_3297_: u64 = 0;
    let mut v_fold_3298_: u64 = 0;
    let mut v___x_3299_: u64 = 0;
    let mut v___x_3300_: u64 = 0;
    let mut v___x_3301_: u64 = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: usize = 0;
    let mut v___x_3304_: usize = 0;
    let mut v___x_3305_: usize = 0;
    let mut v___x_3306_: usize = 0;
    let mut v_bkt_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3311_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: u8 = 0;
    let mut v_val_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_unused_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3290_ = crate::leanh::lean_ctor_get(v_m_3287_, 0);
                v_buckets_3291_ = crate::leanh::lean_ctor_get(v_m_3287_, 1);
                v___x_3292_ = lean_array_get_size(v_buckets_3291_);
                crate::leanh::lean_inc_ref(v_x_3285_);
                crate::leanh::lean_inc_n(v_a_3288_, 2);
                v___x_3293_ = crate::leanh::lean_apply_1(v_x_3285_, v_a_3288_);
                v___x_3294_ = 32u64;
                v___x_3295_ = crate::leanh::lean_unbox_uint64(v___x_3293_);
                v___x_3296_ = lean_uint64_shift_right(v___x_3295_, v___x_3294_);
                v___x_3297_ = crate::leanh::lean_unbox_uint64(v___x_3293_);
                crate::leanh::lean_dec_ref(v___x_3293_);
                v_fold_3298_ = lean_uint64_xor(v___x_3297_, v___x_3296_);
                v___x_3299_ = 16u64;
                v___x_3300_ = lean_uint64_shift_right(v_fold_3298_, v___x_3299_);
                v___x_3301_ = lean_uint64_xor(v_fold_3298_, v___x_3300_);
                v___x_3302_ = lean_uint64_to_usize(v___x_3301_);
                v___x_3303_ = lean_usize_of_nat(v___x_3292_);
                v___x_3304_ = 1usize;
                v___x_3305_ = lean_usize_sub(v___x_3303_, v___x_3304_);
                v___x_3306_ = lean_usize_land(v___x_3302_, v___x_3305_);
                v_bkt_3307_ = lean_array_uget_borrowed(v_buckets_3291_, v___x_3306_);
                crate::leanh::lean_inc(v_bkt_3307_);
                v___x_3308_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_x_3284_,
                    v_a_3288_,
                    v_bkt_3307_,
                );
                if crate::leanh::lean_obj_tag(v___x_3308_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3291_);
                    crate::leanh::lean_inc(v_size_3290_);
                    v_isSharedCheck_3331_ = (!crate::leanh::lean_is_exclusive(v_m_3287_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v_unused_3332_ = crate::leanh::lean_ctor_get(v_m_3287_, 1);
                        crate::leanh::lean_dec(v_unused_3332_);
                        v_unused_3333_ = crate::leanh::lean_ctor_get(v_m_3287_, 0);
                        crate::leanh::lean_dec(v_unused_3333_);
                        v___x_3310_ = v_m_3287_;
                        v_isShared_3311_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3287_);
                        v___x_3310_ = crate::leanh::lean_box(0);
                        v_isShared_3311_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3289_);
                    crate::leanh::lean_dec(v_a_3288_);
                    crate::leanh::lean_dec_ref(v_x_3285_);
                    v___x_3334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3334_, 0, v___x_3308_);
                    crate::leanh::lean_ctor_set(v___x_3334_, 1, v_m_3287_);
                    return v___x_3334_;
                }
            }
            1 => {
                v___x_3312_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3313_ = lean_nat_add(v_size_3290_, v___x_3312_);
                crate::leanh::lean_dec(v_size_3290_);
                crate::leanh::lean_inc(v_bkt_3307_);
                v___x_3314_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3314_, 0, v_a_3288_);
                crate::leanh::lean_ctor_set(v___x_3314_, 1, v_b_3289_);
                crate::leanh::lean_ctor_set(v___x_3314_, 2, v_bkt_3307_);
                v_buckets_x27_3315_ = lean_array_uset(v_buckets_3291_, v___x_3306_, v___x_3314_);
                v___x_3316_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3317_ = lean_nat_mul(v_size_x27_3313_, v___x_3316_);
                v___x_3318_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3319_ = lean_nat_div(v___x_3317_, v___x_3318_);
                crate::leanh::lean_dec(v___x_3317_);
                v___x_3320_ = lean_array_get_size(v_buckets_x27_3315_);
                v___x_3321_ = lean_nat_dec_le(v___x_3319_, v___x_3320_);
                crate::leanh::lean_dec(v___x_3319_);
                if v___x_3321_ == 0 {
                    v_val_3322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_3285_,
                        v_buckets_x27_3315_,
                    );
                    if v_isShared_3311_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3310_, 1, v_val_3322_);
                        crate::leanh::lean_ctor_set(v___x_3310_, 0, v_size_x27_3313_);
                        v___x_3324_ = v___x_3310_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_size_x27_3313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_val_3322_);
                        v___x_3324_ = v_reuseFailAlloc_3326_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3285_);
                    if v_isShared_3311_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3310_, 1, v_buckets_x27_3315_);
                        crate::leanh::lean_ctor_set(v___x_3310_, 0, v_size_x27_3313_);
                        v___x_3328_ = v___x_3310_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_size_x27_3313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_buckets_x27_3315_);
                        v___x_3328_ = v_reuseFailAlloc_3330_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3325_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3325_, 0, v___x_3308_);
                crate::leanh::lean_ctor_set(v___x_3325_, 1, v___x_3324_);
                return v___x_3325_;
            }
            3 => {
                v___x_3329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3329_, 0, v___x_3308_);
                crate::leanh::lean_ctor_set(v___x_3329_, 1, v___x_3328_);
                return v___x_3329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_get_x3f___redArg(
    mut v_x_3335_: *mut crate::leanh::LeanObject,
    mut v_x_3336_: *mut crate::leanh::LeanObject,
    mut v_m_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_3335_, v_x_3336_, v_m_3337_, v_a_3338_,
    );
    return v___x_3339_;
}
pub unsafe fn l_Std_DHashMap_get_x3f___redArg___boxed(
    mut v_x_3340_: *mut crate::leanh::LeanObject,
    mut v_x_3341_: *mut crate::leanh::LeanObject,
    mut v_m_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3344_ = l_Std_DHashMap_get_x3f___redArg(v_x_3340_, v_x_3341_, v_m_3342_, v_a_3343_);
    crate::leanh::lean_dec_ref(v_m_3342_);
    return v_res_3344_;
}
pub unsafe fn l_Std_DHashMap_get_x3f(
    mut v_00_u03b1_3345_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3346_: *mut crate::leanh::LeanObject,
    mut v_x_3347_: *mut crate::leanh::LeanObject,
    mut v_x_3348_: *mut crate::leanh::LeanObject,
    mut v_inst_3349_: *mut crate::leanh::LeanObject,
    mut v_m_3350_: *mut crate::leanh::LeanObject,
    mut v_a_3351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3352_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_x_3347_, v_x_3348_, v_m_3350_, v_a_3351_,
    );
    return v___x_3352_;
}
pub unsafe fn l_Std_DHashMap_get_x3f___boxed(
    mut v_00_u03b1_3353_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3354_: *mut crate::leanh::LeanObject,
    mut v_x_3355_: *mut crate::leanh::LeanObject,
    mut v_x_3356_: *mut crate::leanh::LeanObject,
    mut v_inst_3357_: *mut crate::leanh::LeanObject,
    mut v_m_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3360_ = l_Std_DHashMap_get_x3f(
        v_00_u03b1_3353_,
        v_00_u03b2_3354_,
        v_x_3355_,
        v_x_3356_,
        v_inst_3357_,
        v_m_3358_,
        v_a_3359_,
    );
    crate::leanh::lean_dec_ref(v_m_3358_);
    return v_res_3360_;
}
pub unsafe fn l_Std_DHashMap_contains___redArg(
    mut v_x_3361_: *mut crate::leanh::LeanObject,
    mut v_x_3362_: *mut crate::leanh::LeanObject,
    mut v_m_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3365_: u8 = 0;
    v___x_3365_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_3361_, v_x_3362_, v_m_3363_, v_a_3364_,
    );
    return v___x_3365_;
}
pub unsafe fn l_Std_DHashMap_contains___redArg___boxed(
    mut v_x_3366_: *mut crate::leanh::LeanObject,
    mut v_x_3367_: *mut crate::leanh::LeanObject,
    mut v_m_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3370_: u8 = 0;
    let mut v_r_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3370_ = l_Std_DHashMap_contains___redArg(v_x_3366_, v_x_3367_, v_m_3368_, v_a_3369_);
    crate::leanh::lean_dec_ref(v_m_3368_);
    v_r_3371_ = crate::leanh::lean_box((v_res_3370_) as usize);
    return v_r_3371_;
}
pub unsafe fn l_Std_DHashMap_contains(
    mut v_00_u03b1_3372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3373_: *mut crate::leanh::LeanObject,
    mut v_x_3374_: *mut crate::leanh::LeanObject,
    mut v_x_3375_: *mut crate::leanh::LeanObject,
    mut v_m_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3378_: u8 = 0;
    v___x_3378_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_3374_, v_x_3375_, v_m_3376_, v_a_3377_,
    );
    return v___x_3378_;
}
pub unsafe fn l_Std_DHashMap_contains___boxed(
    mut v_00_u03b1_3379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3380_: *mut crate::leanh::LeanObject,
    mut v_x_3381_: *mut crate::leanh::LeanObject,
    mut v_x_3382_: *mut crate::leanh::LeanObject,
    mut v_m_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3385_: u8 = 0;
    let mut v_r_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3385_ = l_Std_DHashMap_contains(
        v_00_u03b1_3379_,
        v_00_u03b2_3380_,
        v_x_3381_,
        v_x_3382_,
        v_m_3383_,
        v_a_3384_,
    );
    crate::leanh::lean_dec_ref(v_m_3383_);
    v_r_3386_ = crate::leanh::lean_box((v_res_3385_) as usize);
    return v_r_3386_;
}
pub unsafe fn l_Std_DHashMap_instMembership(
    mut v_00_u03b1_3387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3388_: *mut crate::leanh::LeanObject,
    mut v_inst_3389_: *mut crate::leanh::LeanObject,
    mut v_inst_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = crate::leanh::lean_box(0);
    return v___x_3391_;
}
pub unsafe fn l_Std_DHashMap_instMembership___boxed(
    mut v_00_u03b1_3392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3393_: *mut crate::leanh::LeanObject,
    mut v_inst_3394_: *mut crate::leanh::LeanObject,
    mut v_inst_3395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3396_ = l_Std_DHashMap_instMembership(
        v_00_u03b1_3392_,
        v_00_u03b2_3393_,
        v_inst_3394_,
        v_inst_3395_,
    );
    crate::leanh::lean_dec_ref(v_inst_3395_);
    crate::leanh::lean_dec_ref(v_inst_3394_);
    return v_res_3396_;
}
pub unsafe fn l_Std_DHashMap_instDecidableMem___redArg(
    mut v_inst_3397_: *mut crate::leanh::LeanObject,
    mut v_inst_3398_: *mut crate::leanh::LeanObject,
    mut v_m_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3401_: u8 = 0;
    v___x_3401_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_3397_,
        v_inst_3398_,
        v_m_3399_,
        v_a_3400_,
    );
    return v___x_3401_;
}
pub unsafe fn l_Std_DHashMap_instDecidableMem___redArg___boxed(
    mut v_inst_3402_: *mut crate::leanh::LeanObject,
    mut v_inst_3403_: *mut crate::leanh::LeanObject,
    mut v_m_3404_: *mut crate::leanh::LeanObject,
    mut v_a_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3406_: u8 = 0;
    let mut v_r_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3406_ =
        l_Std_DHashMap_instDecidableMem___redArg(v_inst_3402_, v_inst_3403_, v_m_3404_, v_a_3405_);
    crate::leanh::lean_dec_ref(v_m_3404_);
    v_r_3407_ = crate::leanh::lean_box((v_res_3406_) as usize);
    return v_r_3407_;
}
pub unsafe fn l_Std_DHashMap_instDecidableMem(
    mut v_00_u03b1_3408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3409_: *mut crate::leanh::LeanObject,
    mut v_inst_3410_: *mut crate::leanh::LeanObject,
    mut v_inst_3411_: *mut crate::leanh::LeanObject,
    mut v_m_3412_: *mut crate::leanh::LeanObject,
    mut v_a_3413_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3414_: u8 = 0;
    v___x_3414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_3410_,
        v_inst_3411_,
        v_m_3412_,
        v_a_3413_,
    );
    return v___x_3414_;
}
pub unsafe fn l_Std_DHashMap_instDecidableMem___boxed(
    mut v_00_u03b1_3415_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3416_: *mut crate::leanh::LeanObject,
    mut v_inst_3417_: *mut crate::leanh::LeanObject,
    mut v_inst_3418_: *mut crate::leanh::LeanObject,
    mut v_m_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3421_: u8 = 0;
    let mut v_r_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_Std_DHashMap_instDecidableMem(
        v_00_u03b1_3415_,
        v_00_u03b2_3416_,
        v_inst_3417_,
        v_inst_3418_,
        v_m_3419_,
        v_a_3420_,
    );
    crate::leanh::lean_dec_ref(v_m_3419_);
    v_r_3422_ = crate::leanh::lean_box((v_res_3421_) as usize);
    return v_r_3422_;
}
pub unsafe fn l_Std_DHashMap_get___redArg(
    mut v_x_3423_: *mut crate::leanh::LeanObject,
    mut v_x_3424_: *mut crate::leanh::LeanObject,
    mut v_m_3425_: *mut crate::leanh::LeanObject,
    mut v_a_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3427_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_3423_, v_x_3424_, v_m_3425_, v_a_3426_);
    return v___x_3427_;
}
pub unsafe fn l_Std_DHashMap_get___redArg___boxed(
    mut v_x_3428_: *mut crate::leanh::LeanObject,
    mut v_x_3429_: *mut crate::leanh::LeanObject,
    mut v_m_3430_: *mut crate::leanh::LeanObject,
    mut v_a_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Std_DHashMap_get___redArg(v_x_3428_, v_x_3429_, v_m_3430_, v_a_3431_);
    crate::leanh::lean_dec_ref(v_m_3430_);
    return v_res_3432_;
}
pub unsafe fn l_Std_DHashMap_get(
    mut v_00_u03b1_3433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3434_: *mut crate::leanh::LeanObject,
    mut v_x_3435_: *mut crate::leanh::LeanObject,
    mut v_x_3436_: *mut crate::leanh::LeanObject,
    mut v_inst_3437_: *mut crate::leanh::LeanObject,
    mut v_m_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
    mut v_h_3440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ =
        l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_3435_, v_x_3436_, v_m_3438_, v_a_3439_);
    return v___x_3441_;
}
pub unsafe fn l_Std_DHashMap_get___boxed(
    mut v_00_u03b1_3442_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3443_: *mut crate::leanh::LeanObject,
    mut v_x_3444_: *mut crate::leanh::LeanObject,
    mut v_x_3445_: *mut crate::leanh::LeanObject,
    mut v_inst_3446_: *mut crate::leanh::LeanObject,
    mut v_m_3447_: *mut crate::leanh::LeanObject,
    mut v_a_3448_: *mut crate::leanh::LeanObject,
    mut v_h_3449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3450_ = l_Std_DHashMap_get(
        v_00_u03b1_3442_,
        v_00_u03b2_3443_,
        v_x_3444_,
        v_x_3445_,
        v_inst_3446_,
        v_m_3447_,
        v_a_3448_,
        v_h_3449_,
    );
    crate::leanh::lean_dec_ref(v_m_3447_);
    return v_res_3450_;
}
pub unsafe fn l_Std_DHashMap_get_x21___redArg(
    mut v_x_3451_: *mut crate::leanh::LeanObject,
    mut v_x_3452_: *mut crate::leanh::LeanObject,
    mut v_m_3453_: *mut crate::leanh::LeanObject,
    mut v_a_3454_: *mut crate::leanh::LeanObject,
    mut v_inst_3455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
        v_x_3451_,
        v_x_3452_,
        v_m_3453_,
        v_a_3454_,
        v_inst_3455_,
    );
    return v___x_3456_;
}
pub unsafe fn l_Std_DHashMap_get_x21___redArg___boxed(
    mut v_x_3457_: *mut crate::leanh::LeanObject,
    mut v_x_3458_: *mut crate::leanh::LeanObject,
    mut v_m_3459_: *mut crate::leanh::LeanObject,
    mut v_a_3460_: *mut crate::leanh::LeanObject,
    mut v_inst_3461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ =
        l_Std_DHashMap_get_x21___redArg(v_x_3457_, v_x_3458_, v_m_3459_, v_a_3460_, v_inst_3461_);
    crate::leanh::lean_dec(v_inst_3461_);
    crate::leanh::lean_dec_ref(v_m_3459_);
    return v_res_3462_;
}
pub unsafe fn l_Std_DHashMap_get_x21(
    mut v_00_u03b1_3463_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3464_: *mut crate::leanh::LeanObject,
    mut v_x_3465_: *mut crate::leanh::LeanObject,
    mut v_x_3466_: *mut crate::leanh::LeanObject,
    mut v_inst_3467_: *mut crate::leanh::LeanObject,
    mut v_m_3468_: *mut crate::leanh::LeanObject,
    mut v_a_3469_: *mut crate::leanh::LeanObject,
    mut v_inst_3470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3471_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
        v_x_3465_,
        v_x_3466_,
        v_m_3468_,
        v_a_3469_,
        v_inst_3470_,
    );
    return v___x_3471_;
}
pub unsafe fn l_Std_DHashMap_get_x21___boxed(
    mut v_00_u03b1_3472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3473_: *mut crate::leanh::LeanObject,
    mut v_x_3474_: *mut crate::leanh::LeanObject,
    mut v_x_3475_: *mut crate::leanh::LeanObject,
    mut v_inst_3476_: *mut crate::leanh::LeanObject,
    mut v_m_3477_: *mut crate::leanh::LeanObject,
    mut v_a_3478_: *mut crate::leanh::LeanObject,
    mut v_inst_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Std_DHashMap_get_x21(
        v_00_u03b1_3472_,
        v_00_u03b2_3473_,
        v_x_3474_,
        v_x_3475_,
        v_inst_3476_,
        v_m_3477_,
        v_a_3478_,
        v_inst_3479_,
    );
    crate::leanh::lean_dec(v_inst_3479_);
    crate::leanh::lean_dec_ref(v_m_3477_);
    return v_res_3480_;
}
pub unsafe fn l_Std_DHashMap_getD___redArg(
    mut v_x_3481_: *mut crate::leanh::LeanObject,
    mut v_x_3482_: *mut crate::leanh::LeanObject,
    mut v_m_3483_: *mut crate::leanh::LeanObject,
    mut v_a_3484_: *mut crate::leanh::LeanObject,
    mut v_fallback_3485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
        v_x_3481_,
        v_x_3482_,
        v_m_3483_,
        v_a_3484_,
        v_fallback_3485_,
    );
    return v___x_3486_;
}
pub unsafe fn l_Std_DHashMap_getD___redArg___boxed(
    mut v_x_3487_: *mut crate::leanh::LeanObject,
    mut v_x_3488_: *mut crate::leanh::LeanObject,
    mut v_m_3489_: *mut crate::leanh::LeanObject,
    mut v_a_3490_: *mut crate::leanh::LeanObject,
    mut v_fallback_3491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3492_ =
        l_Std_DHashMap_getD___redArg(v_x_3487_, v_x_3488_, v_m_3489_, v_a_3490_, v_fallback_3491_);
    crate::leanh::lean_dec(v_fallback_3491_);
    crate::leanh::lean_dec_ref(v_m_3489_);
    return v_res_3492_;
}
pub unsafe fn l_Std_DHashMap_getD(
    mut v_00_u03b1_3493_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3494_: *mut crate::leanh::LeanObject,
    mut v_x_3495_: *mut crate::leanh::LeanObject,
    mut v_x_3496_: *mut crate::leanh::LeanObject,
    mut v_inst_3497_: *mut crate::leanh::LeanObject,
    mut v_m_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_fallback_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3501_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
        v_x_3495_,
        v_x_3496_,
        v_m_3498_,
        v_a_3499_,
        v_fallback_3500_,
    );
    return v___x_3501_;
}
pub unsafe fn l_Std_DHashMap_getD___boxed(
    mut v_00_u03b1_3502_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3503_: *mut crate::leanh::LeanObject,
    mut v_x_3504_: *mut crate::leanh::LeanObject,
    mut v_x_3505_: *mut crate::leanh::LeanObject,
    mut v_inst_3506_: *mut crate::leanh::LeanObject,
    mut v_m_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
    mut v_fallback_3509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3510_ = l_Std_DHashMap_getD(
        v_00_u03b1_3502_,
        v_00_u03b2_3503_,
        v_x_3504_,
        v_x_3505_,
        v_inst_3506_,
        v_m_3507_,
        v_a_3508_,
        v_fallback_3509_,
    );
    crate::leanh::lean_dec(v_fallback_3509_);
    crate::leanh::lean_dec_ref(v_m_3507_);
    return v_res_3510_;
}
pub unsafe fn l_Std_DHashMap_erase___redArg(
    mut v_x_3511_: *mut crate::leanh::LeanObject,
    mut v_x_3512_: *mut crate::leanh::LeanObject,
    mut v_m_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_3511_, v_x_3512_, v_m_3513_, v_a_3514_,
    );
    return v___x_3515_;
}
pub unsafe fn l_Std_DHashMap_erase(
    mut v_00_u03b1_3516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3517_: *mut crate::leanh::LeanObject,
    mut v_x_3518_: *mut crate::leanh::LeanObject,
    mut v_x_3519_: *mut crate::leanh::LeanObject,
    mut v_m_3520_: *mut crate::leanh::LeanObject,
    mut v_a_3521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3522_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_3518_, v_x_3519_, v_m_3520_, v_a_3521_,
    );
    return v___x_3522_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x3f___redArg(
    mut v_x_3523_: *mut crate::leanh::LeanObject,
    mut v_x_3524_: *mut crate::leanh::LeanObject,
    mut v_m_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_3523_, v_x_3524_, v_m_3525_, v_a_3526_,
    );
    return v___x_3527_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x3f___redArg___boxed(
    mut v_x_3528_: *mut crate::leanh::LeanObject,
    mut v_x_3529_: *mut crate::leanh::LeanObject,
    mut v_m_3530_: *mut crate::leanh::LeanObject,
    mut v_a_3531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3532_ = l_Std_DHashMap_Const_get_x3f___redArg(v_x_3528_, v_x_3529_, v_m_3530_, v_a_3531_);
    crate::leanh::lean_dec_ref(v_m_3530_);
    return v_res_3532_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x3f(
    mut v_00_u03b1_3533_: *mut crate::leanh::LeanObject,
    mut v_x_3534_: *mut crate::leanh::LeanObject,
    mut v_x_3535_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3536_: *mut crate::leanh::LeanObject,
    mut v_m_3537_: *mut crate::leanh::LeanObject,
    mut v_a_3538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_3534_, v_x_3535_, v_m_3537_, v_a_3538_,
    );
    return v___x_3539_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x3f___boxed(
    mut v_00_u03b1_3540_: *mut crate::leanh::LeanObject,
    mut v_x_3541_: *mut crate::leanh::LeanObject,
    mut v_x_3542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3543_: *mut crate::leanh::LeanObject,
    mut v_m_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3546_ = l_Std_DHashMap_Const_get_x3f(
        v_00_u03b1_3540_,
        v_x_3541_,
        v_x_3542_,
        v_00_u03b2_3543_,
        v_m_3544_,
        v_a_3545_,
    );
    crate::leanh::lean_dec_ref(v_m_3544_);
    return v_res_3546_;
}
pub unsafe fn l_Std_DHashMap_Const_get___redArg(
    mut v_x_3547_: *mut crate::leanh::LeanObject,
    mut v_x_3548_: *mut crate::leanh::LeanObject,
    mut v_m_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_3547_, v_x_3548_, v_m_3549_, v_a_3550_,
    );
    return v___x_3551_;
}
pub unsafe fn l_Std_DHashMap_Const_get___redArg___boxed(
    mut v_x_3552_: *mut crate::leanh::LeanObject,
    mut v_x_3553_: *mut crate::leanh::LeanObject,
    mut v_m_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Std_DHashMap_Const_get___redArg(v_x_3552_, v_x_3553_, v_m_3554_, v_a_3555_);
    crate::leanh::lean_dec_ref(v_m_3554_);
    return v_res_3556_;
}
pub unsafe fn l_Std_DHashMap_Const_get(
    mut v_00_u03b1_3557_: *mut crate::leanh::LeanObject,
    mut v_x_3558_: *mut crate::leanh::LeanObject,
    mut v_x_3559_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3560_: *mut crate::leanh::LeanObject,
    mut v_m_3561_: *mut crate::leanh::LeanObject,
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v_h_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_3558_, v_x_3559_, v_m_3561_, v_a_3562_,
    );
    return v___x_3564_;
}
pub unsafe fn l_Std_DHashMap_Const_get___boxed(
    mut v_00_u03b1_3565_: *mut crate::leanh::LeanObject,
    mut v_x_3566_: *mut crate::leanh::LeanObject,
    mut v_x_3567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3568_: *mut crate::leanh::LeanObject,
    mut v_m_3569_: *mut crate::leanh::LeanObject,
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_h_3571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3572_ = l_Std_DHashMap_Const_get(
        v_00_u03b1_3565_,
        v_x_3566_,
        v_x_3567_,
        v_00_u03b2_3568_,
        v_m_3569_,
        v_a_3570_,
        v_h_3571_,
    );
    crate::leanh::lean_dec_ref(v_m_3569_);
    return v_res_3572_;
}
pub unsafe fn l_Std_DHashMap_Const_getD___redArg(
    mut v_x_3573_: *mut crate::leanh::LeanObject,
    mut v_x_3574_: *mut crate::leanh::LeanObject,
    mut v_m_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_fallback_3577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_3573_,
        v_x_3574_,
        v_m_3575_,
        v_a_3576_,
        v_fallback_3577_,
    );
    return v___x_3578_;
}
pub unsafe fn l_Std_DHashMap_Const_getD___redArg___boxed(
    mut v_x_3579_: *mut crate::leanh::LeanObject,
    mut v_x_3580_: *mut crate::leanh::LeanObject,
    mut v_m_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_fallback_3583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3584_ = l_Std_DHashMap_Const_getD___redArg(
        v_x_3579_,
        v_x_3580_,
        v_m_3581_,
        v_a_3582_,
        v_fallback_3583_,
    );
    crate::leanh::lean_dec(v_fallback_3583_);
    crate::leanh::lean_dec_ref(v_m_3581_);
    return v_res_3584_;
}
pub unsafe fn l_Std_DHashMap_Const_getD(
    mut v_00_u03b1_3585_: *mut crate::leanh::LeanObject,
    mut v_x_3586_: *mut crate::leanh::LeanObject,
    mut v_x_3587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3588_: *mut crate::leanh::LeanObject,
    mut v_m_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v_fallback_3591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_3586_,
        v_x_3587_,
        v_m_3589_,
        v_a_3590_,
        v_fallback_3591_,
    );
    return v___x_3592_;
}
pub unsafe fn l_Std_DHashMap_Const_getD___boxed(
    mut v_00_u03b1_3593_: *mut crate::leanh::LeanObject,
    mut v_x_3594_: *mut crate::leanh::LeanObject,
    mut v_x_3595_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3596_: *mut crate::leanh::LeanObject,
    mut v_m_3597_: *mut crate::leanh::LeanObject,
    mut v_a_3598_: *mut crate::leanh::LeanObject,
    mut v_fallback_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l_Std_DHashMap_Const_getD(
        v_00_u03b1_3593_,
        v_x_3594_,
        v_x_3595_,
        v_00_u03b2_3596_,
        v_m_3597_,
        v_a_3598_,
        v_fallback_3599_,
    );
    crate::leanh::lean_dec(v_fallback_3599_);
    crate::leanh::lean_dec_ref(v_m_3597_);
    return v_res_3600_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x21___redArg(
    mut v_x_3601_: *mut crate::leanh::LeanObject,
    mut v_x_3602_: *mut crate::leanh::LeanObject,
    mut v_inst_3603_: *mut crate::leanh::LeanObject,
    mut v_m_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_3601_,
        v_x_3602_,
        v_inst_3603_,
        v_m_3604_,
        v_a_3605_,
    );
    return v___x_3606_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x21___redArg___boxed(
    mut v_x_3607_: *mut crate::leanh::LeanObject,
    mut v_x_3608_: *mut crate::leanh::LeanObject,
    mut v_inst_3609_: *mut crate::leanh::LeanObject,
    mut v_m_3610_: *mut crate::leanh::LeanObject,
    mut v_a_3611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ = l_Std_DHashMap_Const_get_x21___redArg(
        v_x_3607_,
        v_x_3608_,
        v_inst_3609_,
        v_m_3610_,
        v_a_3611_,
    );
    crate::leanh::lean_dec_ref(v_m_3610_);
    crate::leanh::lean_dec(v_inst_3609_);
    return v_res_3612_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x21(
    mut v_00_u03b1_3613_: *mut crate::leanh::LeanObject,
    mut v_x_3614_: *mut crate::leanh::LeanObject,
    mut v_x_3615_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3616_: *mut crate::leanh::LeanObject,
    mut v_inst_3617_: *mut crate::leanh::LeanObject,
    mut v_m_3618_: *mut crate::leanh::LeanObject,
    mut v_a_3619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_3614_,
        v_x_3615_,
        v_inst_3617_,
        v_m_3618_,
        v_a_3619_,
    );
    return v___x_3620_;
}
pub unsafe fn l_Std_DHashMap_Const_get_x21___boxed(
    mut v_00_u03b1_3621_: *mut crate::leanh::LeanObject,
    mut v_x_3622_: *mut crate::leanh::LeanObject,
    mut v_x_3623_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3624_: *mut crate::leanh::LeanObject,
    mut v_inst_3625_: *mut crate::leanh::LeanObject,
    mut v_m_3626_: *mut crate::leanh::LeanObject,
    mut v_a_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3628_ = l_Std_DHashMap_Const_get_x21(
        v_00_u03b1_3621_,
        v_x_3622_,
        v_x_3623_,
        v_00_u03b2_3624_,
        v_inst_3625_,
        v_m_3626_,
        v_a_3627_,
    );
    crate::leanh::lean_dec_ref(v_m_3626_);
    crate::leanh::lean_dec(v_inst_3625_);
    return v_res_3628_;
}
pub unsafe fn l_Std_DHashMap_Const_getThenInsertIfNew_x3f___redArg(
    mut v_x_3629_: *mut crate::leanh::LeanObject,
    mut v_x_3630_: *mut crate::leanh::LeanObject,
    mut v_m_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_b_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u64 = 0;
    let mut v___x_3639_: u64 = 0;
    let mut v___x_3640_: u64 = 0;
    let mut v___x_3641_: u64 = 0;
    let mut v_fold_3642_: u64 = 0;
    let mut v___x_3643_: u64 = 0;
    let mut v___x_3644_: u64 = 0;
    let mut v___x_3645_: u64 = 0;
    let mut v___x_3646_: usize = 0;
    let mut v___x_3647_: usize = 0;
    let mut v___x_3648_: usize = 0;
    let mut v___x_3649_: usize = 0;
    let mut v___x_3650_: usize = 0;
    let mut v_bkt_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3655_: u8 = 0;
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: u8 = 0;
    let mut v_val_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v_unused_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3634_ = crate::leanh::lean_ctor_get(v_m_3631_, 0);
                v_buckets_3635_ = crate::leanh::lean_ctor_get(v_m_3631_, 1);
                v___x_3636_ = lean_array_get_size(v_buckets_3635_);
                crate::leanh::lean_inc_ref(v_x_3630_);
                crate::leanh::lean_inc_n(v_a_3632_, 2);
                v___x_3637_ = crate::leanh::lean_apply_1(v_x_3630_, v_a_3632_);
                v___x_3638_ = 32u64;
                v___x_3639_ = crate::leanh::lean_unbox_uint64(v___x_3637_);
                v___x_3640_ = lean_uint64_shift_right(v___x_3639_, v___x_3638_);
                v___x_3641_ = crate::leanh::lean_unbox_uint64(v___x_3637_);
                crate::leanh::lean_dec_ref(v___x_3637_);
                v_fold_3642_ = lean_uint64_xor(v___x_3641_, v___x_3640_);
                v___x_3643_ = 16u64;
                v___x_3644_ = lean_uint64_shift_right(v_fold_3642_, v___x_3643_);
                v___x_3645_ = lean_uint64_xor(v_fold_3642_, v___x_3644_);
                v___x_3646_ = lean_uint64_to_usize(v___x_3645_);
                v___x_3647_ = lean_usize_of_nat(v___x_3636_);
                v___x_3648_ = 1usize;
                v___x_3649_ = lean_usize_sub(v___x_3647_, v___x_3648_);
                v___x_3650_ = lean_usize_land(v___x_3646_, v___x_3649_);
                v_bkt_3651_ = lean_array_uget_borrowed(v_buckets_3635_, v___x_3650_);
                crate::leanh::lean_inc(v_bkt_3651_);
                v___x_3652_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_3629_,
                    v_a_3632_,
                    v_bkt_3651_,
                );
                if crate::leanh::lean_obj_tag(v___x_3652_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3635_);
                    crate::leanh::lean_inc(v_size_3634_);
                    v_isSharedCheck_3675_ = (!crate::leanh::lean_is_exclusive(v_m_3631_)) as u8;
                    if v_isSharedCheck_3675_ == 0 {
                        v_unused_3676_ = crate::leanh::lean_ctor_get(v_m_3631_, 1);
                        crate::leanh::lean_dec(v_unused_3676_);
                        v_unused_3677_ = crate::leanh::lean_ctor_get(v_m_3631_, 0);
                        crate::leanh::lean_dec(v_unused_3677_);
                        v___x_3654_ = v_m_3631_;
                        v_isShared_3655_ = v_isSharedCheck_3675_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3631_);
                        v___x_3654_ = crate::leanh::lean_box(0);
                        v_isShared_3655_ = v_isSharedCheck_3675_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3633_);
                    crate::leanh::lean_dec(v_a_3632_);
                    crate::leanh::lean_dec_ref(v_x_3630_);
                    v___x_3678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3678_, 0, v___x_3652_);
                    crate::leanh::lean_ctor_set(v___x_3678_, 1, v_m_3631_);
                    return v___x_3678_;
                }
            }
            1 => {
                v___x_3656_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3657_ = lean_nat_add(v_size_3634_, v___x_3656_);
                crate::leanh::lean_dec(v_size_3634_);
                crate::leanh::lean_inc(v_bkt_3651_);
                v___x_3658_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3658_, 0, v_a_3632_);
                crate::leanh::lean_ctor_set(v___x_3658_, 1, v_b_3633_);
                crate::leanh::lean_ctor_set(v___x_3658_, 2, v_bkt_3651_);
                v_buckets_x27_3659_ = lean_array_uset(v_buckets_3635_, v___x_3650_, v___x_3658_);
                v___x_3660_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3661_ = lean_nat_mul(v_size_x27_3657_, v___x_3660_);
                v___x_3662_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3663_ = lean_nat_div(v___x_3661_, v___x_3662_);
                crate::leanh::lean_dec(v___x_3661_);
                v___x_3664_ = lean_array_get_size(v_buckets_x27_3659_);
                v___x_3665_ = lean_nat_dec_le(v___x_3663_, v___x_3664_);
                crate::leanh::lean_dec(v___x_3663_);
                if v___x_3665_ == 0 {
                    v_val_3666_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_3630_,
                        v_buckets_x27_3659_,
                    );
                    if v_isShared_3655_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3654_, 1, v_val_3666_);
                        crate::leanh::lean_ctor_set(v___x_3654_, 0, v_size_x27_3657_);
                        v___x_3668_ = v___x_3654_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_size_x27_3657_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_val_3666_);
                        v___x_3668_ = v_reuseFailAlloc_3670_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3630_);
                    if v_isShared_3655_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3654_, 1, v_buckets_x27_3659_);
                        crate::leanh::lean_ctor_set(v___x_3654_, 0, v_size_x27_3657_);
                        v___x_3672_ = v___x_3654_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3674_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_size_x27_3657_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_buckets_x27_3659_);
                        v___x_3672_ = v_reuseFailAlloc_3674_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3669_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3669_, 0, v___x_3652_);
                crate::leanh::lean_ctor_set(v___x_3669_, 1, v___x_3668_);
                return v___x_3669_;
            }
            3 => {
                v___x_3673_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3673_, 0, v___x_3652_);
                crate::leanh::lean_ctor_set(v___x_3673_, 1, v___x_3672_);
                return v___x_3673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_3679_: *mut crate::leanh::LeanObject,
    mut v_x_3680_: *mut crate::leanh::LeanObject,
    mut v_x_3681_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3682_: *mut crate::leanh::LeanObject,
    mut v_m_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_b_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u64 = 0;
    let mut v___x_3691_: u64 = 0;
    let mut v___x_3692_: u64 = 0;
    let mut v___x_3693_: u64 = 0;
    let mut v_fold_3694_: u64 = 0;
    let mut v___x_3695_: u64 = 0;
    let mut v___x_3696_: u64 = 0;
    let mut v___x_3697_: u64 = 0;
    let mut v___x_3698_: usize = 0;
    let mut v___x_3699_: usize = 0;
    let mut v___x_3700_: usize = 0;
    let mut v___x_3701_: usize = 0;
    let mut v___x_3702_: usize = 0;
    let mut v_bkt_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3707_: u8 = 0;
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v_val_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3727_: u8 = 0;
    let mut v_unused_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3686_ = crate::leanh::lean_ctor_get(v_m_3683_, 0);
                v_buckets_3687_ = crate::leanh::lean_ctor_get(v_m_3683_, 1);
                v___x_3688_ = lean_array_get_size(v_buckets_3687_);
                crate::leanh::lean_inc_ref(v_x_3681_);
                crate::leanh::lean_inc_n(v_a_3684_, 2);
                v___x_3689_ = crate::leanh::lean_apply_1(v_x_3681_, v_a_3684_);
                v___x_3690_ = 32u64;
                v___x_3691_ = crate::leanh::lean_unbox_uint64(v___x_3689_);
                v___x_3692_ = lean_uint64_shift_right(v___x_3691_, v___x_3690_);
                v___x_3693_ = crate::leanh::lean_unbox_uint64(v___x_3689_);
                crate::leanh::lean_dec_ref(v___x_3689_);
                v_fold_3694_ = lean_uint64_xor(v___x_3693_, v___x_3692_);
                v___x_3695_ = 16u64;
                v___x_3696_ = lean_uint64_shift_right(v_fold_3694_, v___x_3695_);
                v___x_3697_ = lean_uint64_xor(v_fold_3694_, v___x_3696_);
                v___x_3698_ = lean_uint64_to_usize(v___x_3697_);
                v___x_3699_ = lean_usize_of_nat(v___x_3688_);
                v___x_3700_ = 1usize;
                v___x_3701_ = lean_usize_sub(v___x_3699_, v___x_3700_);
                v___x_3702_ = lean_usize_land(v___x_3698_, v___x_3701_);
                v_bkt_3703_ = lean_array_uget_borrowed(v_buckets_3687_, v___x_3702_);
                crate::leanh::lean_inc(v_bkt_3703_);
                v___x_3704_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_3680_,
                    v_a_3684_,
                    v_bkt_3703_,
                );
                if crate::leanh::lean_obj_tag(v___x_3704_) == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3687_);
                    crate::leanh::lean_inc(v_size_3686_);
                    v_isSharedCheck_3727_ = (!crate::leanh::lean_is_exclusive(v_m_3683_)) as u8;
                    if v_isSharedCheck_3727_ == 0 {
                        v_unused_3728_ = crate::leanh::lean_ctor_get(v_m_3683_, 1);
                        crate::leanh::lean_dec(v_unused_3728_);
                        v_unused_3729_ = crate::leanh::lean_ctor_get(v_m_3683_, 0);
                        crate::leanh::lean_dec(v_unused_3729_);
                        v___x_3706_ = v_m_3683_;
                        v_isShared_3707_ = v_isSharedCheck_3727_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3683_);
                        v___x_3706_ = crate::leanh::lean_box(0);
                        v_isShared_3707_ = v_isSharedCheck_3727_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3685_);
                    crate::leanh::lean_dec(v_a_3684_);
                    crate::leanh::lean_dec_ref(v_x_3681_);
                    v___x_3730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3730_, 0, v___x_3704_);
                    crate::leanh::lean_ctor_set(v___x_3730_, 1, v_m_3683_);
                    return v___x_3730_;
                }
            }
            1 => {
                v___x_3708_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3709_ = lean_nat_add(v_size_3686_, v___x_3708_);
                crate::leanh::lean_dec(v_size_3686_);
                crate::leanh::lean_inc(v_bkt_3703_);
                v___x_3710_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3710_, 0, v_a_3684_);
                crate::leanh::lean_ctor_set(v___x_3710_, 1, v_b_3685_);
                crate::leanh::lean_ctor_set(v___x_3710_, 2, v_bkt_3703_);
                v_buckets_x27_3711_ = lean_array_uset(v_buckets_3687_, v___x_3702_, v___x_3710_);
                v___x_3712_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3713_ = lean_nat_mul(v_size_x27_3709_, v___x_3712_);
                v___x_3714_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3715_ = lean_nat_div(v___x_3713_, v___x_3714_);
                crate::leanh::lean_dec(v___x_3713_);
                v___x_3716_ = lean_array_get_size(v_buckets_x27_3711_);
                v___x_3717_ = lean_nat_dec_le(v___x_3715_, v___x_3716_);
                crate::leanh::lean_dec(v___x_3715_);
                if v___x_3717_ == 0 {
                    v_val_3718_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_3681_,
                        v_buckets_x27_3711_,
                    );
                    if v_isShared_3707_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3706_, 1, v_val_3718_);
                        crate::leanh::lean_ctor_set(v___x_3706_, 0, v_size_x27_3709_);
                        v___x_3720_ = v___x_3706_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3722_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_size_x27_3709_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_val_3718_);
                        v___x_3720_ = v_reuseFailAlloc_3722_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3681_);
                    if v_isShared_3707_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3706_, 1, v_buckets_x27_3711_);
                        crate::leanh::lean_ctor_set(v___x_3706_, 0, v_size_x27_3709_);
                        v___x_3724_ = v___x_3706_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_size_x27_3709_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_buckets_x27_3711_);
                        v___x_3724_ = v_reuseFailAlloc_3726_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3721_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3721_, 0, v___x_3704_);
                crate::leanh::lean_ctor_set(v___x_3721_, 1, v___x_3720_);
                return v___x_3721_;
            }
            3 => {
                v___x_3725_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3725_, 0, v___x_3704_);
                crate::leanh::lean_ctor_set(v___x_3725_, 1, v___x_3724_);
                return v___x_3725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_getKey_x3f___redArg(
    mut v_x_3731_: *mut crate::leanh::LeanObject,
    mut v_x_3732_: *mut crate::leanh::LeanObject,
    mut v_m_3733_: *mut crate::leanh::LeanObject,
    mut v_a_3734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_3731_, v_x_3732_, v_m_3733_, v_a_3734_,
    );
    return v___x_3735_;
}
pub unsafe fn l_Std_DHashMap_getKey_x3f___redArg___boxed(
    mut v_x_3736_: *mut crate::leanh::LeanObject,
    mut v_x_3737_: *mut crate::leanh::LeanObject,
    mut v_m_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3740_ = l_Std_DHashMap_getKey_x3f___redArg(v_x_3736_, v_x_3737_, v_m_3738_, v_a_3739_);
    crate::leanh::lean_dec_ref(v_m_3738_);
    return v_res_3740_;
}
pub unsafe fn l_Std_DHashMap_getKey_x3f(
    mut v_00_u03b1_3741_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3742_: *mut crate::leanh::LeanObject,
    mut v_x_3743_: *mut crate::leanh::LeanObject,
    mut v_x_3744_: *mut crate::leanh::LeanObject,
    mut v_m_3745_: *mut crate::leanh::LeanObject,
    mut v_a_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3747_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_3743_, v_x_3744_, v_m_3745_, v_a_3746_,
    );
    return v___x_3747_;
}
pub unsafe fn l_Std_DHashMap_getKey_x3f___boxed(
    mut v_00_u03b1_3748_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3749_: *mut crate::leanh::LeanObject,
    mut v_x_3750_: *mut crate::leanh::LeanObject,
    mut v_x_3751_: *mut crate::leanh::LeanObject,
    mut v_m_3752_: *mut crate::leanh::LeanObject,
    mut v_a_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l_Std_DHashMap_getKey_x3f(
        v_00_u03b1_3748_,
        v_00_u03b2_3749_,
        v_x_3750_,
        v_x_3751_,
        v_m_3752_,
        v_a_3753_,
    );
    crate::leanh::lean_dec_ref(v_m_3752_);
    return v_res_3754_;
}
pub unsafe fn l_Std_DHashMap_getKey___redArg(
    mut v_x_3755_: *mut crate::leanh::LeanObject,
    mut v_x_3756_: *mut crate::leanh::LeanObject,
    mut v_m_3757_: *mut crate::leanh::LeanObject,
    mut v_a_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3759_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_3755_, v_x_3756_, v_m_3757_, v_a_3758_,
    );
    return v___x_3759_;
}
pub unsafe fn l_Std_DHashMap_getKey___redArg___boxed(
    mut v_x_3760_: *mut crate::leanh::LeanObject,
    mut v_x_3761_: *mut crate::leanh::LeanObject,
    mut v_m_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3764_ = l_Std_DHashMap_getKey___redArg(v_x_3760_, v_x_3761_, v_m_3762_, v_a_3763_);
    crate::leanh::lean_dec_ref(v_m_3762_);
    return v_res_3764_;
}
pub unsafe fn l_Std_DHashMap_getKey(
    mut v_00_u03b1_3765_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3766_: *mut crate::leanh::LeanObject,
    mut v_x_3767_: *mut crate::leanh::LeanObject,
    mut v_x_3768_: *mut crate::leanh::LeanObject,
    mut v_m_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
    mut v_h_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3772_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_3767_, v_x_3768_, v_m_3769_, v_a_3770_,
    );
    return v___x_3772_;
}
pub unsafe fn l_Std_DHashMap_getKey___boxed(
    mut v_00_u03b1_3773_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3774_: *mut crate::leanh::LeanObject,
    mut v_x_3775_: *mut crate::leanh::LeanObject,
    mut v_x_3776_: *mut crate::leanh::LeanObject,
    mut v_m_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_h_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l_Std_DHashMap_getKey(
        v_00_u03b1_3773_,
        v_00_u03b2_3774_,
        v_x_3775_,
        v_x_3776_,
        v_m_3777_,
        v_a_3778_,
        v_h_3779_,
    );
    crate::leanh::lean_dec_ref(v_m_3777_);
    return v_res_3780_;
}
pub unsafe fn l_Std_DHashMap_getKey_x21___redArg(
    mut v_x_3781_: *mut crate::leanh::LeanObject,
    mut v_x_3782_: *mut crate::leanh::LeanObject,
    mut v_inst_3783_: *mut crate::leanh::LeanObject,
    mut v_m_3784_: *mut crate::leanh::LeanObject,
    mut v_a_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3786_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_3781_,
        v_x_3782_,
        v_inst_3783_,
        v_m_3784_,
        v_a_3785_,
    );
    return v___x_3786_;
}
pub unsafe fn l_Std_DHashMap_getKey_x21___redArg___boxed(
    mut v_x_3787_: *mut crate::leanh::LeanObject,
    mut v_x_3788_: *mut crate::leanh::LeanObject,
    mut v_inst_3789_: *mut crate::leanh::LeanObject,
    mut v_m_3790_: *mut crate::leanh::LeanObject,
    mut v_a_3791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Std_DHashMap_getKey_x21___redArg(
        v_x_3787_,
        v_x_3788_,
        v_inst_3789_,
        v_m_3790_,
        v_a_3791_,
    );
    crate::leanh::lean_dec_ref(v_m_3790_);
    crate::leanh::lean_dec(v_inst_3789_);
    return v_res_3792_;
}
pub unsafe fn l_Std_DHashMap_getKey_x21(
    mut v_00_u03b1_3793_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3794_: *mut crate::leanh::LeanObject,
    mut v_x_3795_: *mut crate::leanh::LeanObject,
    mut v_x_3796_: *mut crate::leanh::LeanObject,
    mut v_inst_3797_: *mut crate::leanh::LeanObject,
    mut v_m_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_3795_,
        v_x_3796_,
        v_inst_3797_,
        v_m_3798_,
        v_a_3799_,
    );
    return v___x_3800_;
}
pub unsafe fn l_Std_DHashMap_getKey_x21___boxed(
    mut v_00_u03b1_3801_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3802_: *mut crate::leanh::LeanObject,
    mut v_x_3803_: *mut crate::leanh::LeanObject,
    mut v_x_3804_: *mut crate::leanh::LeanObject,
    mut v_inst_3805_: *mut crate::leanh::LeanObject,
    mut v_m_3806_: *mut crate::leanh::LeanObject,
    mut v_a_3807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3808_ = l_Std_DHashMap_getKey_x21(
        v_00_u03b1_3801_,
        v_00_u03b2_3802_,
        v_x_3803_,
        v_x_3804_,
        v_inst_3805_,
        v_m_3806_,
        v_a_3807_,
    );
    crate::leanh::lean_dec_ref(v_m_3806_);
    crate::leanh::lean_dec(v_inst_3805_);
    return v_res_3808_;
}
pub unsafe fn l_Std_DHashMap_getKeyD___redArg(
    mut v_x_3809_: *mut crate::leanh::LeanObject,
    mut v_x_3810_: *mut crate::leanh::LeanObject,
    mut v_m_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_fallback_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_3809_,
        v_x_3810_,
        v_m_3811_,
        v_a_3812_,
        v_fallback_3813_,
    );
    return v___x_3814_;
}
pub unsafe fn l_Std_DHashMap_getKeyD___redArg___boxed(
    mut v_x_3815_: *mut crate::leanh::LeanObject,
    mut v_x_3816_: *mut crate::leanh::LeanObject,
    mut v_m_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
    mut v_fallback_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3820_ = l_Std_DHashMap_getKeyD___redArg(
        v_x_3815_,
        v_x_3816_,
        v_m_3817_,
        v_a_3818_,
        v_fallback_3819_,
    );
    crate::leanh::lean_dec(v_fallback_3819_);
    crate::leanh::lean_dec_ref(v_m_3817_);
    return v_res_3820_;
}
pub unsafe fn l_Std_DHashMap_getKeyD(
    mut v_00_u03b1_3821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3822_: *mut crate::leanh::LeanObject,
    mut v_x_3823_: *mut crate::leanh::LeanObject,
    mut v_x_3824_: *mut crate::leanh::LeanObject,
    mut v_m_3825_: *mut crate::leanh::LeanObject,
    mut v_a_3826_: *mut crate::leanh::LeanObject,
    mut v_fallback_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_3823_,
        v_x_3824_,
        v_m_3825_,
        v_a_3826_,
        v_fallback_3827_,
    );
    return v___x_3828_;
}
pub unsafe fn l_Std_DHashMap_getKeyD___boxed(
    mut v_00_u03b1_3829_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3830_: *mut crate::leanh::LeanObject,
    mut v_x_3831_: *mut crate::leanh::LeanObject,
    mut v_x_3832_: *mut crate::leanh::LeanObject,
    mut v_m_3833_: *mut crate::leanh::LeanObject,
    mut v_a_3834_: *mut crate::leanh::LeanObject,
    mut v_fallback_3835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3836_ = l_Std_DHashMap_getKeyD(
        v_00_u03b1_3829_,
        v_00_u03b2_3830_,
        v_x_3831_,
        v_x_3832_,
        v_m_3833_,
        v_a_3834_,
        v_fallback_3835_,
    );
    crate::leanh::lean_dec(v_fallback_3835_);
    crate::leanh::lean_dec_ref(v_m_3833_);
    return v_res_3836_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x3f___redArg(
    mut v_x_3837_: *mut crate::leanh::LeanObject,
    mut v_x_3838_: *mut crate::leanh::LeanObject,
    mut v_m_3839_: *mut crate::leanh::LeanObject,
    mut v_a_3840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
        v_x_3837_, v_x_3838_, v_m_3839_, v_a_3840_,
    );
    return v___x_3841_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x3f___redArg___boxed(
    mut v_x_3842_: *mut crate::leanh::LeanObject,
    mut v_x_3843_: *mut crate::leanh::LeanObject,
    mut v_m_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3846_ = l_Std_DHashMap_getEntry_x3f___redArg(v_x_3842_, v_x_3843_, v_m_3844_, v_a_3845_);
    crate::leanh::lean_dec_ref(v_m_3844_);
    return v_res_3846_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x3f(
    mut v_00_u03b1_3847_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3848_: *mut crate::leanh::LeanObject,
    mut v_x_3849_: *mut crate::leanh::LeanObject,
    mut v_x_3850_: *mut crate::leanh::LeanObject,
    mut v_m_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
        v_x_3849_, v_x_3850_, v_m_3851_, v_a_3852_,
    );
    return v___x_3853_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x3f___boxed(
    mut v_00_u03b1_3854_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3855_: *mut crate::leanh::LeanObject,
    mut v_x_3856_: *mut crate::leanh::LeanObject,
    mut v_x_3857_: *mut crate::leanh::LeanObject,
    mut v_m_3858_: *mut crate::leanh::LeanObject,
    mut v_a_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3860_ = l_Std_DHashMap_getEntry_x3f(
        v_00_u03b1_3854_,
        v_00_u03b2_3855_,
        v_x_3856_,
        v_x_3857_,
        v_m_3858_,
        v_a_3859_,
    );
    crate::leanh::lean_dec_ref(v_m_3858_);
    return v_res_3860_;
}
pub unsafe fn l_Std_DHashMap_getEntry___redArg(
    mut v_x_3861_: *mut crate::leanh::LeanObject,
    mut v_x_3862_: *mut crate::leanh::LeanObject,
    mut v_m_3863_: *mut crate::leanh::LeanObject,
    mut v_a_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3865_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_x_3861_, v_x_3862_, v_m_3863_, v_a_3864_,
    );
    return v___x_3865_;
}
pub unsafe fn l_Std_DHashMap_getEntry___redArg___boxed(
    mut v_x_3866_: *mut crate::leanh::LeanObject,
    mut v_x_3867_: *mut crate::leanh::LeanObject,
    mut v_m_3868_: *mut crate::leanh::LeanObject,
    mut v_a_3869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3870_ = l_Std_DHashMap_getEntry___redArg(v_x_3866_, v_x_3867_, v_m_3868_, v_a_3869_);
    crate::leanh::lean_dec_ref(v_m_3868_);
    return v_res_3870_;
}
pub unsafe fn l_Std_DHashMap_getEntry(
    mut v_00_u03b1_3871_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3872_: *mut crate::leanh::LeanObject,
    mut v_x_3873_: *mut crate::leanh::LeanObject,
    mut v_x_3874_: *mut crate::leanh::LeanObject,
    mut v_m_3875_: *mut crate::leanh::LeanObject,
    mut v_a_3876_: *mut crate::leanh::LeanObject,
    mut v_h_3877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_x_3873_, v_x_3874_, v_m_3875_, v_a_3876_,
    );
    return v___x_3878_;
}
pub unsafe fn l_Std_DHashMap_getEntry___boxed(
    mut v_00_u03b1_3879_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3880_: *mut crate::leanh::LeanObject,
    mut v_x_3881_: *mut crate::leanh::LeanObject,
    mut v_x_3882_: *mut crate::leanh::LeanObject,
    mut v_m_3883_: *mut crate::leanh::LeanObject,
    mut v_a_3884_: *mut crate::leanh::LeanObject,
    mut v_h_3885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3886_ = l_Std_DHashMap_getEntry(
        v_00_u03b1_3879_,
        v_00_u03b2_3880_,
        v_x_3881_,
        v_x_3882_,
        v_m_3883_,
        v_a_3884_,
        v_h_3885_,
    );
    crate::leanh::lean_dec_ref(v_m_3883_);
    return v_res_3886_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x21___redArg(
    mut v_x_3887_: *mut crate::leanh::LeanObject,
    mut v_x_3888_: *mut crate::leanh::LeanObject,
    mut v_inst_3889_: *mut crate::leanh::LeanObject,
    mut v_m_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3892_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(
        v_x_3887_,
        v_x_3888_,
        v_m_3890_,
        v_a_3891_,
        v_inst_3889_,
    );
    return v___x_3892_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x21___redArg___boxed(
    mut v_x_3893_: *mut crate::leanh::LeanObject,
    mut v_x_3894_: *mut crate::leanh::LeanObject,
    mut v_inst_3895_: *mut crate::leanh::LeanObject,
    mut v_m_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3898_ = l_Std_DHashMap_getEntry_x21___redArg(
        v_x_3893_,
        v_x_3894_,
        v_inst_3895_,
        v_m_3896_,
        v_a_3897_,
    );
    crate::leanh::lean_dec_ref(v_m_3896_);
    crate::leanh::lean_dec_ref(v_inst_3895_);
    return v_res_3898_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x21(
    mut v_00_u03b1_3899_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3900_: *mut crate::leanh::LeanObject,
    mut v_x_3901_: *mut crate::leanh::LeanObject,
    mut v_x_3902_: *mut crate::leanh::LeanObject,
    mut v_inst_3903_: *mut crate::leanh::LeanObject,
    mut v_m_3904_: *mut crate::leanh::LeanObject,
    mut v_a_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3906_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(
        v_x_3901_,
        v_x_3902_,
        v_m_3904_,
        v_a_3905_,
        v_inst_3903_,
    );
    return v___x_3906_;
}
pub unsafe fn l_Std_DHashMap_getEntry_x21___boxed(
    mut v_00_u03b1_3907_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3908_: *mut crate::leanh::LeanObject,
    mut v_x_3909_: *mut crate::leanh::LeanObject,
    mut v_x_3910_: *mut crate::leanh::LeanObject,
    mut v_inst_3911_: *mut crate::leanh::LeanObject,
    mut v_m_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3914_ = l_Std_DHashMap_getEntry_x21(
        v_00_u03b1_3907_,
        v_00_u03b2_3908_,
        v_x_3909_,
        v_x_3910_,
        v_inst_3911_,
        v_m_3912_,
        v_a_3913_,
    );
    crate::leanh::lean_dec_ref(v_m_3912_);
    crate::leanh::lean_dec_ref(v_inst_3911_);
    return v_res_3914_;
}
pub unsafe fn l_Std_DHashMap_getEntryD___redArg(
    mut v_x_3915_: *mut crate::leanh::LeanObject,
    mut v_x_3916_: *mut crate::leanh::LeanObject,
    mut v_m_3917_: *mut crate::leanh::LeanObject,
    mut v_a_3918_: *mut crate::leanh::LeanObject,
    mut v_fallback_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3920_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(
        v_x_3915_,
        v_x_3916_,
        v_m_3917_,
        v_a_3918_,
        v_fallback_3919_,
    );
    return v___x_3920_;
}
pub unsafe fn l_Std_DHashMap_getEntryD___redArg___boxed(
    mut v_x_3921_: *mut crate::leanh::LeanObject,
    mut v_x_3922_: *mut crate::leanh::LeanObject,
    mut v_m_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_fallback_3925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Std_DHashMap_getEntryD___redArg(
        v_x_3921_,
        v_x_3922_,
        v_m_3923_,
        v_a_3924_,
        v_fallback_3925_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3925_);
    crate::leanh::lean_dec_ref(v_m_3923_);
    return v_res_3926_;
}
pub unsafe fn l_Std_DHashMap_getEntryD(
    mut v_00_u03b1_3927_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3928_: *mut crate::leanh::LeanObject,
    mut v_x_3929_: *mut crate::leanh::LeanObject,
    mut v_x_3930_: *mut crate::leanh::LeanObject,
    mut v_m_3931_: *mut crate::leanh::LeanObject,
    mut v_a_3932_: *mut crate::leanh::LeanObject,
    mut v_fallback_3933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3934_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(
        v_x_3929_,
        v_x_3930_,
        v_m_3931_,
        v_a_3932_,
        v_fallback_3933_,
    );
    return v___x_3934_;
}
pub unsafe fn l_Std_DHashMap_getEntryD___boxed(
    mut v_00_u03b1_3935_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3936_: *mut crate::leanh::LeanObject,
    mut v_x_3937_: *mut crate::leanh::LeanObject,
    mut v_x_3938_: *mut crate::leanh::LeanObject,
    mut v_m_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_fallback_3941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Std_DHashMap_getEntryD(
        v_00_u03b1_3935_,
        v_00_u03b2_3936_,
        v_x_3937_,
        v_x_3938_,
        v_m_3939_,
        v_a_3940_,
        v_fallback_3941_,
    );
    crate::leanh::lean_dec_ref(v_fallback_3941_);
    crate::leanh::lean_dec_ref(v_m_3939_);
    return v_res_3942_;
}
pub unsafe fn l_Std_DHashMap_size___redArg(
    mut v_m_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_3944_ = crate::leanh::lean_ctor_get(v_m_3943_, 0);
    crate::leanh::lean_inc(v_size_3944_);
    return v_size_3944_;
}
pub unsafe fn l_Std_DHashMap_size___redArg___boxed(
    mut v_m_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3946_ = l_Std_DHashMap_size___redArg(v_m_3945_);
    crate::leanh::lean_dec_ref(v_m_3945_);
    return v_res_3946_;
}
pub unsafe fn l_Std_DHashMap_size(
    mut v_00_u03b1_3947_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3948_: *mut crate::leanh::LeanObject,
    mut v_x_3949_: *mut crate::leanh::LeanObject,
    mut v_x_3950_: *mut crate::leanh::LeanObject,
    mut v_m_3951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_3952_ = crate::leanh::lean_ctor_get(v_m_3951_, 0);
    crate::leanh::lean_inc(v_size_3952_);
    return v_size_3952_;
}
pub unsafe fn l_Std_DHashMap_size___boxed(
    mut v_00_u03b1_3953_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3954_: *mut crate::leanh::LeanObject,
    mut v_x_3955_: *mut crate::leanh::LeanObject,
    mut v_x_3956_: *mut crate::leanh::LeanObject,
    mut v_m_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3958_ = l_Std_DHashMap_size(
        v_00_u03b1_3953_,
        v_00_u03b2_3954_,
        v_x_3955_,
        v_x_3956_,
        v_m_3957_,
    );
    crate::leanh::lean_dec_ref(v_m_3957_);
    crate::leanh::lean_dec_ref(v_x_3956_);
    crate::leanh::lean_dec_ref(v_x_3955_);
    return v_res_3958_;
}
pub unsafe fn l_Std_DHashMap_isEmpty___redArg(mut v_m_3959_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_size_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    v_size_3960_ = crate::leanh::lean_ctor_get(v_m_3959_, 0);
    v___x_3961_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3962_ = lean_nat_dec_eq(v_size_3960_, v___x_3961_);
    return v___x_3962_;
}
pub unsafe fn l_Std_DHashMap_isEmpty___redArg___boxed(
    mut v_m_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3964_: u8 = 0;
    let mut v_r_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Std_DHashMap_isEmpty___redArg(v_m_3963_);
    crate::leanh::lean_dec_ref(v_m_3963_);
    v_r_3965_ = crate::leanh::lean_box((v_res_3964_) as usize);
    return v_r_3965_;
}
pub unsafe fn l_Std_DHashMap_isEmpty(
    mut v_00_u03b1_3966_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3967_: *mut crate::leanh::LeanObject,
    mut v_x_3968_: *mut crate::leanh::LeanObject,
    mut v_x_3969_: *mut crate::leanh::LeanObject,
    mut v_m_3970_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: u8 = 0;
    v_size_3971_ = crate::leanh::lean_ctor_get(v_m_3970_, 0);
    v___x_3972_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3973_ = lean_nat_dec_eq(v_size_3971_, v___x_3972_);
    return v___x_3973_;
}
pub unsafe fn l_Std_DHashMap_isEmpty___boxed(
    mut v_00_u03b1_3974_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3975_: *mut crate::leanh::LeanObject,
    mut v_x_3976_: *mut crate::leanh::LeanObject,
    mut v_x_3977_: *mut crate::leanh::LeanObject,
    mut v_m_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3979_: u8 = 0;
    let mut v_r_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Std_DHashMap_isEmpty(
        v_00_u03b1_3974_,
        v_00_u03b2_3975_,
        v_x_3976_,
        v_x_3977_,
        v_m_3978_,
    );
    crate::leanh::lean_dec_ref(v_m_3978_);
    crate::leanh::lean_dec_ref(v_x_3977_);
    crate::leanh::lean_dec_ref(v_x_3976_);
    v_r_3980_ = crate::leanh::lean_box((v_res_3979_) as usize);
    return v_r_3980_;
}
pub unsafe fn l_Std_DHashMap_keys___redArg___lam__0(
    mut v_a_3981_: *mut crate::leanh::LeanObject,
    mut v_b_3982_: *mut crate::leanh::LeanObject,
    mut v_d_3983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3984_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3984_, 0, v_a_3981_);
    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_d_3983_);
    return v___x_3984_;
}
pub unsafe fn l_Std_DHashMap_keys___redArg___lam__0___boxed(
    mut v_a_3985_: *mut crate::leanh::LeanObject,
    mut v_b_3986_: *mut crate::leanh::LeanObject,
    mut v_d_3987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3988_ = l_Std_DHashMap_keys___redArg___lam__0(v_a_3985_, v_b_3986_, v_d_3987_);
    crate::leanh::lean_dec(v_b_3986_);
    return v_res_3988_;
}
pub unsafe fn l_Std_DHashMap_keys___redArg___lam__1(
    mut v___x_3989_: *mut crate::leanh::LeanObject,
    mut v___f_3990_: *mut crate::leanh::LeanObject,
    mut v_l_3991_: *mut crate::leanh::LeanObject,
    mut v_acc_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3993_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_3989_,
        v___f_3990_,
        v_acc_3992_,
        v_l_3991_,
    );
    return v___x_3993_;
}
pub unsafe fn l_Std_DHashMap_keys___redArg(
    mut v_m_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: u8 = 0;
    v___x_4018_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4019_ = crate::leanh::lean_ctor_get(v_m_4017_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4019_);
    crate::leanh::lean_dec_ref(v_m_4017_);
    v___x_4020_ = crate::leanh::lean_box(0);
    v___x_4021_ = lean_array_get_size(v_buckets_4019_);
    v___x_4022_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4023_ = lean_nat_dec_lt(v___x_4022_, v___x_4021_);
    if v___x_4023_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4019_);
        return v___x_4020_;
    } else {
        let mut v___f_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4025_: usize = 0;
        let mut v___x_4026_: usize = 0;
        let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4024_ = l_Std_DHashMap_keys___redArg___closed__11;
        v___x_4025_ = lean_usize_of_nat(v___x_4021_);
        v___x_4026_ = 0usize;
        v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4018_,
            v___f_4024_,
            v_buckets_4019_,
            v___x_4025_,
            v___x_4026_,
            v___x_4020_,
        );
        return v___x_4027_;
    }
}
pub unsafe fn l_Std_DHashMap_keys(
    mut v_00_u03b1_4028_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4029_: *mut crate::leanh::LeanObject,
    mut v_x_4030_: *mut crate::leanh::LeanObject,
    mut v_x_4031_: *mut crate::leanh::LeanObject,
    mut v_m_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: u8 = 0;
    v___x_4033_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4034_ = crate::leanh::lean_ctor_get(v_m_4032_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4034_);
    crate::leanh::lean_dec_ref(v_m_4032_);
    v___x_4035_ = crate::leanh::lean_box(0);
    v___x_4036_ = lean_array_get_size(v_buckets_4034_);
    v___x_4037_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4038_ = lean_nat_dec_lt(v___x_4037_, v___x_4036_);
    if v___x_4038_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4034_);
        return v___x_4035_;
    } else {
        let mut v___f_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4040_: usize = 0;
        let mut v___x_4041_: usize = 0;
        let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4039_ = l_Std_DHashMap_keys___redArg___closed__11;
        v___x_4040_ = lean_usize_of_nat(v___x_4036_);
        v___x_4041_ = 0usize;
        v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4033_,
            v___f_4039_,
            v_buckets_4034_,
            v___x_4040_,
            v___x_4041_,
            v___x_4035_,
        );
        return v___x_4042_;
    }
}
pub unsafe fn l_Std_DHashMap_keys___boxed(
    mut v_00_u03b1_4043_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4044_: *mut crate::leanh::LeanObject,
    mut v_x_4045_: *mut crate::leanh::LeanObject,
    mut v_x_4046_: *mut crate::leanh::LeanObject,
    mut v_m_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4048_ = l_Std_DHashMap_keys(
        v_00_u03b1_4043_,
        v_00_u03b2_4044_,
        v_x_4045_,
        v_x_4046_,
        v_m_4047_,
    );
    crate::leanh::lean_dec_ref(v_x_4046_);
    crate::leanh::lean_dec_ref(v_x_4045_);
    return v_res_4048_;
}
pub unsafe fn l_Std_DHashMap_toList___redArg___lam__0(
    mut v_a_4049_: *mut crate::leanh::LeanObject,
    mut v_b_4050_: *mut crate::leanh::LeanObject,
    mut v_d_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4052_, 0, v_a_4049_);
    crate::leanh::lean_ctor_set(v___x_4052_, 1, v_b_4050_);
    v___x_4053_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4053_, 0, v___x_4052_);
    crate::leanh::lean_ctor_set(v___x_4053_, 1, v_d_4051_);
    return v___x_4053_;
}
pub unsafe fn l_Std_DHashMap_toList___redArg___lam__1(
    mut v___x_4054_: *mut crate::leanh::LeanObject,
    mut v___f_4055_: *mut crate::leanh::LeanObject,
    mut v_l_4056_: *mut crate::leanh::LeanObject,
    mut v_acc_4057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4058_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_4054_,
        v___f_4055_,
        v_acc_4057_,
        v_l_4056_,
    );
    return v___x_4058_;
}
pub unsafe fn l_Std_DHashMap_toList___redArg(
    mut v_m_4063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    v___x_4064_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4065_ = crate::leanh::lean_ctor_get(v_m_4063_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4065_);
    crate::leanh::lean_dec_ref(v_m_4063_);
    v___x_4066_ = crate::leanh::lean_box(0);
    v___x_4067_ = lean_array_get_size(v_buckets_4065_);
    v___x_4068_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4069_ = lean_nat_dec_lt(v___x_4068_, v___x_4067_);
    if v___x_4069_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4065_);
        return v___x_4066_;
    } else {
        let mut v___f_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: usize = 0;
        let mut v___x_4072_: usize = 0;
        let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4070_ = l_Std_DHashMap_toList___redArg___closed__1;
        v___x_4071_ = lean_usize_of_nat(v___x_4067_);
        v___x_4072_ = 0usize;
        v___x_4073_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4064_,
            v___f_4070_,
            v_buckets_4065_,
            v___x_4071_,
            v___x_4072_,
            v___x_4066_,
        );
        return v___x_4073_;
    }
}
pub unsafe fn l_Std_DHashMap_toList(
    mut v_00_u03b1_4074_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4075_: *mut crate::leanh::LeanObject,
    mut v_x_4076_: *mut crate::leanh::LeanObject,
    mut v_x_4077_: *mut crate::leanh::LeanObject,
    mut v_m_4078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    v___x_4079_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4080_ = crate::leanh::lean_ctor_get(v_m_4078_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4080_);
    crate::leanh::lean_dec_ref(v_m_4078_);
    v___x_4081_ = crate::leanh::lean_box(0);
    v___x_4082_ = lean_array_get_size(v_buckets_4080_);
    v___x_4083_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4084_ = lean_nat_dec_lt(v___x_4083_, v___x_4082_);
    if v___x_4084_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4080_);
        return v___x_4081_;
    } else {
        let mut v___f_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4086_: usize = 0;
        let mut v___x_4087_: usize = 0;
        let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4085_ = l_Std_DHashMap_toList___redArg___closed__1;
        v___x_4086_ = lean_usize_of_nat(v___x_4082_);
        v___x_4087_ = 0usize;
        v___x_4088_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4079_,
            v___f_4085_,
            v_buckets_4080_,
            v___x_4086_,
            v___x_4087_,
            v___x_4081_,
        );
        return v___x_4088_;
    }
}
pub unsafe fn l_Std_DHashMap_toList___boxed(
    mut v_00_u03b1_4089_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4090_: *mut crate::leanh::LeanObject,
    mut v_x_4091_: *mut crate::leanh::LeanObject,
    mut v_x_4092_: *mut crate::leanh::LeanObject,
    mut v_m_4093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4094_ = l_Std_DHashMap_toList(
        v_00_u03b1_4089_,
        v_00_u03b2_4090_,
        v_x_4091_,
        v_x_4092_,
        v_m_4093_,
    );
    crate::leanh::lean_dec_ref(v_x_4092_);
    crate::leanh::lean_dec_ref(v_x_4091_);
    return v_res_4094_;
}
pub unsafe fn l_Std_DHashMap_Const_toList___redArg___lam__0(
    mut v_a_4095_: *mut crate::leanh::LeanObject,
    mut v_b_4096_: *mut crate::leanh::LeanObject,
    mut v_d_4097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4098_, 0, v_a_4095_);
    crate::leanh::lean_ctor_set(v___x_4098_, 1, v_b_4096_);
    v___x_4099_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4099_, 0, v___x_4098_);
    crate::leanh::lean_ctor_set(v___x_4099_, 1, v_d_4097_);
    return v___x_4099_;
}
pub unsafe fn l_Std_DHashMap_Const_toList___redArg___lam__1(
    mut v___x_4100_: *mut crate::leanh::LeanObject,
    mut v___f_4101_: *mut crate::leanh::LeanObject,
    mut v_l_4102_: *mut crate::leanh::LeanObject,
    mut v_acc_4103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4104_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_4100_,
        v___f_4101_,
        v_acc_4103_,
        v_l_4102_,
    );
    return v___x_4104_;
}
pub unsafe fn l_Std_DHashMap_Const_toList___redArg(
    mut v_m_4109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: u8 = 0;
    v___x_4110_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4111_ = crate::leanh::lean_ctor_get(v_m_4109_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4111_);
    crate::leanh::lean_dec_ref(v_m_4109_);
    v___x_4112_ = crate::leanh::lean_box(0);
    v___x_4113_ = lean_array_get_size(v_buckets_4111_);
    v___x_4114_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4115_ = lean_nat_dec_lt(v___x_4114_, v___x_4113_);
    if v___x_4115_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4111_);
        return v___x_4112_;
    } else {
        let mut v___f_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4117_: usize = 0;
        let mut v___x_4118_: usize = 0;
        let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4116_ = l_Std_DHashMap_Const_toList___redArg___closed__1;
        v___x_4117_ = lean_usize_of_nat(v___x_4113_);
        v___x_4118_ = 0usize;
        v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4110_,
            v___f_4116_,
            v_buckets_4111_,
            v___x_4117_,
            v___x_4118_,
            v___x_4112_,
        );
        return v___x_4119_;
    }
}
pub unsafe fn l_Std_DHashMap_Const_toList(
    mut v_00_u03b1_4120_: *mut crate::leanh::LeanObject,
    mut v_x_4121_: *mut crate::leanh::LeanObject,
    mut v_x_4122_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4123_: *mut crate::leanh::LeanObject,
    mut v_m_4124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: u8 = 0;
    v___x_4125_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4126_ = crate::leanh::lean_ctor_get(v_m_4124_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4126_);
    crate::leanh::lean_dec_ref(v_m_4124_);
    v___x_4127_ = crate::leanh::lean_box(0);
    v___x_4128_ = lean_array_get_size(v_buckets_4126_);
    v___x_4129_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4130_ = lean_nat_dec_lt(v___x_4129_, v___x_4128_);
    if v___x_4130_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4126_);
        return v___x_4127_;
    } else {
        let mut v___f_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4132_: usize = 0;
        let mut v___x_4133_: usize = 0;
        let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4131_ = l_Std_DHashMap_Const_toList___redArg___closed__1;
        v___x_4132_ = lean_usize_of_nat(v___x_4128_);
        v___x_4133_ = 0usize;
        v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4125_,
            v___f_4131_,
            v_buckets_4126_,
            v___x_4132_,
            v___x_4133_,
            v___x_4127_,
        );
        return v___x_4134_;
    }
}
pub unsafe fn l_Std_DHashMap_Const_toList___boxed(
    mut v_00_u03b1_4135_: *mut crate::leanh::LeanObject,
    mut v_x_4136_: *mut crate::leanh::LeanObject,
    mut v_x_4137_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4138_: *mut crate::leanh::LeanObject,
    mut v_m_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4140_ = l_Std_DHashMap_Const_toList(
        v_00_u03b1_4135_,
        v_x_4136_,
        v_x_4137_,
        v_00_u03b2_4138_,
        v_m_4139_,
    );
    crate::leanh::lean_dec_ref(v_x_4137_);
    crate::leanh::lean_dec_ref(v_x_4136_);
    return v_res_4140_;
}
pub unsafe fn l_Std_DHashMap_foldM___redArg___lam__0(
    mut v_inst_4141_: *mut crate::leanh::LeanObject,
    mut v_f_4142_: *mut crate::leanh::LeanObject,
    mut v_acc_4143_: *mut crate::leanh::LeanObject,
    mut v_l_4144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4145_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_4141_,
        v_f_4142_,
        v_acc_4143_,
        v_l_4144_,
    );
    return v___x_4145_;
}
pub unsafe fn l_Std_DHashMap_foldM___redArg(
    mut v_inst_4146_: *mut crate::leanh::LeanObject,
    mut v_f_4147_: *mut crate::leanh::LeanObject,
    mut v_init_4148_: *mut crate::leanh::LeanObject,
    mut v_b_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: u8 = 0;
    v_buckets_4150_ = crate::leanh::lean_ctor_get(v_b_4149_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4150_);
    crate::leanh::lean_dec_ref(v_b_4149_);
    v___x_4151_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4152_ = lean_array_get_size(v_buckets_4150_);
    v___x_4153_ = lean_nat_dec_lt(v___x_4151_, v___x_4152_);
    if v___x_4153_ == 0 {
        let mut v_toApplicative_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4150_);
        crate::leanh::lean_dec(v_f_4147_);
        v_toApplicative_4154_ = crate::leanh::lean_ctor_get(v_inst_4146_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4154_);
        crate::leanh::lean_dec_ref(v_inst_4146_);
        v_toPure_4155_ = crate::leanh::lean_ctor_get(v_toApplicative_4154_, 1);
        crate::leanh::lean_inc(v_toPure_4155_);
        crate::leanh::lean_dec_ref(v_toApplicative_4154_);
        v___x_4156_ =
            crate::leanh::lean_apply_2(v_toPure_4155_, crate::leanh::lean_box(0), v_init_4148_);
        return v___x_4156_;
    } else {
        let mut v___f_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4158_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_4146_);
        v___f_4157_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4157_, 0, v_inst_4146_);
        crate::leanh::lean_closure_set(v___f_4157_, 1, v_f_4147_);
        v___x_4158_ = lean_nat_dec_le(v___x_4152_, v___x_4152_);
        if v___x_4158_ == 0 {
            if v___x_4153_ == 0 {
                let mut v_toApplicative_4159_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4157_);
                crate::leanh::lean_dec_ref(v_buckets_4150_);
                v_toApplicative_4159_ = crate::leanh::lean_ctor_get(v_inst_4146_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4159_);
                crate::leanh::lean_dec_ref(v_inst_4146_);
                v_toPure_4160_ = crate::leanh::lean_ctor_get(v_toApplicative_4159_, 1);
                crate::leanh::lean_inc(v_toPure_4160_);
                crate::leanh::lean_dec_ref(v_toApplicative_4159_);
                v___x_4161_ = crate::leanh::lean_apply_2(
                    v_toPure_4160_,
                    crate::leanh::lean_box(0),
                    v_init_4148_,
                );
                return v___x_4161_;
            } else {
                let mut v___x_4162_: usize = 0;
                let mut v___x_4163_: usize = 0;
                let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4162_ = 0usize;
                v___x_4163_ = lean_usize_of_nat(v___x_4152_);
                v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4146_,
                    v___f_4157_,
                    v_buckets_4150_,
                    v___x_4162_,
                    v___x_4163_,
                    v_init_4148_,
                );
                return v___x_4164_;
            }
        } else {
            let mut v___x_4165_: usize = 0;
            let mut v___x_4166_: usize = 0;
            let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4165_ = 0usize;
            v___x_4166_ = lean_usize_of_nat(v___x_4152_);
            v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4146_,
                v___f_4157_,
                v_buckets_4150_,
                v___x_4165_,
                v___x_4166_,
                v_init_4148_,
            );
            return v___x_4167_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_foldM(
    mut v_00_u03b1_4168_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4169_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4170_: *mut crate::leanh::LeanObject,
    mut v_m_4171_: *mut crate::leanh::LeanObject,
    mut v_inst_4172_: *mut crate::leanh::LeanObject,
    mut v_x_4173_: *mut crate::leanh::LeanObject,
    mut v_x_4174_: *mut crate::leanh::LeanObject,
    mut v_f_4175_: *mut crate::leanh::LeanObject,
    mut v_init_4176_: *mut crate::leanh::LeanObject,
    mut v_b_4177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    v_buckets_4178_ = crate::leanh::lean_ctor_get(v_b_4177_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4178_);
    crate::leanh::lean_dec_ref(v_b_4177_);
    v___x_4179_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4180_ = lean_array_get_size(v_buckets_4178_);
    v___x_4181_ = lean_nat_dec_lt(v___x_4179_, v___x_4180_);
    if v___x_4181_ == 0 {
        let mut v_toApplicative_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4178_);
        crate::leanh::lean_dec(v_f_4175_);
        v_toApplicative_4182_ = crate::leanh::lean_ctor_get(v_inst_4172_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4182_);
        crate::leanh::lean_dec_ref(v_inst_4172_);
        v_toPure_4183_ = crate::leanh::lean_ctor_get(v_toApplicative_4182_, 1);
        crate::leanh::lean_inc(v_toPure_4183_);
        crate::leanh::lean_dec_ref(v_toApplicative_4182_);
        v___x_4184_ =
            crate::leanh::lean_apply_2(v_toPure_4183_, crate::leanh::lean_box(0), v_init_4176_);
        return v___x_4184_;
    } else {
        let mut v___f_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4186_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_4172_);
        v___f_4185_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4185_, 0, v_inst_4172_);
        crate::leanh::lean_closure_set(v___f_4185_, 1, v_f_4175_);
        v___x_4186_ = lean_nat_dec_le(v___x_4180_, v___x_4180_);
        if v___x_4186_ == 0 {
            if v___x_4181_ == 0 {
                let mut v_toApplicative_4187_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4185_);
                crate::leanh::lean_dec_ref(v_buckets_4178_);
                v_toApplicative_4187_ = crate::leanh::lean_ctor_get(v_inst_4172_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4187_);
                crate::leanh::lean_dec_ref(v_inst_4172_);
                v_toPure_4188_ = crate::leanh::lean_ctor_get(v_toApplicative_4187_, 1);
                crate::leanh::lean_inc(v_toPure_4188_);
                crate::leanh::lean_dec_ref(v_toApplicative_4187_);
                v___x_4189_ = crate::leanh::lean_apply_2(
                    v_toPure_4188_,
                    crate::leanh::lean_box(0),
                    v_init_4176_,
                );
                return v___x_4189_;
            } else {
                let mut v___x_4190_: usize = 0;
                let mut v___x_4191_: usize = 0;
                let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4190_ = 0usize;
                v___x_4191_ = lean_usize_of_nat(v___x_4180_);
                v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4172_,
                    v___f_4185_,
                    v_buckets_4178_,
                    v___x_4190_,
                    v___x_4191_,
                    v_init_4176_,
                );
                return v___x_4192_;
            }
        } else {
            let mut v___x_4193_: usize = 0;
            let mut v___x_4194_: usize = 0;
            let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4193_ = 0usize;
            v___x_4194_ = lean_usize_of_nat(v___x_4180_);
            v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4172_,
                v___f_4185_,
                v_buckets_4178_,
                v___x_4193_,
                v___x_4194_,
                v_init_4176_,
            );
            return v___x_4195_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_foldM___boxed(
    mut v_00_u03b1_4196_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4197_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4198_: *mut crate::leanh::LeanObject,
    mut v_m_4199_: *mut crate::leanh::LeanObject,
    mut v_inst_4200_: *mut crate::leanh::LeanObject,
    mut v_x_4201_: *mut crate::leanh::LeanObject,
    mut v_x_4202_: *mut crate::leanh::LeanObject,
    mut v_f_4203_: *mut crate::leanh::LeanObject,
    mut v_init_4204_: *mut crate::leanh::LeanObject,
    mut v_b_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_Std_DHashMap_foldM(
        v_00_u03b1_4196_,
        v_00_u03b2_4197_,
        v_00_u03b4_4198_,
        v_m_4199_,
        v_inst_4200_,
        v_x_4201_,
        v_x_4202_,
        v_f_4203_,
        v_init_4204_,
        v_b_4205_,
    );
    crate::leanh::lean_dec_ref(v_x_4202_);
    crate::leanh::lean_dec_ref(v_x_4201_);
    return v_res_4206_;
}
pub unsafe fn l_Std_DHashMap_fold___redArg___lam__0(
    mut v_f_4207_: *mut crate::leanh::LeanObject,
    mut v_x1_4208_: *mut crate::leanh::LeanObject,
    mut v_x2_4209_: *mut crate::leanh::LeanObject,
    mut v_x3_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4211_ = crate::leanh::lean_apply_3(v_f_4207_, v_x1_4208_, v_x2_4209_, v_x3_4210_);
    return v___x_4211_;
}
pub unsafe fn l_Std_DHashMap_fold___redArg___lam__1(
    mut v___x_4212_: *mut crate::leanh::LeanObject,
    mut v___f_4213_: *mut crate::leanh::LeanObject,
    mut v_acc_4214_: *mut crate::leanh::LeanObject,
    mut v_l_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4216_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4212_,
        v___f_4213_,
        v_acc_4214_,
        v_l_4215_,
    );
    return v___x_4216_;
}
pub unsafe fn l_Std_DHashMap_fold___redArg(
    mut v_f_4217_: *mut crate::leanh::LeanObject,
    mut v_init_4218_: *mut crate::leanh::LeanObject,
    mut v_b_4219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    v___x_4220_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4221_ = crate::leanh::lean_ctor_get(v_b_4219_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4221_);
    crate::leanh::lean_dec_ref(v_b_4219_);
    v___x_4222_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4223_ = lean_array_get_size(v_buckets_4221_);
    v___x_4224_ = lean_nat_dec_lt(v___x_4222_, v___x_4223_);
    if v___x_4224_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4221_);
        crate::leanh::lean_dec(v_f_4217_);
        return v_init_4218_;
    } else {
        let mut v___f_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4227_: u8 = 0;
        v___f_4225_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4225_, 0, v_f_4217_);
        v___f_4226_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4226_, 0, v___x_4220_);
        crate::leanh::lean_closure_set(v___f_4226_, 1, v___f_4225_);
        v___x_4227_ = lean_nat_dec_le(v___x_4223_, v___x_4223_);
        if v___x_4227_ == 0 {
            if v___x_4224_ == 0 {
                crate::leanh::lean_dec_ref(v___f_4226_);
                crate::leanh::lean_dec_ref(v_buckets_4221_);
                return v_init_4218_;
            } else {
                let mut v___x_4228_: usize = 0;
                let mut v___x_4229_: usize = 0;
                let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4228_ = 0usize;
                v___x_4229_ = lean_usize_of_nat(v___x_4223_);
                v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4220_,
                    v___f_4226_,
                    v_buckets_4221_,
                    v___x_4228_,
                    v___x_4229_,
                    v_init_4218_,
                );
                return v___x_4230_;
            }
        } else {
            let mut v___x_4231_: usize = 0;
            let mut v___x_4232_: usize = 0;
            let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4231_ = 0usize;
            v___x_4232_ = lean_usize_of_nat(v___x_4223_);
            v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4220_,
                v___f_4226_,
                v_buckets_4221_,
                v___x_4231_,
                v___x_4232_,
                v_init_4218_,
            );
            return v___x_4233_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_fold(
    mut v_00_u03b1_4234_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4235_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4236_: *mut crate::leanh::LeanObject,
    mut v_x_4237_: *mut crate::leanh::LeanObject,
    mut v_x_4238_: *mut crate::leanh::LeanObject,
    mut v_f_4239_: *mut crate::leanh::LeanObject,
    mut v_init_4240_: *mut crate::leanh::LeanObject,
    mut v_b_4241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    v___x_4242_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4243_ = crate::leanh::lean_ctor_get(v_b_4241_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4243_);
    crate::leanh::lean_dec_ref(v_b_4241_);
    v___x_4244_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4245_ = lean_array_get_size(v_buckets_4243_);
    v___x_4246_ = lean_nat_dec_lt(v___x_4244_, v___x_4245_);
    if v___x_4246_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4243_);
        crate::leanh::lean_dec(v_f_4239_);
        return v_init_4240_;
    } else {
        let mut v___f_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4249_: u8 = 0;
        v___f_4247_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4247_, 0, v_f_4239_);
        v___f_4248_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4248_, 0, v___x_4242_);
        crate::leanh::lean_closure_set(v___f_4248_, 1, v___f_4247_);
        v___x_4249_ = lean_nat_dec_le(v___x_4245_, v___x_4245_);
        if v___x_4249_ == 0 {
            if v___x_4246_ == 0 {
                crate::leanh::lean_dec_ref(v___f_4248_);
                crate::leanh::lean_dec_ref(v_buckets_4243_);
                return v_init_4240_;
            } else {
                let mut v___x_4250_: usize = 0;
                let mut v___x_4251_: usize = 0;
                let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4250_ = 0usize;
                v___x_4251_ = lean_usize_of_nat(v___x_4245_);
                v___x_4252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4242_,
                    v___f_4248_,
                    v_buckets_4243_,
                    v___x_4250_,
                    v___x_4251_,
                    v_init_4240_,
                );
                return v___x_4252_;
            }
        } else {
            let mut v___x_4253_: usize = 0;
            let mut v___x_4254_: usize = 0;
            let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4253_ = 0usize;
            v___x_4254_ = lean_usize_of_nat(v___x_4245_);
            v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4242_,
                v___f_4248_,
                v_buckets_4243_,
                v___x_4253_,
                v___x_4254_,
                v_init_4240_,
            );
            return v___x_4255_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_fold___boxed(
    mut v_00_u03b1_4256_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4257_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4258_: *mut crate::leanh::LeanObject,
    mut v_x_4259_: *mut crate::leanh::LeanObject,
    mut v_x_4260_: *mut crate::leanh::LeanObject,
    mut v_f_4261_: *mut crate::leanh::LeanObject,
    mut v_init_4262_: *mut crate::leanh::LeanObject,
    mut v_b_4263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4264_ = l_Std_DHashMap_fold(
        v_00_u03b1_4256_,
        v_00_u03b2_4257_,
        v_00_u03b4_4258_,
        v_x_4259_,
        v_x_4260_,
        v_f_4261_,
        v_init_4262_,
        v_b_4263_,
    );
    crate::leanh::lean_dec_ref(v_x_4260_);
    crate::leanh::lean_dec_ref(v_x_4259_);
    return v_res_4264_;
}
pub unsafe fn l_Std_DHashMap_forM___redArg___lam__0(
    mut v_f_4265_: *mut crate::leanh::LeanObject,
    mut v_x_4266_: *mut crate::leanh::LeanObject,
    mut v___y_4267_: *mut crate::leanh::LeanObject,
    mut v___y_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = crate::leanh::lean_apply_2(v_f_4265_, v___y_4267_, v___y_4268_);
    return v___x_4269_;
}
pub unsafe fn l_Std_DHashMap_forM___redArg___lam__1(
    mut v_inst_4270_: *mut crate::leanh::LeanObject,
    mut v___f_4271_: *mut crate::leanh::LeanObject,
    mut v_x_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4274_ = crate::leanh::lean_box(0);
    v___x_4275_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_4270_,
        v___f_4271_,
        v___x_4274_,
        v___y_4273_,
    );
    return v___x_4275_;
}
pub unsafe fn l_Std_DHashMap_forM___redArg(
    mut v_inst_4276_: *mut crate::leanh::LeanObject,
    mut v_f_4277_: *mut crate::leanh::LeanObject,
    mut v_b_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: u8 = 0;
    v_buckets_4279_ = crate::leanh::lean_ctor_get(v_b_4278_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4279_);
    crate::leanh::lean_dec_ref(v_b_4278_);
    v___x_4280_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4281_ = lean_array_get_size(v_buckets_4279_);
    v___x_4282_ = crate::leanh::lean_box(0);
    v___x_4283_ = lean_nat_dec_lt(v___x_4280_, v___x_4281_);
    if v___x_4283_ == 0 {
        let mut v_toApplicative_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4279_);
        crate::leanh::lean_dec(v_f_4277_);
        v_toApplicative_4284_ = crate::leanh::lean_ctor_get(v_inst_4276_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4284_);
        crate::leanh::lean_dec_ref(v_inst_4276_);
        v_toPure_4285_ = crate::leanh::lean_ctor_get(v_toApplicative_4284_, 1);
        crate::leanh::lean_inc(v_toPure_4285_);
        crate::leanh::lean_dec_ref(v_toApplicative_4284_);
        v___x_4286_ =
            crate::leanh::lean_apply_2(v_toPure_4285_, crate::leanh::lean_box(0), v___x_4282_);
        return v___x_4286_;
    } else {
        let mut v___f_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4289_: u8 = 0;
        v___f_4287_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4287_, 0, v_f_4277_);
        crate::leanh::lean_inc_ref(v_inst_4276_);
        v___f_4288_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4288_, 0, v_inst_4276_);
        crate::leanh::lean_closure_set(v___f_4288_, 1, v___f_4287_);
        v___x_4289_ = lean_nat_dec_le(v___x_4281_, v___x_4281_);
        if v___x_4289_ == 0 {
            if v___x_4283_ == 0 {
                let mut v_toApplicative_4290_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4288_);
                crate::leanh::lean_dec_ref(v_buckets_4279_);
                v_toApplicative_4290_ = crate::leanh::lean_ctor_get(v_inst_4276_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4290_);
                crate::leanh::lean_dec_ref(v_inst_4276_);
                v_toPure_4291_ = crate::leanh::lean_ctor_get(v_toApplicative_4290_, 1);
                crate::leanh::lean_inc(v_toPure_4291_);
                crate::leanh::lean_dec_ref(v_toApplicative_4290_);
                v___x_4292_ = crate::leanh::lean_apply_2(
                    v_toPure_4291_,
                    crate::leanh::lean_box(0),
                    v___x_4282_,
                );
                return v___x_4292_;
            } else {
                let mut v___x_4293_: usize = 0;
                let mut v___x_4294_: usize = 0;
                let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4293_ = 0usize;
                v___x_4294_ = lean_usize_of_nat(v___x_4281_);
                v___x_4295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4276_,
                    v___f_4288_,
                    v_buckets_4279_,
                    v___x_4293_,
                    v___x_4294_,
                    v___x_4282_,
                );
                return v___x_4295_;
            }
        } else {
            let mut v___x_4296_: usize = 0;
            let mut v___x_4297_: usize = 0;
            let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4296_ = 0usize;
            v___x_4297_ = lean_usize_of_nat(v___x_4281_);
            v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4276_,
                v___f_4288_,
                v_buckets_4279_,
                v___x_4296_,
                v___x_4297_,
                v___x_4282_,
            );
            return v___x_4298_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_forM(
    mut v_00_u03b1_4299_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4300_: *mut crate::leanh::LeanObject,
    mut v_m_4301_: *mut crate::leanh::LeanObject,
    mut v_inst_4302_: *mut crate::leanh::LeanObject,
    mut v_x_4303_: *mut crate::leanh::LeanObject,
    mut v_x_4304_: *mut crate::leanh::LeanObject,
    mut v_f_4305_: *mut crate::leanh::LeanObject,
    mut v_b_4306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    v_buckets_4307_ = crate::leanh::lean_ctor_get(v_b_4306_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4307_);
    crate::leanh::lean_dec_ref(v_b_4306_);
    v___x_4308_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4309_ = lean_array_get_size(v_buckets_4307_);
    v___x_4310_ = crate::leanh::lean_box(0);
    v___x_4311_ = lean_nat_dec_lt(v___x_4308_, v___x_4309_);
    if v___x_4311_ == 0 {
        let mut v_toApplicative_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4307_);
        crate::leanh::lean_dec(v_f_4305_);
        v_toApplicative_4312_ = crate::leanh::lean_ctor_get(v_inst_4302_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4312_);
        crate::leanh::lean_dec_ref(v_inst_4302_);
        v_toPure_4313_ = crate::leanh::lean_ctor_get(v_toApplicative_4312_, 1);
        crate::leanh::lean_inc(v_toPure_4313_);
        crate::leanh::lean_dec_ref(v_toApplicative_4312_);
        v___x_4314_ =
            crate::leanh::lean_apply_2(v_toPure_4313_, crate::leanh::lean_box(0), v___x_4310_);
        return v___x_4314_;
    } else {
        let mut v___f_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4317_: u8 = 0;
        v___f_4315_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4315_, 0, v_f_4305_);
        crate::leanh::lean_inc_ref(v_inst_4302_);
        v___f_4316_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4316_, 0, v_inst_4302_);
        crate::leanh::lean_closure_set(v___f_4316_, 1, v___f_4315_);
        v___x_4317_ = lean_nat_dec_le(v___x_4309_, v___x_4309_);
        if v___x_4317_ == 0 {
            if v___x_4311_ == 0 {
                let mut v_toApplicative_4318_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4316_);
                crate::leanh::lean_dec_ref(v_buckets_4307_);
                v_toApplicative_4318_ = crate::leanh::lean_ctor_get(v_inst_4302_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4318_);
                crate::leanh::lean_dec_ref(v_inst_4302_);
                v_toPure_4319_ = crate::leanh::lean_ctor_get(v_toApplicative_4318_, 1);
                crate::leanh::lean_inc(v_toPure_4319_);
                crate::leanh::lean_dec_ref(v_toApplicative_4318_);
                v___x_4320_ = crate::leanh::lean_apply_2(
                    v_toPure_4319_,
                    crate::leanh::lean_box(0),
                    v___x_4310_,
                );
                return v___x_4320_;
            } else {
                let mut v___x_4321_: usize = 0;
                let mut v___x_4322_: usize = 0;
                let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4321_ = 0usize;
                v___x_4322_ = lean_usize_of_nat(v___x_4309_);
                v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4302_,
                    v___f_4316_,
                    v_buckets_4307_,
                    v___x_4321_,
                    v___x_4322_,
                    v___x_4310_,
                );
                return v___x_4323_;
            }
        } else {
            let mut v___x_4324_: usize = 0;
            let mut v___x_4325_: usize = 0;
            let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4324_ = 0usize;
            v___x_4325_ = lean_usize_of_nat(v___x_4309_);
            v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4302_,
                v___f_4316_,
                v_buckets_4307_,
                v___x_4324_,
                v___x_4325_,
                v___x_4310_,
            );
            return v___x_4326_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_forM___boxed(
    mut v_00_u03b1_4327_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4328_: *mut crate::leanh::LeanObject,
    mut v_m_4329_: *mut crate::leanh::LeanObject,
    mut v_inst_4330_: *mut crate::leanh::LeanObject,
    mut v_x_4331_: *mut crate::leanh::LeanObject,
    mut v_x_4332_: *mut crate::leanh::LeanObject,
    mut v_f_4333_: *mut crate::leanh::LeanObject,
    mut v_b_4334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4335_ = l_Std_DHashMap_forM(
        v_00_u03b1_4327_,
        v_00_u03b2_4328_,
        v_m_4329_,
        v_inst_4330_,
        v_x_4331_,
        v_x_4332_,
        v_f_4333_,
        v_b_4334_,
    );
    crate::leanh::lean_dec_ref(v_x_4332_);
    crate::leanh::lean_dec_ref(v_x_4331_);
    return v_res_4335_;
}
pub unsafe fn l_Std_DHashMap_forIn___redArg___lam__0(
    mut v_inst_4336_: *mut crate::leanh::LeanObject,
    mut v_f_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_x_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4341_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_4336_, v_f_4337_, v_a_4338_, v___y_4340_);
    return v___x_4341_;
}
pub unsafe fn l_Std_DHashMap_forIn___redArg(
    mut v_inst_4342_: *mut crate::leanh::LeanObject,
    mut v_f_4343_: *mut crate::leanh::LeanObject,
    mut v_init_4344_: *mut crate::leanh::LeanObject,
    mut v_b_4345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4348_: usize = 0;
    let mut v___x_4349_: usize = 0;
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4346_ = crate::leanh::lean_ctor_get(v_b_4345_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4346_);
    crate::leanh::lean_dec_ref(v_b_4345_);
    crate::leanh::lean_inc_ref(v_inst_4342_);
    v___f_4347_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4347_, 0, v_inst_4342_);
    crate::leanh::lean_closure_set(v___f_4347_, 1, v_f_4343_);
    v_sz_4348_ = lean_array_size(v_buckets_4346_);
    v___x_4349_ = 0usize;
    v___x_4350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4342_,
        v_buckets_4346_,
        v___f_4347_,
        v_sz_4348_,
        v___x_4349_,
        v_init_4344_,
    );
    return v___x_4350_;
}
pub unsafe fn l_Std_DHashMap_forIn(
    mut v_00_u03b1_4351_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4352_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4353_: *mut crate::leanh::LeanObject,
    mut v_m_4354_: *mut crate::leanh::LeanObject,
    mut v_inst_4355_: *mut crate::leanh::LeanObject,
    mut v_x_4356_: *mut crate::leanh::LeanObject,
    mut v_x_4357_: *mut crate::leanh::LeanObject,
    mut v_f_4358_: *mut crate::leanh::LeanObject,
    mut v_init_4359_: *mut crate::leanh::LeanObject,
    mut v_b_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4363_: usize = 0;
    let mut v___x_4364_: usize = 0;
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4361_ = crate::leanh::lean_ctor_get(v_b_4360_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4361_);
    crate::leanh::lean_dec_ref(v_b_4360_);
    crate::leanh::lean_inc_ref(v_inst_4355_);
    v___f_4362_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4362_, 0, v_inst_4355_);
    crate::leanh::lean_closure_set(v___f_4362_, 1, v_f_4358_);
    v_sz_4363_ = lean_array_size(v_buckets_4361_);
    v___x_4364_ = 0usize;
    v___x_4365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4355_,
        v_buckets_4361_,
        v___f_4362_,
        v_sz_4363_,
        v___x_4364_,
        v_init_4359_,
    );
    return v___x_4365_;
}
pub unsafe fn l_Std_DHashMap_forIn___boxed(
    mut v_00_u03b1_4366_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4368_: *mut crate::leanh::LeanObject,
    mut v_m_4369_: *mut crate::leanh::LeanObject,
    mut v_inst_4370_: *mut crate::leanh::LeanObject,
    mut v_x_4371_: *mut crate::leanh::LeanObject,
    mut v_x_4372_: *mut crate::leanh::LeanObject,
    mut v_f_4373_: *mut crate::leanh::LeanObject,
    mut v_init_4374_: *mut crate::leanh::LeanObject,
    mut v_b_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4376_ = l_Std_DHashMap_forIn(
        v_00_u03b1_4366_,
        v_00_u03b2_4367_,
        v_00_u03b4_4368_,
        v_m_4369_,
        v_inst_4370_,
        v_x_4371_,
        v_x_4372_,
        v_f_4373_,
        v_init_4374_,
        v_b_4375_,
    );
    crate::leanh::lean_dec_ref(v_x_4372_);
    crate::leanh::lean_dec_ref(v_x_4371_);
    return v_res_4376_;
}
pub unsafe fn l_Std_DHashMap_instForMSigmaOfMonad___redArg___lam__0(
    mut v_f_4377_: *mut crate::leanh::LeanObject,
    mut v_x_4378_: *mut crate::leanh::LeanObject,
    mut v___y_4379_: *mut crate::leanh::LeanObject,
    mut v___y_4380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4381_, 0, v___y_4379_);
    crate::leanh::lean_ctor_set(v___x_4381_, 1, v___y_4380_);
    v___x_4382_ = crate::leanh::lean_apply_1(v_f_4377_, v___x_4381_);
    return v___x_4382_;
}
pub unsafe fn l_Std_DHashMap_instForMSigmaOfMonad___redArg___lam__2(
    mut v_inst_4383_: *mut crate::leanh::LeanObject,
    mut v_m_4384_: *mut crate::leanh::LeanObject,
    mut v_f_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: u8 = 0;
    v_buckets_4386_ = crate::leanh::lean_ctor_get(v_m_4384_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4386_);
    crate::leanh::lean_dec_ref(v_m_4384_);
    v___x_4387_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4388_ = lean_array_get_size(v_buckets_4386_);
    v___x_4389_ = crate::leanh::lean_box(0);
    v___x_4390_ = lean_nat_dec_lt(v___x_4387_, v___x_4388_);
    if v___x_4390_ == 0 {
        let mut v_toApplicative_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4386_);
        crate::leanh::lean_dec(v_f_4385_);
        v_toApplicative_4391_ = crate::leanh::lean_ctor_get(v_inst_4383_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4391_);
        crate::leanh::lean_dec_ref(v_inst_4383_);
        v_toPure_4392_ = crate::leanh::lean_ctor_get(v_toApplicative_4391_, 1);
        crate::leanh::lean_inc(v_toPure_4392_);
        crate::leanh::lean_dec_ref(v_toApplicative_4391_);
        v___x_4393_ =
            crate::leanh::lean_apply_2(v_toPure_4392_, crate::leanh::lean_box(0), v___x_4389_);
        return v___x_4393_;
    } else {
        let mut v___f_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4396_: u8 = 0;
        v___f_4394_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_instForMSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4394_, 0, v_f_4385_);
        crate::leanh::lean_inc_ref(v_inst_4383_);
        v___f_4395_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4395_, 0, v_inst_4383_);
        crate::leanh::lean_closure_set(v___f_4395_, 1, v___f_4394_);
        v___x_4396_ = lean_nat_dec_le(v___x_4388_, v___x_4388_);
        if v___x_4396_ == 0 {
            if v___x_4390_ == 0 {
                let mut v_toApplicative_4397_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4395_);
                crate::leanh::lean_dec_ref(v_buckets_4386_);
                v_toApplicative_4397_ = crate::leanh::lean_ctor_get(v_inst_4383_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4397_);
                crate::leanh::lean_dec_ref(v_inst_4383_);
                v_toPure_4398_ = crate::leanh::lean_ctor_get(v_toApplicative_4397_, 1);
                crate::leanh::lean_inc(v_toPure_4398_);
                crate::leanh::lean_dec_ref(v_toApplicative_4397_);
                v___x_4399_ = crate::leanh::lean_apply_2(
                    v_toPure_4398_,
                    crate::leanh::lean_box(0),
                    v___x_4389_,
                );
                return v___x_4399_;
            } else {
                let mut v___x_4400_: usize = 0;
                let mut v___x_4401_: usize = 0;
                let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4400_ = 0usize;
                v___x_4401_ = lean_usize_of_nat(v___x_4388_);
                v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4383_,
                    v___f_4395_,
                    v_buckets_4386_,
                    v___x_4400_,
                    v___x_4401_,
                    v___x_4389_,
                );
                return v___x_4402_;
            }
        } else {
            let mut v___x_4403_: usize = 0;
            let mut v___x_4404_: usize = 0;
            let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4403_ = 0usize;
            v___x_4404_ = lean_usize_of_nat(v___x_4388_);
            v___x_4405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4383_,
                v___f_4395_,
                v_buckets_4386_,
                v___x_4403_,
                v___x_4404_,
                v___x_4389_,
            );
            return v___x_4405_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_instForMSigmaOfMonad___redArg(
    mut v_inst_4406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4407_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForMSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4407_, 0, v_inst_4406_);
    return v___f_4407_;
}
pub unsafe fn l_Std_DHashMap_instForMSigmaOfMonad(
    mut v_00_u03b1_4408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4409_: *mut crate::leanh::LeanObject,
    mut v_m_4410_: *mut crate::leanh::LeanObject,
    mut v_inst_4411_: *mut crate::leanh::LeanObject,
    mut v_inst_4412_: *mut crate::leanh::LeanObject,
    mut v_inst_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4414_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForMSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4414_, 0, v_inst_4411_);
    return v___f_4414_;
}
pub unsafe fn l_Std_DHashMap_instForMSigmaOfMonad___boxed(
    mut v_00_u03b1_4415_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4416_: *mut crate::leanh::LeanObject,
    mut v_m_4417_: *mut crate::leanh::LeanObject,
    mut v_inst_4418_: *mut crate::leanh::LeanObject,
    mut v_inst_4419_: *mut crate::leanh::LeanObject,
    mut v_inst_4420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4421_ = l_Std_DHashMap_instForMSigmaOfMonad(
        v_00_u03b1_4415_,
        v_00_u03b2_4416_,
        v_m_4417_,
        v_inst_4418_,
        v_inst_4419_,
        v_inst_4420_,
    );
    crate::leanh::lean_dec_ref(v_inst_4420_);
    crate::leanh::lean_dec_ref(v_inst_4419_);
    return v_res_4421_;
}
pub unsafe fn l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__0(
    mut v_f_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_b_4424_: *mut crate::leanh::LeanObject,
    mut v_acc_4425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4426_, 0, v_a_4423_);
    crate::leanh::lean_ctor_set(v___x_4426_, 1, v_b_4424_);
    v___x_4427_ = crate::leanh::lean_apply_2(v_f_4422_, v___x_4426_, v_acc_4425_);
    return v___x_4427_;
}
pub unsafe fn l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__1(
    mut v_inst_4428_: *mut crate::leanh::LeanObject,
    mut v___f_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
    mut v_x_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4433_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_4428_, v___f_4429_, v_a_4430_, v___y_4432_);
    return v___x_4433_;
}
pub unsafe fn l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__2(
    mut v_inst_4434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4435_: *mut crate::leanh::LeanObject,
    mut v_m_4436_: *mut crate::leanh::LeanObject,
    mut v_init_4437_: *mut crate::leanh::LeanObject,
    mut v_f_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4442_: usize = 0;
    let mut v___x_4443_: usize = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4439_ = crate::leanh::lean_ctor_get(v_m_4436_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4439_);
    crate::leanh::lean_dec_ref(v_m_4436_);
    v___f_4440_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4440_, 0, v_f_4438_);
    crate::leanh::lean_inc_ref(v_inst_4434_);
    v___f_4441_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4441_, 0, v_inst_4434_);
    crate::leanh::lean_closure_set(v___f_4441_, 1, v___f_4440_);
    v_sz_4442_ = lean_array_size(v_buckets_4439_);
    v___x_4443_ = 0usize;
    v___x_4444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4434_,
        v_buckets_4439_,
        v___f_4441_,
        v_sz_4442_,
        v___x_4443_,
        v_init_4437_,
    );
    return v___x_4444_;
}
pub unsafe fn l_Std_DHashMap_instForInSigmaOfMonad___redArg(
    mut v_inst_4445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4446_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4446_, 0, v_inst_4445_);
    return v___f_4446_;
}
pub unsafe fn l_Std_DHashMap_instForInSigmaOfMonad(
    mut v_00_u03b1_4447_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4448_: *mut crate::leanh::LeanObject,
    mut v_m_4449_: *mut crate::leanh::LeanObject,
    mut v_inst_4450_: *mut crate::leanh::LeanObject,
    mut v_inst_4451_: *mut crate::leanh::LeanObject,
    mut v_inst_4452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4453_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4453_, 0, v_inst_4450_);
    return v___f_4453_;
}
pub unsafe fn l_Std_DHashMap_instForInSigmaOfMonad___boxed(
    mut v_00_u03b1_4454_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4455_: *mut crate::leanh::LeanObject,
    mut v_m_4456_: *mut crate::leanh::LeanObject,
    mut v_inst_4457_: *mut crate::leanh::LeanObject,
    mut v_inst_4458_: *mut crate::leanh::LeanObject,
    mut v_inst_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4460_ = l_Std_DHashMap_instForInSigmaOfMonad(
        v_00_u03b1_4454_,
        v_00_u03b2_4455_,
        v_m_4456_,
        v_inst_4457_,
        v_inst_4458_,
        v_inst_4459_,
    );
    crate::leanh::lean_dec_ref(v_inst_4459_);
    crate::leanh::lean_dec_ref(v_inst_4458_);
    return v_res_4460_;
}
pub unsafe fn l_Std_DHashMap_Const_forMUncurried___redArg___lam__0(
    mut v_f_4461_: *mut crate::leanh::LeanObject,
    mut v_x_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4465_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4465_, 0, v___y_4463_);
    crate::leanh::lean_ctor_set(v___x_4465_, 1, v___y_4464_);
    v___x_4466_ = crate::leanh::lean_apply_1(v_f_4461_, v___x_4465_);
    return v___x_4466_;
}
pub unsafe fn l_Std_DHashMap_Const_forMUncurried___redArg(
    mut v_inst_4467_: *mut crate::leanh::LeanObject,
    mut v_f_4468_: *mut crate::leanh::LeanObject,
    mut v_b_4469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u8 = 0;
    v_buckets_4470_ = crate::leanh::lean_ctor_get(v_b_4469_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4470_);
    crate::leanh::lean_dec_ref(v_b_4469_);
    v___x_4471_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4472_ = lean_array_get_size(v_buckets_4470_);
    v___x_4473_ = crate::leanh::lean_box(0);
    v___x_4474_ = lean_nat_dec_lt(v___x_4471_, v___x_4472_);
    if v___x_4474_ == 0 {
        let mut v_toApplicative_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4470_);
        crate::leanh::lean_dec(v_f_4468_);
        v_toApplicative_4475_ = crate::leanh::lean_ctor_get(v_inst_4467_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4475_);
        crate::leanh::lean_dec_ref(v_inst_4467_);
        v_toPure_4476_ = crate::leanh::lean_ctor_get(v_toApplicative_4475_, 1);
        crate::leanh::lean_inc(v_toPure_4476_);
        crate::leanh::lean_dec_ref(v_toApplicative_4475_);
        v___x_4477_ =
            crate::leanh::lean_apply_2(v_toPure_4476_, crate::leanh::lean_box(0), v___x_4473_);
        return v___x_4477_;
    } else {
        let mut v___f_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4480_: u8 = 0;
        v___f_4478_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4478_, 0, v_f_4468_);
        crate::leanh::lean_inc_ref(v_inst_4467_);
        v___f_4479_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4479_, 0, v_inst_4467_);
        crate::leanh::lean_closure_set(v___f_4479_, 1, v___f_4478_);
        v___x_4480_ = lean_nat_dec_le(v___x_4472_, v___x_4472_);
        if v___x_4480_ == 0 {
            if v___x_4474_ == 0 {
                let mut v_toApplicative_4481_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4479_);
                crate::leanh::lean_dec_ref(v_buckets_4470_);
                v_toApplicative_4481_ = crate::leanh::lean_ctor_get(v_inst_4467_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4481_);
                crate::leanh::lean_dec_ref(v_inst_4467_);
                v_toPure_4482_ = crate::leanh::lean_ctor_get(v_toApplicative_4481_, 1);
                crate::leanh::lean_inc(v_toPure_4482_);
                crate::leanh::lean_dec_ref(v_toApplicative_4481_);
                v___x_4483_ = crate::leanh::lean_apply_2(
                    v_toPure_4482_,
                    crate::leanh::lean_box(0),
                    v___x_4473_,
                );
                return v___x_4483_;
            } else {
                let mut v___x_4484_: usize = 0;
                let mut v___x_4485_: usize = 0;
                let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4484_ = 0usize;
                v___x_4485_ = lean_usize_of_nat(v___x_4472_);
                v___x_4486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4467_,
                    v___f_4479_,
                    v_buckets_4470_,
                    v___x_4484_,
                    v___x_4485_,
                    v___x_4473_,
                );
                return v___x_4486_;
            }
        } else {
            let mut v___x_4487_: usize = 0;
            let mut v___x_4488_: usize = 0;
            let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4487_ = 0usize;
            v___x_4488_ = lean_usize_of_nat(v___x_4472_);
            v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4467_,
                v___f_4479_,
                v_buckets_4470_,
                v___x_4487_,
                v___x_4488_,
                v___x_4473_,
            );
            return v___x_4489_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Const_forMUncurried(
    mut v_00_u03b1_4490_: *mut crate::leanh::LeanObject,
    mut v_m_4491_: *mut crate::leanh::LeanObject,
    mut v_inst_4492_: *mut crate::leanh::LeanObject,
    mut v_x_4493_: *mut crate::leanh::LeanObject,
    mut v_x_4494_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4495_: *mut crate::leanh::LeanObject,
    mut v_f_4496_: *mut crate::leanh::LeanObject,
    mut v_b_4497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: u8 = 0;
    v_buckets_4498_ = crate::leanh::lean_ctor_get(v_b_4497_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4498_);
    crate::leanh::lean_dec_ref(v_b_4497_);
    v___x_4499_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4500_ = lean_array_get_size(v_buckets_4498_);
    v___x_4501_ = crate::leanh::lean_box(0);
    v___x_4502_ = lean_nat_dec_lt(v___x_4499_, v___x_4500_);
    if v___x_4502_ == 0 {
        let mut v_toApplicative_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4498_);
        crate::leanh::lean_dec(v_f_4496_);
        v_toApplicative_4503_ = crate::leanh::lean_ctor_get(v_inst_4492_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_4503_);
        crate::leanh::lean_dec_ref(v_inst_4492_);
        v_toPure_4504_ = crate::leanh::lean_ctor_get(v_toApplicative_4503_, 1);
        crate::leanh::lean_inc(v_toPure_4504_);
        crate::leanh::lean_dec_ref(v_toApplicative_4503_);
        v___x_4505_ =
            crate::leanh::lean_apply_2(v_toPure_4504_, crate::leanh::lean_box(0), v___x_4501_);
        return v___x_4505_;
    } else {
        let mut v___f_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4508_: u8 = 0;
        v___f_4506_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_4506_, 0, v_f_4496_);
        crate::leanh::lean_inc_ref(v_inst_4492_);
        v___f_4507_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4507_, 0, v_inst_4492_);
        crate::leanh::lean_closure_set(v___f_4507_, 1, v___f_4506_);
        v___x_4508_ = lean_nat_dec_le(v___x_4500_, v___x_4500_);
        if v___x_4508_ == 0 {
            if v___x_4502_ == 0 {
                let mut v_toApplicative_4509_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_4507_);
                crate::leanh::lean_dec_ref(v_buckets_4498_);
                v_toApplicative_4509_ = crate::leanh::lean_ctor_get(v_inst_4492_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_4509_);
                crate::leanh::lean_dec_ref(v_inst_4492_);
                v_toPure_4510_ = crate::leanh::lean_ctor_get(v_toApplicative_4509_, 1);
                crate::leanh::lean_inc(v_toPure_4510_);
                crate::leanh::lean_dec_ref(v_toApplicative_4509_);
                v___x_4511_ = crate::leanh::lean_apply_2(
                    v_toPure_4510_,
                    crate::leanh::lean_box(0),
                    v___x_4501_,
                );
                return v___x_4511_;
            } else {
                let mut v___x_4512_: usize = 0;
                let mut v___x_4513_: usize = 0;
                let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4512_ = 0usize;
                v___x_4513_ = lean_usize_of_nat(v___x_4500_);
                v___x_4514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4492_,
                    v___f_4507_,
                    v_buckets_4498_,
                    v___x_4512_,
                    v___x_4513_,
                    v___x_4501_,
                );
                return v___x_4514_;
            }
        } else {
            let mut v___x_4515_: usize = 0;
            let mut v___x_4516_: usize = 0;
            let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4515_ = 0usize;
            v___x_4516_ = lean_usize_of_nat(v___x_4500_);
            v___x_4517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4492_,
                v___f_4507_,
                v_buckets_4498_,
                v___x_4515_,
                v___x_4516_,
                v___x_4501_,
            );
            return v___x_4517_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Const_forMUncurried___boxed(
    mut v_00_u03b1_4518_: *mut crate::leanh::LeanObject,
    mut v_m_4519_: *mut crate::leanh::LeanObject,
    mut v_inst_4520_: *mut crate::leanh::LeanObject,
    mut v_x_4521_: *mut crate::leanh::LeanObject,
    mut v_x_4522_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4523_: *mut crate::leanh::LeanObject,
    mut v_f_4524_: *mut crate::leanh::LeanObject,
    mut v_b_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4526_ = l_Std_DHashMap_Const_forMUncurried(
        v_00_u03b1_4518_,
        v_m_4519_,
        v_inst_4520_,
        v_x_4521_,
        v_x_4522_,
        v_00_u03b2_4523_,
        v_f_4524_,
        v_b_4525_,
    );
    crate::leanh::lean_dec_ref(v_x_4522_);
    crate::leanh::lean_dec_ref(v_x_4521_);
    return v_res_4526_;
}
pub unsafe fn l_Std_DHashMap_Const_forInUncurried___redArg___lam__0(
    mut v_f_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_b_4529_: *mut crate::leanh::LeanObject,
    mut v_d_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4531_, 0, v_a_4528_);
    crate::leanh::lean_ctor_set(v___x_4531_, 1, v_b_4529_);
    v___x_4532_ = crate::leanh::lean_apply_2(v_f_4527_, v___x_4531_, v_d_4530_);
    return v___x_4532_;
}
pub unsafe fn l_Std_DHashMap_Const_forInUncurried___redArg(
    mut v_inst_4533_: *mut crate::leanh::LeanObject,
    mut v_f_4534_: *mut crate::leanh::LeanObject,
    mut v_init_4535_: *mut crate::leanh::LeanObject,
    mut v_b_4536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4540_: usize = 0;
    let mut v___x_4541_: usize = 0;
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4537_ = crate::leanh::lean_ctor_get(v_b_4536_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4537_);
    crate::leanh::lean_dec_ref(v_b_4536_);
    v___f_4538_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4538_, 0, v_f_4534_);
    crate::leanh::lean_inc_ref(v_inst_4533_);
    v___f_4539_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4539_, 0, v_inst_4533_);
    crate::leanh::lean_closure_set(v___f_4539_, 1, v___f_4538_);
    v_sz_4540_ = lean_array_size(v_buckets_4537_);
    v___x_4541_ = 0usize;
    v___x_4542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4533_,
        v_buckets_4537_,
        v___f_4539_,
        v_sz_4540_,
        v___x_4541_,
        v_init_4535_,
    );
    return v___x_4542_;
}
pub unsafe fn l_Std_DHashMap_Const_forInUncurried(
    mut v_00_u03b1_4543_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4544_: *mut crate::leanh::LeanObject,
    mut v_m_4545_: *mut crate::leanh::LeanObject,
    mut v_inst_4546_: *mut crate::leanh::LeanObject,
    mut v_x_4547_: *mut crate::leanh::LeanObject,
    mut v_x_4548_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4549_: *mut crate::leanh::LeanObject,
    mut v_f_4550_: *mut crate::leanh::LeanObject,
    mut v_init_4551_: *mut crate::leanh::LeanObject,
    mut v_b_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4556_: usize = 0;
    let mut v___x_4557_: usize = 0;
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4553_ = crate::leanh::lean_ctor_get(v_b_4552_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4553_);
    crate::leanh::lean_dec_ref(v_b_4552_);
    v___f_4554_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4554_, 0, v_f_4550_);
    crate::leanh::lean_inc_ref(v_inst_4546_);
    v___f_4555_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instForInSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4555_, 0, v_inst_4546_);
    crate::leanh::lean_closure_set(v___f_4555_, 1, v___f_4554_);
    v_sz_4556_ = lean_array_size(v_buckets_4553_);
    v___x_4557_ = 0usize;
    v___x_4558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4546_,
        v_buckets_4553_,
        v___f_4555_,
        v_sz_4556_,
        v___x_4557_,
        v_init_4551_,
    );
    return v___x_4558_;
}
pub unsafe fn l_Std_DHashMap_Const_forInUncurried___boxed(
    mut v_00_u03b1_4559_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4560_: *mut crate::leanh::LeanObject,
    mut v_m_4561_: *mut crate::leanh::LeanObject,
    mut v_inst_4562_: *mut crate::leanh::LeanObject,
    mut v_x_4563_: *mut crate::leanh::LeanObject,
    mut v_x_4564_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4565_: *mut crate::leanh::LeanObject,
    mut v_f_4566_: *mut crate::leanh::LeanObject,
    mut v_init_4567_: *mut crate::leanh::LeanObject,
    mut v_b_4568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4569_ = l_Std_DHashMap_Const_forInUncurried(
        v_00_u03b1_4559_,
        v_00_u03b4_4560_,
        v_m_4561_,
        v_inst_4562_,
        v_x_4563_,
        v_x_4564_,
        v_00_u03b2_4565_,
        v_f_4566_,
        v_init_4567_,
        v_b_4568_,
    );
    crate::leanh::lean_dec_ref(v_x_4564_);
    crate::leanh::lean_dec_ref(v_x_4563_);
    return v_res_4569_;
}
pub unsafe fn l_Std_DHashMap_filter___redArg(
    mut v_f_4570_: *mut crate::leanh::LeanObject,
    mut v_m_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4572_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4570_, v_m_4571_);
    return v___x_4572_;
}
pub unsafe fn l_Std_DHashMap_filter(
    mut v_00_u03b1_4573_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4574_: *mut crate::leanh::LeanObject,
    mut v_x_4575_: *mut crate::leanh::LeanObject,
    mut v_x_4576_: *mut crate::leanh::LeanObject,
    mut v_f_4577_: *mut crate::leanh::LeanObject,
    mut v_m_4578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4579_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4577_, v_m_4578_);
    return v___x_4579_;
}
pub unsafe fn l_Std_DHashMap_filter___boxed(
    mut v_00_u03b1_4580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4581_: *mut crate::leanh::LeanObject,
    mut v_x_4582_: *mut crate::leanh::LeanObject,
    mut v_x_4583_: *mut crate::leanh::LeanObject,
    mut v_f_4584_: *mut crate::leanh::LeanObject,
    mut v_m_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4586_ = l_Std_DHashMap_filter(
        v_00_u03b1_4580_,
        v_00_u03b2_4581_,
        v_x_4582_,
        v_x_4583_,
        v_f_4584_,
        v_m_4585_,
    );
    crate::leanh::lean_dec_ref(v_x_4583_);
    crate::leanh::lean_dec_ref(v_x_4582_);
    return v_res_4586_;
}
pub unsafe fn l_Std_DHashMap_modify___redArg(
    mut v_x_4587_: *mut crate::leanh::LeanObject,
    mut v_x_4588_: *mut crate::leanh::LeanObject,
    mut v_m_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
    mut v_f_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_4587_, v_x_4588_, v_m_4589_, v_a_4590_, v_f_4591_,
    );
    return v___x_4592_;
}
pub unsafe fn l_Std_DHashMap_modify(
    mut v_00_u03b1_4593_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4594_: *mut crate::leanh::LeanObject,
    mut v_x_4595_: *mut crate::leanh::LeanObject,
    mut v_x_4596_: *mut crate::leanh::LeanObject,
    mut v_inst_4597_: *mut crate::leanh::LeanObject,
    mut v_m_4598_: *mut crate::leanh::LeanObject,
    mut v_a_4599_: *mut crate::leanh::LeanObject,
    mut v_f_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4601_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_x_4595_, v_x_4596_, v_m_4598_, v_a_4599_, v_f_4600_,
    );
    return v___x_4601_;
}
pub unsafe fn l_Std_DHashMap_Const_modify___redArg(
    mut v_x_4602_: *mut crate::leanh::LeanObject,
    mut v_x_4603_: *mut crate::leanh::LeanObject,
    mut v_m_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_f_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_4602_, v_x_4603_, v_m_4604_, v_a_4605_, v_f_4606_,
    );
    return v___x_4607_;
}
pub unsafe fn l_Std_DHashMap_Const_modify(
    mut v_00_u03b1_4608_: *mut crate::leanh::LeanObject,
    mut v_x_4609_: *mut crate::leanh::LeanObject,
    mut v_x_4610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4611_: *mut crate::leanh::LeanObject,
    mut v_m_4612_: *mut crate::leanh::LeanObject,
    mut v_a_4613_: *mut crate::leanh::LeanObject,
    mut v_f_4614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_4609_, v_x_4610_, v_m_4612_, v_a_4613_, v_f_4614_,
    );
    return v___x_4615_;
}
pub unsafe fn l_Std_DHashMap_alter___redArg(
    mut v_x_4616_: *mut crate::leanh::LeanObject,
    mut v_x_4617_: *mut crate::leanh::LeanObject,
    mut v_m_4618_: *mut crate::leanh::LeanObject,
    mut v_a_4619_: *mut crate::leanh::LeanObject,
    mut v_f_4620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4621_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_4616_, v_x_4617_, v_m_4618_, v_a_4619_, v_f_4620_,
    );
    return v___x_4621_;
}
pub unsafe fn l_Std_DHashMap_alter(
    mut v_00_u03b1_4622_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4623_: *mut crate::leanh::LeanObject,
    mut v_x_4624_: *mut crate::leanh::LeanObject,
    mut v_x_4625_: *mut crate::leanh::LeanObject,
    mut v_inst_4626_: *mut crate::leanh::LeanObject,
    mut v_m_4627_: *mut crate::leanh::LeanObject,
    mut v_a_4628_: *mut crate::leanh::LeanObject,
    mut v_f_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_x_4624_, v_x_4625_, v_m_4627_, v_a_4628_, v_f_4629_,
    );
    return v___x_4630_;
}
pub unsafe fn l_Std_DHashMap_Const_alter___redArg(
    mut v_x_4631_: *mut crate::leanh::LeanObject,
    mut v_x_4632_: *mut crate::leanh::LeanObject,
    mut v_m_4633_: *mut crate::leanh::LeanObject,
    mut v_a_4634_: *mut crate::leanh::LeanObject,
    mut v_f_4635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_4631_, v_x_4632_, v_m_4633_, v_a_4634_, v_f_4635_,
    );
    return v___x_4636_;
}
pub unsafe fn l_Std_DHashMap_Const_alter(
    mut v_00_u03b1_4637_: *mut crate::leanh::LeanObject,
    mut v_x_4638_: *mut crate::leanh::LeanObject,
    mut v_x_4639_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4640_: *mut crate::leanh::LeanObject,
    mut v_m_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_f_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_4638_, v_x_4639_, v_m_4641_, v_a_4642_, v_f_4643_,
    );
    return v___x_4644_;
}
pub unsafe fn l_Std_DHashMap_insertMany___redArg(
    mut v_x_4645_: *mut crate::leanh::LeanObject,
    mut v_x_4646_: *mut crate::leanh::LeanObject,
    mut v_inst_4647_: *mut crate::leanh::LeanObject,
    mut v_m_4648_: *mut crate::leanh::LeanObject,
    mut v_l_4649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4650_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v_inst_4647_,
        v_x_4645_,
        v_x_4646_,
        v_m_4648_,
        v_l_4649_,
    );
    return v___x_4650_;
}
pub unsafe fn l_Std_DHashMap_insertMany(
    mut v_00_u03b1_4651_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4652_: *mut crate::leanh::LeanObject,
    mut v_x_4653_: *mut crate::leanh::LeanObject,
    mut v_x_4654_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4655_: *mut crate::leanh::LeanObject,
    mut v_inst_4656_: *mut crate::leanh::LeanObject,
    mut v_m_4657_: *mut crate::leanh::LeanObject,
    mut v_l_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4659_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v_inst_4656_,
        v_x_4653_,
        v_x_4654_,
        v_m_4657_,
        v_l_4658_,
    );
    return v___x_4659_;
}
pub unsafe fn l_Std_DHashMap_Const_insertMany___redArg(
    mut v_x_4660_: *mut crate::leanh::LeanObject,
    mut v_x_4661_: *mut crate::leanh::LeanObject,
    mut v_inst_4662_: *mut crate::leanh::LeanObject,
    mut v_m_4663_: *mut crate::leanh::LeanObject,
    mut v_l_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v_inst_4662_,
        v_x_4660_,
        v_x_4661_,
        v_m_4663_,
        v_l_4664_,
    );
    return v___x_4665_;
}
pub unsafe fn l_Std_DHashMap_Const_insertMany(
    mut v_00_u03b1_4666_: *mut crate::leanh::LeanObject,
    mut v_x_4667_: *mut crate::leanh::LeanObject,
    mut v_x_4668_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4669_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4670_: *mut crate::leanh::LeanObject,
    mut v_inst_4671_: *mut crate::leanh::LeanObject,
    mut v_m_4672_: *mut crate::leanh::LeanObject,
    mut v_l_4673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v_inst_4671_,
        v_x_4667_,
        v_x_4668_,
        v_m_4672_,
        v_l_4673_,
    );
    return v___x_4674_;
}
pub unsafe fn l_Std_DHashMap_Const_insertManyIfNewUnit___redArg(
    mut v_x_4675_: *mut crate::leanh::LeanObject,
    mut v_x_4676_: *mut crate::leanh::LeanObject,
    mut v_inst_4677_: *mut crate::leanh::LeanObject,
    mut v_m_4678_: *mut crate::leanh::LeanObject,
    mut v_l_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v_inst_4677_,
        v_x_4675_,
        v_x_4676_,
        v_m_4678_,
        v_l_4679_,
    );
    return v___x_4680_;
}
pub unsafe fn l_Std_DHashMap_Const_insertManyIfNewUnit(
    mut v_00_u03b1_4681_: *mut crate::leanh::LeanObject,
    mut v_x_4682_: *mut crate::leanh::LeanObject,
    mut v_x_4683_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4684_: *mut crate::leanh::LeanObject,
    mut v_inst_4685_: *mut crate::leanh::LeanObject,
    mut v_m_4686_: *mut crate::leanh::LeanObject,
    mut v_l_4687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v_inst_4685_,
        v_x_4682_,
        v_x_4683_,
        v_m_4686_,
        v_l_4687_,
    );
    return v___x_4688_;
}
pub unsafe fn l_Std_DHashMap_toArray___redArg___lam__0(
    mut v_x1_4689_: *mut crate::leanh::LeanObject,
    mut v_x2_4690_: *mut crate::leanh::LeanObject,
    mut v_x3_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4692_, 0, v_x2_4690_);
    crate::leanh::lean_ctor_set(v___x_4692_, 1, v_x3_4691_);
    v___x_4693_ = lean_array_push(v_x1_4689_, v___x_4692_);
    return v___x_4693_;
}
pub unsafe fn l_Std_DHashMap_toArray___redArg___lam__1(
    mut v___x_4694_: *mut crate::leanh::LeanObject,
    mut v___f_4695_: *mut crate::leanh::LeanObject,
    mut v_acc_4696_: *mut crate::leanh::LeanObject,
    mut v_l_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4698_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4694_,
        v___f_4695_,
        v_acc_4696_,
        v_l_4697_,
    );
    return v___x_4698_;
}
pub unsafe fn l_Std_DHashMap_toArray___redArg(
    mut v_m_4703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: u8 = 0;
    v_size_4704_ = crate::leanh::lean_ctor_get(v_m_4703_, 0);
    crate::leanh::lean_inc(v_size_4704_);
    v_buckets_4705_ = crate::leanh::lean_ctor_get(v_m_4703_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4705_);
    crate::leanh::lean_dec_ref(v_m_4703_);
    v___x_4706_ = lean_mk_empty_array_with_capacity(v_size_4704_);
    crate::leanh::lean_dec(v_size_4704_);
    v___x_4707_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_4708_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4709_ = lean_array_get_size(v_buckets_4705_);
    v___x_4710_ = lean_nat_dec_lt(v___x_4708_, v___x_4709_);
    if v___x_4710_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4705_);
        return v___x_4706_;
    } else {
        let mut v___f_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4712_: u8 = 0;
        v___f_4711_ = l_Std_DHashMap_toArray___redArg___closed__1;
        v___x_4712_ = lean_nat_dec_le(v___x_4709_, v___x_4709_);
        if v___x_4712_ == 0 {
            if v___x_4710_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4705_);
                return v___x_4706_;
            } else {
                let mut v___x_4713_: usize = 0;
                let mut v___x_4714_: usize = 0;
                let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4713_ = 0usize;
                v___x_4714_ = lean_usize_of_nat(v___x_4709_);
                v___x_4715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4707_,
                    v___f_4711_,
                    v_buckets_4705_,
                    v___x_4713_,
                    v___x_4714_,
                    v___x_4706_,
                );
                return v___x_4715_;
            }
        } else {
            let mut v___x_4716_: usize = 0;
            let mut v___x_4717_: usize = 0;
            let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4716_ = 0usize;
            v___x_4717_ = lean_usize_of_nat(v___x_4709_);
            v___x_4718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4707_,
                v___f_4711_,
                v_buckets_4705_,
                v___x_4716_,
                v___x_4717_,
                v___x_4706_,
            );
            return v___x_4718_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_toArray(
    mut v_00_u03b1_4719_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4720_: *mut crate::leanh::LeanObject,
    mut v_x_4721_: *mut crate::leanh::LeanObject,
    mut v_x_4722_: *mut crate::leanh::LeanObject,
    mut v_m_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: u8 = 0;
    v_size_4724_ = crate::leanh::lean_ctor_get(v_m_4723_, 0);
    crate::leanh::lean_inc(v_size_4724_);
    v_buckets_4725_ = crate::leanh::lean_ctor_get(v_m_4723_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4725_);
    crate::leanh::lean_dec_ref(v_m_4723_);
    v___x_4726_ = lean_mk_empty_array_with_capacity(v_size_4724_);
    crate::leanh::lean_dec(v_size_4724_);
    v___x_4727_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_4728_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4729_ = lean_array_get_size(v_buckets_4725_);
    v___x_4730_ = lean_nat_dec_lt(v___x_4728_, v___x_4729_);
    if v___x_4730_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4725_);
        return v___x_4726_;
    } else {
        let mut v___f_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4732_: u8 = 0;
        v___f_4731_ = l_Std_DHashMap_toArray___redArg___closed__1;
        v___x_4732_ = lean_nat_dec_le(v___x_4729_, v___x_4729_);
        if v___x_4732_ == 0 {
            if v___x_4730_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4725_);
                return v___x_4726_;
            } else {
                let mut v___x_4733_: usize = 0;
                let mut v___x_4734_: usize = 0;
                let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4733_ = 0usize;
                v___x_4734_ = lean_usize_of_nat(v___x_4729_);
                v___x_4735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4727_,
                    v___f_4731_,
                    v_buckets_4725_,
                    v___x_4733_,
                    v___x_4734_,
                    v___x_4726_,
                );
                return v___x_4735_;
            }
        } else {
            let mut v___x_4736_: usize = 0;
            let mut v___x_4737_: usize = 0;
            let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4736_ = 0usize;
            v___x_4737_ = lean_usize_of_nat(v___x_4729_);
            v___x_4738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4727_,
                v___f_4731_,
                v_buckets_4725_,
                v___x_4736_,
                v___x_4737_,
                v___x_4726_,
            );
            return v___x_4738_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_toArray___boxed(
    mut v_00_u03b1_4739_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4740_: *mut crate::leanh::LeanObject,
    mut v_x_4741_: *mut crate::leanh::LeanObject,
    mut v_x_4742_: *mut crate::leanh::LeanObject,
    mut v_m_4743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4744_ = l_Std_DHashMap_toArray(
        v_00_u03b1_4739_,
        v_00_u03b2_4740_,
        v_x_4741_,
        v_x_4742_,
        v_m_4743_,
    );
    crate::leanh::lean_dec_ref(v_x_4742_);
    crate::leanh::lean_dec_ref(v_x_4741_);
    return v_res_4744_;
}
pub unsafe fn l_Std_DHashMap_Const_toArray___redArg___lam__0(
    mut v_x1_4745_: *mut crate::leanh::LeanObject,
    mut v_x2_4746_: *mut crate::leanh::LeanObject,
    mut v_x3_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4748_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4748_, 0, v_x2_4746_);
    crate::leanh::lean_ctor_set(v___x_4748_, 1, v_x3_4747_);
    v___x_4749_ = lean_array_push(v_x1_4745_, v___x_4748_);
    return v___x_4749_;
}
pub unsafe fn l_Std_DHashMap_Const_toArray___redArg___lam__1(
    mut v___x_4750_: *mut crate::leanh::LeanObject,
    mut v___f_4751_: *mut crate::leanh::LeanObject,
    mut v_acc_4752_: *mut crate::leanh::LeanObject,
    mut v_l_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4754_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4750_,
        v___f_4751_,
        v_acc_4752_,
        v_l_4753_,
    );
    return v___x_4754_;
}
pub unsafe fn l_Std_DHashMap_Const_toArray___redArg(
    mut v_m_4759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: u8 = 0;
    v_size_4760_ = crate::leanh::lean_ctor_get(v_m_4759_, 0);
    crate::leanh::lean_inc(v_size_4760_);
    v_buckets_4761_ = crate::leanh::lean_ctor_get(v_m_4759_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4761_);
    crate::leanh::lean_dec_ref(v_m_4759_);
    v___x_4762_ = lean_mk_empty_array_with_capacity(v_size_4760_);
    crate::leanh::lean_dec(v_size_4760_);
    v___x_4763_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_4764_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4765_ = lean_array_get_size(v_buckets_4761_);
    v___x_4766_ = lean_nat_dec_lt(v___x_4764_, v___x_4765_);
    if v___x_4766_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4761_);
        return v___x_4762_;
    } else {
        let mut v___f_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4768_: u8 = 0;
        v___f_4767_ = l_Std_DHashMap_Const_toArray___redArg___closed__1;
        v___x_4768_ = lean_nat_dec_le(v___x_4765_, v___x_4765_);
        if v___x_4768_ == 0 {
            if v___x_4766_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4761_);
                return v___x_4762_;
            } else {
                let mut v___x_4769_: usize = 0;
                let mut v___x_4770_: usize = 0;
                let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4769_ = 0usize;
                v___x_4770_ = lean_usize_of_nat(v___x_4765_);
                v___x_4771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4763_,
                    v___f_4767_,
                    v_buckets_4761_,
                    v___x_4769_,
                    v___x_4770_,
                    v___x_4762_,
                );
                return v___x_4771_;
            }
        } else {
            let mut v___x_4772_: usize = 0;
            let mut v___x_4773_: usize = 0;
            let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4772_ = 0usize;
            v___x_4773_ = lean_usize_of_nat(v___x_4765_);
            v___x_4774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4763_,
                v___f_4767_,
                v_buckets_4761_,
                v___x_4772_,
                v___x_4773_,
                v___x_4762_,
            );
            return v___x_4774_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Const_toArray(
    mut v_00_u03b1_4775_: *mut crate::leanh::LeanObject,
    mut v_x_4776_: *mut crate::leanh::LeanObject,
    mut v_x_4777_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4778_: *mut crate::leanh::LeanObject,
    mut v_m_4779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    v_size_4780_ = crate::leanh::lean_ctor_get(v_m_4779_, 0);
    crate::leanh::lean_inc(v_size_4780_);
    v_buckets_4781_ = crate::leanh::lean_ctor_get(v_m_4779_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4781_);
    crate::leanh::lean_dec_ref(v_m_4779_);
    v___x_4782_ = lean_mk_empty_array_with_capacity(v_size_4780_);
    crate::leanh::lean_dec(v_size_4780_);
    v___x_4783_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_4784_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4785_ = lean_array_get_size(v_buckets_4781_);
    v___x_4786_ = lean_nat_dec_lt(v___x_4784_, v___x_4785_);
    if v___x_4786_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4781_);
        return v___x_4782_;
    } else {
        let mut v___f_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4788_: u8 = 0;
        v___f_4787_ = l_Std_DHashMap_Const_toArray___redArg___closed__1;
        v___x_4788_ = lean_nat_dec_le(v___x_4785_, v___x_4785_);
        if v___x_4788_ == 0 {
            if v___x_4786_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4781_);
                return v___x_4782_;
            } else {
                let mut v___x_4789_: usize = 0;
                let mut v___x_4790_: usize = 0;
                let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4789_ = 0usize;
                v___x_4790_ = lean_usize_of_nat(v___x_4785_);
                v___x_4791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4783_,
                    v___f_4787_,
                    v_buckets_4781_,
                    v___x_4789_,
                    v___x_4790_,
                    v___x_4782_,
                );
                return v___x_4791_;
            }
        } else {
            let mut v___x_4792_: usize = 0;
            let mut v___x_4793_: usize = 0;
            let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4792_ = 0usize;
            v___x_4793_ = lean_usize_of_nat(v___x_4785_);
            v___x_4794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4783_,
                v___f_4787_,
                v_buckets_4781_,
                v___x_4792_,
                v___x_4793_,
                v___x_4782_,
            );
            return v___x_4794_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Const_toArray___boxed(
    mut v_00_u03b1_4795_: *mut crate::leanh::LeanObject,
    mut v_x_4796_: *mut crate::leanh::LeanObject,
    mut v_x_4797_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4798_: *mut crate::leanh::LeanObject,
    mut v_m_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4800_ = l_Std_DHashMap_Const_toArray(
        v_00_u03b1_4795_,
        v_x_4796_,
        v_x_4797_,
        v_00_u03b2_4798_,
        v_m_4799_,
    );
    crate::leanh::lean_dec_ref(v_x_4797_);
    crate::leanh::lean_dec_ref(v_x_4796_);
    return v_res_4800_;
}
pub unsafe fn l_Std_DHashMap_keysArray___redArg___lam__0(
    mut v_x1_4801_: *mut crate::leanh::LeanObject,
    mut v_x2_4802_: *mut crate::leanh::LeanObject,
    mut v_x3_4803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = lean_array_push(v_x1_4801_, v_x2_4802_);
    return v___x_4804_;
}
pub unsafe fn l_Std_DHashMap_keysArray___redArg___lam__0___boxed(
    mut v_x1_4805_: *mut crate::leanh::LeanObject,
    mut v_x2_4806_: *mut crate::leanh::LeanObject,
    mut v_x3_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4808_ = l_Std_DHashMap_keysArray___redArg___lam__0(v_x1_4805_, v_x2_4806_, v_x3_4807_);
    crate::leanh::lean_dec(v_x3_4807_);
    return v_res_4808_;
}
pub unsafe fn l_Std_DHashMap_keysArray___redArg___lam__1(
    mut v___x_4809_: *mut crate::leanh::LeanObject,
    mut v___f_4810_: *mut crate::leanh::LeanObject,
    mut v_acc_4811_: *mut crate::leanh::LeanObject,
    mut v_l_4812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4813_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4809_,
        v___f_4810_,
        v_acc_4811_,
        v_l_4812_,
    );
    return v___x_4813_;
}
pub unsafe fn l_Std_DHashMap_keysArray___redArg(
    mut v_m_4818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: u8 = 0;
    v_size_4819_ = crate::leanh::lean_ctor_get(v_m_4818_, 0);
    crate::leanh::lean_inc(v_size_4819_);
    v_buckets_4820_ = crate::leanh::lean_ctor_get(v_m_4818_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4820_);
    crate::leanh::lean_dec_ref(v_m_4818_);
    v___x_4821_ = lean_mk_empty_array_with_capacity(v_size_4819_);
    crate::leanh::lean_dec(v_size_4819_);
    v___x_4822_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_4823_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4824_ = lean_array_get_size(v_buckets_4820_);
    v___x_4825_ = lean_nat_dec_lt(v___x_4823_, v___x_4824_);
    if v___x_4825_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4820_);
        return v___x_4821_;
    } else {
        let mut v___f_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4827_: u8 = 0;
        v___f_4826_ = l_Std_DHashMap_keysArray___redArg___closed__1;
        v___x_4827_ = lean_nat_dec_le(v___x_4824_, v___x_4824_);
        if v___x_4827_ == 0 {
            if v___x_4825_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4820_);
                return v___x_4821_;
            } else {
                let mut v___x_4828_: usize = 0;
                let mut v___x_4829_: usize = 0;
                let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4828_ = 0usize;
                v___x_4829_ = lean_usize_of_nat(v___x_4824_);
                v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4822_,
                    v___f_4826_,
                    v_buckets_4820_,
                    v___x_4828_,
                    v___x_4829_,
                    v___x_4821_,
                );
                return v___x_4830_;
            }
        } else {
            let mut v___x_4831_: usize = 0;
            let mut v___x_4832_: usize = 0;
            let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4831_ = 0usize;
            v___x_4832_ = lean_usize_of_nat(v___x_4824_);
            v___x_4833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4822_,
                v___f_4826_,
                v_buckets_4820_,
                v___x_4831_,
                v___x_4832_,
                v___x_4821_,
            );
            return v___x_4833_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_keysArray(
    mut v_00_u03b1_4834_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4835_: *mut crate::leanh::LeanObject,
    mut v_x_4836_: *mut crate::leanh::LeanObject,
    mut v_x_4837_: *mut crate::leanh::LeanObject,
    mut v_m_4838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: u8 = 0;
    v_size_4839_ = crate::leanh::lean_ctor_get(v_m_4838_, 0);
    crate::leanh::lean_inc(v_size_4839_);
    v_buckets_4840_ = crate::leanh::lean_ctor_get(v_m_4838_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4840_);
    crate::leanh::lean_dec_ref(v_m_4838_);
    v___x_4841_ = lean_mk_empty_array_with_capacity(v_size_4839_);
    crate::leanh::lean_dec(v_size_4839_);
    v___x_4842_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_4843_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4844_ = lean_array_get_size(v_buckets_4840_);
    v___x_4845_ = lean_nat_dec_lt(v___x_4843_, v___x_4844_);
    if v___x_4845_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4840_);
        return v___x_4841_;
    } else {
        let mut v___f_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4847_: u8 = 0;
        v___f_4846_ = l_Std_DHashMap_keysArray___redArg___closed__1;
        v___x_4847_ = lean_nat_dec_le(v___x_4844_, v___x_4844_);
        if v___x_4847_ == 0 {
            if v___x_4845_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4840_);
                return v___x_4841_;
            } else {
                let mut v___x_4848_: usize = 0;
                let mut v___x_4849_: usize = 0;
                let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4848_ = 0usize;
                v___x_4849_ = lean_usize_of_nat(v___x_4844_);
                v___x_4850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4842_,
                    v___f_4846_,
                    v_buckets_4840_,
                    v___x_4848_,
                    v___x_4849_,
                    v___x_4841_,
                );
                return v___x_4850_;
            }
        } else {
            let mut v___x_4851_: usize = 0;
            let mut v___x_4852_: usize = 0;
            let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4851_ = 0usize;
            v___x_4852_ = lean_usize_of_nat(v___x_4844_);
            v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4842_,
                v___f_4846_,
                v_buckets_4840_,
                v___x_4851_,
                v___x_4852_,
                v___x_4841_,
            );
            return v___x_4853_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_keysArray___boxed(
    mut v_00_u03b1_4854_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4855_: *mut crate::leanh::LeanObject,
    mut v_x_4856_: *mut crate::leanh::LeanObject,
    mut v_x_4857_: *mut crate::leanh::LeanObject,
    mut v_m_4858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4859_ = l_Std_DHashMap_keysArray(
        v_00_u03b1_4854_,
        v_00_u03b2_4855_,
        v_x_4856_,
        v_x_4857_,
        v_m_4858_,
    );
    crate::leanh::lean_dec_ref(v_x_4857_);
    crate::leanh::lean_dec_ref(v_x_4856_);
    return v_res_4859_;
}
pub unsafe fn l_Std_DHashMap_all___redArg___lam__0(
    mut v_p_4860_: *mut crate::leanh::LeanObject,
    mut v___x_4861_: *mut crate::leanh::LeanObject,
    mut v___x_4862_: *mut crate::leanh::LeanObject,
    mut v_a_4863_: *mut crate::leanh::LeanObject,
    mut v_b_4864_: *mut crate::leanh::LeanObject,
    mut v_acc_4865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: u8 = 0;
    v___x_4866_ = crate::leanh::lean_apply_2(v_p_4860_, v_a_4863_, v_b_4864_);
    v___x_4867_ = (crate::leanh::lean_unbox(v___x_4866_) as u8);
    if v___x_4867_ == 0 {
        let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_4862_);
        v___x_4868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4868_, 0, v___x_4866_);
        v___x_4869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4869_, 0, v___x_4868_);
        crate::leanh::lean_ctor_set(v___x_4869_, 1, v___x_4861_);
        v___x_4870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4870_, 0, v___x_4869_);
        return v___x_4870_;
    } else {
        let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4871_, 0, v___x_4862_);
        return v___x_4871_;
    }
}
pub unsafe fn l_Std_DHashMap_all___redArg___lam__0___boxed(
    mut v_p_4872_: *mut crate::leanh::LeanObject,
    mut v___x_4873_: *mut crate::leanh::LeanObject,
    mut v___x_4874_: *mut crate::leanh::LeanObject,
    mut v_a_4875_: *mut crate::leanh::LeanObject,
    mut v_b_4876_: *mut crate::leanh::LeanObject,
    mut v_acc_4877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4878_ = l_Std_DHashMap_all___redArg___lam__0(
        v_p_4872_,
        v___x_4873_,
        v___x_4874_,
        v_a_4875_,
        v_b_4876_,
        v_acc_4877_,
    );
    crate::leanh::lean_dec_ref(v_acc_4877_);
    return v_res_4878_;
}
pub unsafe fn l_Std_DHashMap_all___redArg___lam__1(
    mut v___x_4879_: *mut crate::leanh::LeanObject,
    mut v___f_4880_: *mut crate::leanh::LeanObject,
    mut v_a_4881_: *mut crate::leanh::LeanObject,
    mut v_x_4882_: *mut crate::leanh::LeanObject,
    mut v___y_4883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4884_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_4879_, v___f_4880_, v_a_4881_, v___y_4883_);
    return v___x_4884_;
}
pub unsafe fn l_Std_DHashMap_all___redArg(
    mut v_m_4888_: *mut crate::leanh::LeanObject,
    mut v_p_4889_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4896_: usize = 0;
    let mut v___x_4897_: usize = 0;
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4890_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4891_ = crate::leanh::lean_ctor_get(v_m_4888_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4891_);
    crate::leanh::lean_dec_ref(v_m_4888_);
    v___x_4892_ = crate::leanh::lean_box(0);
    v___x_4893_ = l_Std_DHashMap_all___redArg___closed__0;
    v___f_4894_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4894_, 0, v_p_4889_);
    crate::leanh::lean_closure_set(v___f_4894_, 1, v___x_4892_);
    crate::leanh::lean_closure_set(v___f_4894_, 2, v___x_4893_);
    v___f_4895_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4895_, 0, v___x_4890_);
    crate::leanh::lean_closure_set(v___f_4895_, 1, v___f_4894_);
    v_sz_4896_ = lean_array_size(v_buckets_4891_);
    v___x_4897_ = 0usize;
    v___x_4898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4890_,
        v_buckets_4891_,
        v___f_4895_,
        v_sz_4896_,
        v___x_4897_,
        v___x_4893_,
    );
    v_fst_4899_ = crate::leanh::lean_ctor_get(v___x_4898_, 0);
    crate::leanh::lean_inc(v_fst_4899_);
    crate::leanh::lean_dec(v___x_4898_);
    if crate::leanh::lean_obj_tag(v_fst_4899_) == 0 {
        let mut v___x_4900_: u8 = 0;
        v___x_4900_ = 1;
        return v___x_4900_;
    } else {
        let mut v_val_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4902_: u8 = 0;
        v_val_4901_ = crate::leanh::lean_ctor_get(v_fst_4899_, 0);
        crate::leanh::lean_inc(v_val_4901_);
        crate::leanh::lean_dec_ref_known(v_fst_4899_, 1);
        v___x_4902_ = (crate::leanh::lean_unbox(v_val_4901_) as u8);
        crate::leanh::lean_dec(v_val_4901_);
        return v___x_4902_;
    }
}
pub unsafe fn l_Std_DHashMap_all___redArg___boxed(
    mut v_m_4903_: *mut crate::leanh::LeanObject,
    mut v_p_4904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4905_: u8 = 0;
    let mut v_r_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4905_ = l_Std_DHashMap_all___redArg(v_m_4903_, v_p_4904_);
    v_r_4906_ = crate::leanh::lean_box((v_res_4905_) as usize);
    return v_r_4906_;
}
pub unsafe fn l_Std_DHashMap_all(
    mut v_00_u03b1_4907_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4908_: *mut crate::leanh::LeanObject,
    mut v_x_4909_: *mut crate::leanh::LeanObject,
    mut v_x_4910_: *mut crate::leanh::LeanObject,
    mut v_m_4911_: *mut crate::leanh::LeanObject,
    mut v_p_4912_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4919_: usize = 0;
    let mut v___x_4920_: usize = 0;
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4913_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4914_ = crate::leanh::lean_ctor_get(v_m_4911_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4914_);
    crate::leanh::lean_dec_ref(v_m_4911_);
    v___x_4915_ = crate::leanh::lean_box(0);
    v___x_4916_ = l_Std_DHashMap_all___redArg___closed__0;
    v___f_4917_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4917_, 0, v_p_4912_);
    crate::leanh::lean_closure_set(v___f_4917_, 1, v___x_4915_);
    crate::leanh::lean_closure_set(v___f_4917_, 2, v___x_4916_);
    v___f_4918_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4918_, 0, v___x_4913_);
    crate::leanh::lean_closure_set(v___f_4918_, 1, v___f_4917_);
    v_sz_4919_ = lean_array_size(v_buckets_4914_);
    v___x_4920_ = 0usize;
    v___x_4921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4913_,
        v_buckets_4914_,
        v___f_4918_,
        v_sz_4919_,
        v___x_4920_,
        v___x_4916_,
    );
    v_fst_4922_ = crate::leanh::lean_ctor_get(v___x_4921_, 0);
    crate::leanh::lean_inc(v_fst_4922_);
    crate::leanh::lean_dec(v___x_4921_);
    if crate::leanh::lean_obj_tag(v_fst_4922_) == 0 {
        let mut v___x_4923_: u8 = 0;
        v___x_4923_ = 1;
        return v___x_4923_;
    } else {
        let mut v_val_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4925_: u8 = 0;
        v_val_4924_ = crate::leanh::lean_ctor_get(v_fst_4922_, 0);
        crate::leanh::lean_inc(v_val_4924_);
        crate::leanh::lean_dec_ref_known(v_fst_4922_, 1);
        v___x_4925_ = (crate::leanh::lean_unbox(v_val_4924_) as u8);
        crate::leanh::lean_dec(v_val_4924_);
        return v___x_4925_;
    }
}
pub unsafe fn l_Std_DHashMap_all___boxed(
    mut v_00_u03b1_4926_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4927_: *mut crate::leanh::LeanObject,
    mut v_x_4928_: *mut crate::leanh::LeanObject,
    mut v_x_4929_: *mut crate::leanh::LeanObject,
    mut v_m_4930_: *mut crate::leanh::LeanObject,
    mut v_p_4931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4932_: u8 = 0;
    let mut v_r_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4932_ = l_Std_DHashMap_all(
        v_00_u03b1_4926_,
        v_00_u03b2_4927_,
        v_x_4928_,
        v_x_4929_,
        v_m_4930_,
        v_p_4931_,
    );
    crate::leanh::lean_dec_ref(v_x_4929_);
    crate::leanh::lean_dec_ref(v_x_4928_);
    v_r_4933_ = crate::leanh::lean_box((v_res_4932_) as usize);
    return v_r_4933_;
}
pub unsafe fn l_Std_DHashMap_any___redArg___lam__0(
    mut v_p_4934_: *mut crate::leanh::LeanObject,
    mut v___x_4935_: *mut crate::leanh::LeanObject,
    mut v___x_4936_: *mut crate::leanh::LeanObject,
    mut v_a_4937_: *mut crate::leanh::LeanObject,
    mut v_b_4938_: *mut crate::leanh::LeanObject,
    mut v_acc_4939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: u8 = 0;
    v___x_4940_ = crate::leanh::lean_apply_2(v_p_4934_, v_a_4937_, v_b_4938_);
    v___x_4941_ = (crate::leanh::lean_unbox(v___x_4940_) as u8);
    if v___x_4941_ == 0 {
        let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4942_, 0, v___x_4935_);
        return v___x_4942_;
    } else {
        let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_4935_);
        v___x_4943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4943_, 0, v___x_4940_);
        v___x_4944_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4944_, 0, v___x_4943_);
        crate::leanh::lean_ctor_set(v___x_4944_, 1, v___x_4936_);
        v___x_4945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4945_, 0, v___x_4944_);
        return v___x_4945_;
    }
}
pub unsafe fn l_Std_DHashMap_any___redArg___lam__0___boxed(
    mut v_p_4946_: *mut crate::leanh::LeanObject,
    mut v___x_4947_: *mut crate::leanh::LeanObject,
    mut v___x_4948_: *mut crate::leanh::LeanObject,
    mut v_a_4949_: *mut crate::leanh::LeanObject,
    mut v_b_4950_: *mut crate::leanh::LeanObject,
    mut v_acc_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4952_ = l_Std_DHashMap_any___redArg___lam__0(
        v_p_4946_,
        v___x_4947_,
        v___x_4948_,
        v_a_4949_,
        v_b_4950_,
        v_acc_4951_,
    );
    crate::leanh::lean_dec_ref(v_acc_4951_);
    return v_res_4952_;
}
pub unsafe fn l_Std_DHashMap_any___redArg(
    mut v_m_4953_: *mut crate::leanh::LeanObject,
    mut v_p_4954_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4961_: usize = 0;
    let mut v___x_4962_: usize = 0;
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4955_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4956_ = crate::leanh::lean_ctor_get(v_m_4953_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4956_);
    crate::leanh::lean_dec_ref(v_m_4953_);
    v___x_4957_ = crate::leanh::lean_box(0);
    v___x_4958_ = l_Std_DHashMap_all___redArg___closed__0;
    v___f_4959_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4959_, 0, v_p_4954_);
    crate::leanh::lean_closure_set(v___f_4959_, 1, v___x_4958_);
    crate::leanh::lean_closure_set(v___f_4959_, 2, v___x_4957_);
    v___f_4960_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4960_, 0, v___x_4955_);
    crate::leanh::lean_closure_set(v___f_4960_, 1, v___f_4959_);
    v_sz_4961_ = lean_array_size(v_buckets_4956_);
    v___x_4962_ = 0usize;
    v___x_4963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4955_,
        v_buckets_4956_,
        v___f_4960_,
        v_sz_4961_,
        v___x_4962_,
        v___x_4958_,
    );
    v_fst_4964_ = crate::leanh::lean_ctor_get(v___x_4963_, 0);
    crate::leanh::lean_inc(v_fst_4964_);
    crate::leanh::lean_dec(v___x_4963_);
    if crate::leanh::lean_obj_tag(v_fst_4964_) == 0 {
        let mut v___x_4965_: u8 = 0;
        v___x_4965_ = 0;
        return v___x_4965_;
    } else {
        let mut v_val_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4967_: u8 = 0;
        v_val_4966_ = crate::leanh::lean_ctor_get(v_fst_4964_, 0);
        crate::leanh::lean_inc(v_val_4966_);
        crate::leanh::lean_dec_ref_known(v_fst_4964_, 1);
        v___x_4967_ = (crate::leanh::lean_unbox(v_val_4966_) as u8);
        crate::leanh::lean_dec(v_val_4966_);
        return v___x_4967_;
    }
}
pub unsafe fn l_Std_DHashMap_any___redArg___boxed(
    mut v_m_4968_: *mut crate::leanh::LeanObject,
    mut v_p_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4970_: u8 = 0;
    let mut v_r_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4970_ = l_Std_DHashMap_any___redArg(v_m_4968_, v_p_4969_);
    v_r_4971_ = crate::leanh::lean_box((v_res_4970_) as usize);
    return v_r_4971_;
}
pub unsafe fn l_Std_DHashMap_any(
    mut v_00_u03b1_4972_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4973_: *mut crate::leanh::LeanObject,
    mut v_x_4974_: *mut crate::leanh::LeanObject,
    mut v_x_4975_: *mut crate::leanh::LeanObject,
    mut v_m_4976_: *mut crate::leanh::LeanObject,
    mut v_p_4977_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4984_: usize = 0;
    let mut v___x_4985_: usize = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4978_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_4979_ = crate::leanh::lean_ctor_get(v_m_4976_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4979_);
    crate::leanh::lean_dec_ref(v_m_4976_);
    v___x_4980_ = crate::leanh::lean_box(0);
    v___x_4981_ = l_Std_DHashMap_all___redArg___closed__0;
    v___f_4982_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4982_, 0, v_p_4977_);
    crate::leanh::lean_closure_set(v___f_4982_, 1, v___x_4981_);
    crate::leanh::lean_closure_set(v___f_4982_, 2, v___x_4980_);
    v___f_4983_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4983_, 0, v___x_4978_);
    crate::leanh::lean_closure_set(v___f_4983_, 1, v___f_4982_);
    v_sz_4984_ = lean_array_size(v_buckets_4979_);
    v___x_4985_ = 0usize;
    v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4978_,
        v_buckets_4979_,
        v___f_4983_,
        v_sz_4984_,
        v___x_4985_,
        v___x_4981_,
    );
    v_fst_4987_ = crate::leanh::lean_ctor_get(v___x_4986_, 0);
    crate::leanh::lean_inc(v_fst_4987_);
    crate::leanh::lean_dec(v___x_4986_);
    if crate::leanh::lean_obj_tag(v_fst_4987_) == 0 {
        let mut v___x_4988_: u8 = 0;
        v___x_4988_ = 0;
        return v___x_4988_;
    } else {
        let mut v_val_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4990_: u8 = 0;
        v_val_4989_ = crate::leanh::lean_ctor_get(v_fst_4987_, 0);
        crate::leanh::lean_inc(v_val_4989_);
        crate::leanh::lean_dec_ref_known(v_fst_4987_, 1);
        v___x_4990_ = (crate::leanh::lean_unbox(v_val_4989_) as u8);
        crate::leanh::lean_dec(v_val_4989_);
        return v___x_4990_;
    }
}
pub unsafe fn l_Std_DHashMap_any___boxed(
    mut v_00_u03b1_4991_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4992_: *mut crate::leanh::LeanObject,
    mut v_x_4993_: *mut crate::leanh::LeanObject,
    mut v_x_4994_: *mut crate::leanh::LeanObject,
    mut v_m_4995_: *mut crate::leanh::LeanObject,
    mut v_p_4996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4997_: u8 = 0;
    let mut v_r_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4997_ = l_Std_DHashMap_any(
        v_00_u03b1_4991_,
        v_00_u03b2_4992_,
        v_x_4993_,
        v_x_4994_,
        v_m_4995_,
        v_p_4996_,
    );
    crate::leanh::lean_dec_ref(v_x_4994_);
    crate::leanh::lean_dec_ref(v_x_4993_);
    v_r_4998_ = crate::leanh::lean_box((v_res_4997_) as usize);
    return v_r_4998_;
}
pub unsafe fn l_Std_DHashMap_union___redArg___lam__0(
    mut v_inst_4999_: *mut crate::leanh::LeanObject,
    mut v_inst_5000_: *mut crate::leanh::LeanObject,
    mut v_a_5001_: *mut crate::leanh::LeanObject,
    mut v_b_5002_: *mut crate::leanh::LeanObject,
    mut v_acc_5003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_5004_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_4999_,
        v_inst_5000_,
        v_acc_5003_,
        v_a_5001_,
        v_b_5002_,
    );
    v___x_5005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5005_, 0, v_r_5004_);
    return v___x_5005_;
}
pub unsafe fn l_Std_DHashMap_union___redArg___lam__1(
    mut v___x_5006_: *mut crate::leanh::LeanObject,
    mut v___f_5007_: *mut crate::leanh::LeanObject,
    mut v_a_5008_: *mut crate::leanh::LeanObject,
    mut v_x_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5011_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_5006_, v___f_5007_, v_a_5008_, v___y_5010_);
    return v___x_5011_;
}
pub unsafe fn l_Std_DHashMap_union___redArg(
    mut v_inst_5014_: *mut crate::leanh::LeanObject,
    mut v_inst_5015_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5016_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: u8 = 0;
    v_size_5018_ = crate::leanh::lean_ctor_get(v_m_u2081_5016_, 0);
    v_buckets_5019_ = crate::leanh::lean_ctor_get(v_m_u2081_5016_, 1);
    v_size_5020_ = crate::leanh::lean_ctor_get(v_m_u2082_5017_, 0);
    v___x_5021_ = lean_nat_dec_le(v_size_5018_, v_size_5020_);
    if v___x_5021_ == 0 {
        let mut v___f_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5022_ = l_Std_DHashMap_union___redArg___closed__0;
        v___x_5023_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_5022_,
            v_inst_5014_,
            v_inst_5015_,
            v_m_u2081_5016_,
            v_m_u2082_5017_,
        );
        return v___x_5023_;
    } else {
        let mut v___f_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5027_: usize = 0;
        let mut v___x_5028_: usize = 0;
        let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_5019_);
        crate::leanh::lean_dec_ref(v_m_u2081_5016_);
        v___f_5024_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5024_, 0, v_inst_5014_);
        crate::leanh::lean_closure_set(v___f_5024_, 1, v_inst_5015_);
        v___x_5025_ = l_Std_DHashMap_keys___redArg___closed__9;
        v___f_5026_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5026_, 0, v___x_5025_);
        crate::leanh::lean_closure_set(v___f_5026_, 1, v___f_5024_);
        v_sz_5027_ = lean_array_size(v_buckets_5019_);
        v___x_5028_ = 0usize;
        v___x_5029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5025_,
            v_buckets_5019_,
            v___f_5026_,
            v_sz_5027_,
            v___x_5028_,
            v_m_u2082_5017_,
        );
        return v___x_5029_;
    }
}
pub unsafe fn l_Std_DHashMap_union(
    mut v_00_u03b1_5030_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5031_: *mut crate::leanh::LeanObject,
    mut v_inst_5032_: *mut crate::leanh::LeanObject,
    mut v_inst_5033_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5034_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    v_size_5036_ = crate::leanh::lean_ctor_get(v_m_u2081_5034_, 0);
    v_buckets_5037_ = crate::leanh::lean_ctor_get(v_m_u2081_5034_, 1);
    v_size_5038_ = crate::leanh::lean_ctor_get(v_m_u2082_5035_, 0);
    v___x_5039_ = lean_nat_dec_le(v_size_5036_, v_size_5038_);
    if v___x_5039_ == 0 {
        let mut v___f_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5040_ = l_Std_DHashMap_union___redArg___closed__0;
        v___x_5041_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_5040_,
            v_inst_5032_,
            v_inst_5033_,
            v_m_u2081_5034_,
            v_m_u2082_5035_,
        );
        return v___x_5041_;
    } else {
        let mut v___f_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5045_: usize = 0;
        let mut v___x_5046_: usize = 0;
        let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_5037_);
        crate::leanh::lean_dec_ref(v_m_u2081_5034_);
        v___f_5042_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5042_, 0, v_inst_5032_);
        crate::leanh::lean_closure_set(v___f_5042_, 1, v_inst_5033_);
        v___x_5043_ = l_Std_DHashMap_keys___redArg___closed__9;
        v___f_5044_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5044_, 0, v___x_5043_);
        crate::leanh::lean_closure_set(v___f_5044_, 1, v___f_5042_);
        v_sz_5045_ = lean_array_size(v_buckets_5037_);
        v___x_5046_ = 0usize;
        v___x_5047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5043_,
            v_buckets_5037_,
            v___f_5044_,
            v_sz_5045_,
            v___x_5046_,
            v_m_u2082_5035_,
        );
        return v___x_5047_;
    }
}
pub unsafe fn l_Std_DHashMap_inter___redArg(
    mut v_inst_5048_: *mut crate::leanh::LeanObject,
    mut v_inst_5049_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5050_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_inst_5048_,
        v_inst_5049_,
        v_m_u2081_5050_,
        v_m_u2082_5051_,
    );
    return v___x_5052_;
}
pub unsafe fn l_Std_DHashMap_inter(
    mut v_00_u03b1_5053_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5054_: *mut crate::leanh::LeanObject,
    mut v_inst_5055_: *mut crate::leanh::LeanObject,
    mut v_inst_5056_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5057_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5059_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_inst_5055_,
        v_inst_5056_,
        v_m_u2081_5057_,
        v_m_u2082_5058_,
    );
    return v___x_5059_;
}
pub unsafe fn l_Std_DHashMap_diff___redArg___lam__0(
    mut v_inst_5060_: *mut crate::leanh::LeanObject,
    mut v_inst_5061_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5062_: *mut crate::leanh::LeanObject,
    mut v___x_5063_: u8,
    mut v_k_5064_: *mut crate::leanh::LeanObject,
    mut v_x_5065_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5066_: u8 = 0;
    v___x_5066_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_5060_,
        v_inst_5061_,
        v_m_u2082_5062_,
        v_k_5064_,
    );
    if v___x_5066_ == 0 {
        return v___x_5063_;
    } else {
        let mut v___x_5067_: u8 = 0;
        v___x_5067_ = 0;
        return v___x_5067_;
    }
}
pub unsafe fn l_Std_DHashMap_diff___redArg___lam__0___boxed(
    mut v_inst_5068_: *mut crate::leanh::LeanObject,
    mut v_inst_5069_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5070_: *mut crate::leanh::LeanObject,
    mut v___x_5071_: *mut crate::leanh::LeanObject,
    mut v_k_5072_: *mut crate::leanh::LeanObject,
    mut v_x_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_76__boxed_5074_: u8 = 0;
    let mut v_res_5075_: u8 = 0;
    let mut v_r_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_76__boxed_5074_ = (crate::leanh::lean_unbox(v___x_5071_) as u8);
    v_res_5075_ = l_Std_DHashMap_diff___redArg___lam__0(
        v_inst_5068_,
        v_inst_5069_,
        v_m_u2082_5070_,
        v___x_76__boxed_5074_,
        v_k_5072_,
        v_x_5073_,
    );
    crate::leanh::lean_dec(v_x_5073_);
    crate::leanh::lean_dec_ref(v_m_u2082_5070_);
    v_r_5076_ = crate::leanh::lean_box((v_res_5075_) as usize);
    return v_r_5076_;
}
pub unsafe fn l_Std_DHashMap_diff___redArg(
    mut v_inst_5077_: *mut crate::leanh::LeanObject,
    mut v_inst_5078_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5079_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: u8 = 0;
    v_size_5081_ = crate::leanh::lean_ctor_get(v_m_u2081_5079_, 0);
    v_size_5082_ = crate::leanh::lean_ctor_get(v_m_u2082_5080_, 0);
    v___x_5083_ = lean_nat_dec_le(v_size_5081_, v_size_5082_);
    if v___x_5083_ == 0 {
        let mut v___f_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5084_ = l_Std_DHashMap_union___redArg___closed__0;
        v___x_5085_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_5084_,
            v_inst_5077_,
            v_inst_5078_,
            v_m_u2081_5079_,
            v_m_u2082_5080_,
        );
        return v___x_5085_;
    } else {
        let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5086_ = crate::leanh::lean_box((v___x_5083_) as usize);
        v___f_5087_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5087_, 0, v_inst_5077_);
        crate::leanh::lean_closure_set(v___f_5087_, 1, v_inst_5078_);
        crate::leanh::lean_closure_set(v___f_5087_, 2, v_m_u2082_5080_);
        crate::leanh::lean_closure_set(v___f_5087_, 3, v___x_5086_);
        v___x_5088_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_5087_, v_m_u2081_5079_);
        return v___x_5088_;
    }
}
pub unsafe fn l_Std_DHashMap_diff(
    mut v_00_u03b1_5089_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5090_: *mut crate::leanh::LeanObject,
    mut v_inst_5091_: *mut crate::leanh::LeanObject,
    mut v_inst_5092_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5093_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: u8 = 0;
    v_size_5095_ = crate::leanh::lean_ctor_get(v_m_u2081_5093_, 0);
    v_size_5096_ = crate::leanh::lean_ctor_get(v_m_u2082_5094_, 0);
    v___x_5097_ = lean_nat_dec_le(v_size_5095_, v_size_5096_);
    if v___x_5097_ == 0 {
        let mut v___f_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5098_ = l_Std_DHashMap_union___redArg___closed__0;
        v___x_5099_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_5098_,
            v_inst_5091_,
            v_inst_5092_,
            v_m_u2081_5093_,
            v_m_u2082_5094_,
        );
        return v___x_5099_;
    } else {
        let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5100_ = crate::leanh::lean_box((v___x_5097_) as usize);
        v___f_5101_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5101_, 0, v_inst_5091_);
        crate::leanh::lean_closure_set(v___f_5101_, 1, v_inst_5092_);
        crate::leanh::lean_closure_set(v___f_5101_, 2, v_m_u2082_5094_);
        crate::leanh::lean_closure_set(v___f_5101_, 3, v___x_5100_);
        v___x_5102_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_5101_, v_m_u2081_5093_);
        return v___x_5102_;
    }
}
pub unsafe fn l_Std_DHashMap_instUnion___redArg(
    mut v_inst_5103_: *mut crate::leanh::LeanObject,
    mut v_inst_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5105_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_union as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5105_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5105_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5105_, 2, v_inst_5103_);
    crate::leanh::lean_closure_set(v___x_5105_, 3, v_inst_5104_);
    return v___x_5105_;
}
pub unsafe fn l_Std_DHashMap_instUnion(
    mut v_00_u03b1_5106_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5107_: *mut crate::leanh::LeanObject,
    mut v_inst_5108_: *mut crate::leanh::LeanObject,
    mut v_inst_5109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5110_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_union as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5110_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5110_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5110_, 2, v_inst_5108_);
    crate::leanh::lean_closure_set(v___x_5110_, 3, v_inst_5109_);
    return v___x_5110_;
}
pub unsafe fn l_Std_DHashMap_instInter___redArg(
    mut v_inst_5111_: *mut crate::leanh::LeanObject,
    mut v_inst_5112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5113_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_inter as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5113_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5113_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5113_, 2, v_inst_5111_);
    crate::leanh::lean_closure_set(v___x_5113_, 3, v_inst_5112_);
    return v___x_5113_;
}
pub unsafe fn l_Std_DHashMap_instInter(
    mut v_00_u03b1_5114_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5115_: *mut crate::leanh::LeanObject,
    mut v_inst_5116_: *mut crate::leanh::LeanObject,
    mut v_inst_5117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5118_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_inter as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5118_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5118_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5118_, 2, v_inst_5116_);
    crate::leanh::lean_closure_set(v___x_5118_, 3, v_inst_5117_);
    return v___x_5118_;
}
pub unsafe fn l_Std_DHashMap_instSDiff___redArg(
    mut v_inst_5119_: *mut crate::leanh::LeanObject,
    mut v_inst_5120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5121_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_diff as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5121_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5121_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5121_, 2, v_inst_5119_);
    crate::leanh::lean_closure_set(v___x_5121_, 3, v_inst_5120_);
    return v___x_5121_;
}
pub unsafe fn l_Std_DHashMap_instSDiff(
    mut v_00_u03b1_5122_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5123_: *mut crate::leanh::LeanObject,
    mut v_inst_5124_: *mut crate::leanh::LeanObject,
    mut v_inst_5125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5126_ =
        crate::leanh::lean_alloc_closure(l_Std_DHashMap_diff as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5126_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5126_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5126_, 2, v_inst_5124_);
    crate::leanh::lean_closure_set(v___x_5126_, 3, v_inst_5125_);
    return v___x_5126_;
}
pub unsafe fn l_Std_DHashMap_beq___redArg(
    mut v_x_5127_: *mut crate::leanh::LeanObject,
    mut v_x_5128_: *mut crate::leanh::LeanObject,
    mut v_inst_5129_: *mut crate::leanh::LeanObject,
    mut v_a_5130_: *mut crate::leanh::LeanObject,
    mut v_b_5131_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5132_: u8 = 0;
    v___x_5132_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_x_5127_,
        v_x_5128_,
        v_inst_5129_,
        v_a_5130_,
        v_b_5131_,
    );
    return v___x_5132_;
}
pub unsafe fn l_Std_DHashMap_beq___redArg___boxed(
    mut v_x_5133_: *mut crate::leanh::LeanObject,
    mut v_x_5134_: *mut crate::leanh::LeanObject,
    mut v_inst_5135_: *mut crate::leanh::LeanObject,
    mut v_a_5136_: *mut crate::leanh::LeanObject,
    mut v_b_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5138_: u8 = 0;
    let mut v_r_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5138_ =
        l_Std_DHashMap_beq___redArg(v_x_5133_, v_x_5134_, v_inst_5135_, v_a_5136_, v_b_5137_);
    v_r_5139_ = crate::leanh::lean_box((v_res_5138_) as usize);
    return v_r_5139_;
}
pub unsafe fn l_Std_DHashMap_beq(
    mut v_00_u03b1_5140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5141_: *mut crate::leanh::LeanObject,
    mut v_x_5142_: *mut crate::leanh::LeanObject,
    mut v_x_5143_: *mut crate::leanh::LeanObject,
    mut v_inst_5144_: *mut crate::leanh::LeanObject,
    mut v_inst_5145_: *mut crate::leanh::LeanObject,
    mut v_a_5146_: *mut crate::leanh::LeanObject,
    mut v_b_5147_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5148_: u8 = 0;
    v___x_5148_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_x_5142_,
        v_x_5143_,
        v_inst_5145_,
        v_a_5146_,
        v_b_5147_,
    );
    return v___x_5148_;
}
pub unsafe fn l_Std_DHashMap_beq___boxed(
    mut v_00_u03b1_5149_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5150_: *mut crate::leanh::LeanObject,
    mut v_x_5151_: *mut crate::leanh::LeanObject,
    mut v_x_5152_: *mut crate::leanh::LeanObject,
    mut v_inst_5153_: *mut crate::leanh::LeanObject,
    mut v_inst_5154_: *mut crate::leanh::LeanObject,
    mut v_a_5155_: *mut crate::leanh::LeanObject,
    mut v_b_5156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5157_: u8 = 0;
    let mut v_r_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Std_DHashMap_beq(
        v_00_u03b1_5149_,
        v_00_u03b2_5150_,
        v_x_5151_,
        v_x_5152_,
        v_inst_5153_,
        v_inst_5154_,
        v_a_5155_,
        v_b_5156_,
    );
    v_r_5158_ = crate::leanh::lean_box((v_res_5157_) as usize);
    return v_r_5158_;
}
pub unsafe fn l_Std_DHashMap_instBEqOfLawfulBEq___redArg(
    mut v_x_5159_: *mut crate::leanh::LeanObject,
    mut v_x_5160_: *mut crate::leanh::LeanObject,
    mut v_inst_5161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5162_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_5162_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5162_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5162_, 2, v_x_5159_);
    crate::leanh::lean_closure_set(v___x_5162_, 3, v_x_5160_);
    crate::leanh::lean_closure_set(v___x_5162_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5162_, 5, v_inst_5161_);
    return v___x_5162_;
}
pub unsafe fn l_Std_DHashMap_instBEqOfLawfulBEq(
    mut v_00_u03b1_5163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5164_: *mut crate::leanh::LeanObject,
    mut v_x_5165_: *mut crate::leanh::LeanObject,
    mut v_x_5166_: *mut crate::leanh::LeanObject,
    mut v_inst_5167_: *mut crate::leanh::LeanObject,
    mut v_inst_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5169_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___x_5169_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5169_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5169_, 2, v_x_5165_);
    crate::leanh::lean_closure_set(v___x_5169_, 3, v_x_5166_);
    crate::leanh::lean_closure_set(v___x_5169_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5169_, 5, v_inst_5168_);
    return v___x_5169_;
}
pub unsafe fn l_Std_DHashMap_Const_beq___redArg(
    mut v_x_5170_: *mut crate::leanh::LeanObject,
    mut v_inst_5171_: *mut crate::leanh::LeanObject,
    mut v_inst_5172_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5173_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5174_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5175_: u8 = 0;
    v___x_5175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_5171_,
        v_x_5170_,
        v_inst_5172_,
        v_m_u2081_5173_,
        v_m_u2082_5174_,
    );
    return v___x_5175_;
}
pub unsafe fn l_Std_DHashMap_Const_beq___redArg___boxed(
    mut v_x_5176_: *mut crate::leanh::LeanObject,
    mut v_inst_5177_: *mut crate::leanh::LeanObject,
    mut v_inst_5178_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5179_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5181_: u8 = 0;
    let mut v_r_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5181_ = l_Std_DHashMap_Const_beq___redArg(
        v_x_5176_,
        v_inst_5177_,
        v_inst_5178_,
        v_m_u2081_5179_,
        v_m_u2082_5180_,
    );
    v_r_5182_ = crate::leanh::lean_box((v_res_5181_) as usize);
    return v_r_5182_;
}
pub unsafe fn l_Std_DHashMap_Const_beq(
    mut v_00_u03b1_5183_: *mut crate::leanh::LeanObject,
    mut v_x_5184_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5185_: *mut crate::leanh::LeanObject,
    mut v_inst_5186_: *mut crate::leanh::LeanObject,
    mut v_inst_5187_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5188_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5189_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5190_: u8 = 0;
    v___x_5190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_5186_,
        v_x_5184_,
        v_inst_5187_,
        v_m_u2081_5188_,
        v_m_u2082_5189_,
    );
    return v___x_5190_;
}
pub unsafe fn l_Std_DHashMap_Const_beq___boxed(
    mut v_00_u03b1_5191_: *mut crate::leanh::LeanObject,
    mut v_x_5192_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5193_: *mut crate::leanh::LeanObject,
    mut v_inst_5194_: *mut crate::leanh::LeanObject,
    mut v_inst_5195_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_5196_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_5197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5198_: u8 = 0;
    let mut v_r_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Std_DHashMap_Const_beq(
        v_00_u03b1_5191_,
        v_x_5192_,
        v_00_u03b2_5193_,
        v_inst_5194_,
        v_inst_5195_,
        v_m_u2081_5196_,
        v_m_u2082_5197_,
    );
    v_r_5199_ = crate::leanh::lean_box((v_res_5198_) as usize);
    return v_r_5199_;
}
pub unsafe fn l_Std_DHashMap_partition___redArg___lam__0(
    mut v_f_5200_: *mut crate::leanh::LeanObject,
    mut v_x_5201_: *mut crate::leanh::LeanObject,
    mut v_x_5202_: *mut crate::leanh::LeanObject,
    mut v_x1_5203_: *mut crate::leanh::LeanObject,
    mut v_x2_5204_: *mut crate::leanh::LeanObject,
    mut v_x3_5205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5210_: u8 = 0;
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: u8 = 0;
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5206_ = crate::leanh::lean_ctor_get(v_x1_5203_, 0);
                v_snd_5207_ = crate::leanh::lean_ctor_get(v_x1_5203_, 1);
                v_isSharedCheck_5221_ = (!crate::leanh::lean_is_exclusive(v_x1_5203_)) as u8;
                if v_isSharedCheck_5221_ == 0 {
                    v___x_5209_ = v_x1_5203_;
                    v_isShared_5210_ = v_isSharedCheck_5221_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5207_);
                    crate::leanh::lean_inc(v_fst_5206_);
                    crate::leanh::lean_dec(v_x1_5203_);
                    v___x_5209_ = crate::leanh::lean_box(0);
                    v_isShared_5210_ = v_isSharedCheck_5221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x3_5205_);
                crate::leanh::lean_inc(v_x2_5204_);
                v___x_5211_ = crate::leanh::lean_apply_2(v_f_5200_, v_x2_5204_, v_x3_5205_);
                v___x_5212_ = (crate::leanh::lean_unbox(v___x_5211_) as u8);
                if v___x_5212_ == 0 {
                    v___x_5213_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_x_5201_,
                        v_x_5202_,
                        v_snd_5207_,
                        v_x2_5204_,
                        v_x3_5205_,
                    );
                    if v_isShared_5210_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5209_, 1, v___x_5213_);
                        v___x_5215_ = v___x_5209_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5216_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_fst_5206_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 1, v___x_5213_);
                        v___x_5215_ = v_reuseFailAlloc_5216_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_x_5201_,
                        v_x_5202_,
                        v_fst_5206_,
                        v_x2_5204_,
                        v_x3_5205_,
                    );
                    if v_isShared_5210_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5209_, 0, v___x_5217_);
                        v___x_5219_ = v___x_5209_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5220_, 0, v___x_5217_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5220_, 1, v_snd_5207_);
                        v___x_5219_ = v_reuseFailAlloc_5220_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5215_;
            }
            3 => {
                return v___x_5219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_partition___redArg___lam__1(
    mut v___x_5222_: *mut crate::leanh::LeanObject,
    mut v___f_5223_: *mut crate::leanh::LeanObject,
    mut v_acc_5224_: *mut crate::leanh::LeanObject,
    mut v_l_5225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_5222_,
        v___f_5223_,
        v_acc_5224_,
        v_l_5225_,
    );
    return v___x_5226_;
}
pub unsafe fn _init_l_Std_DHashMap_partition___redArg___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5227_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5228_, 0, v___x_5227_);
    crate::leanh::lean_ctor_set(v___x_5228_, 1, v___x_5227_);
    return v___x_5228_;
}
pub unsafe fn l_Std_DHashMap_partition___redArg(
    mut v_x_5229_: *mut crate::leanh::LeanObject,
    mut v_x_5230_: *mut crate::leanh::LeanObject,
    mut v_f_5231_: *mut crate::leanh::LeanObject,
    mut v_m_5232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: u8 = 0;
    v___x_5233_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5234_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_partition___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_DHashMap_partition___redArg___closed__0_once),
        _init_l_Std_DHashMap_partition___redArg___closed__0,
    );
    v___x_5235_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_5236_ = crate::leanh::lean_ctor_get(v_m_5232_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5236_);
    crate::leanh::lean_dec_ref(v_m_5232_);
    v___x_5237_ = lean_array_get_size(v_buckets_5236_);
    v___x_5238_ = lean_nat_dec_lt(v___x_5233_, v___x_5237_);
    if v___x_5238_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5236_);
        crate::leanh::lean_dec_ref(v_f_5231_);
        crate::leanh::lean_dec_ref(v_x_5230_);
        crate::leanh::lean_dec_ref(v_x_5229_);
        return v___x_5234_;
    } else {
        let mut v___f_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5241_: u8 = 0;
        v___f_5239_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
            6,
            3,
        );
        crate::leanh::lean_closure_set(v___f_5239_, 0, v_f_5231_);
        crate::leanh::lean_closure_set(v___f_5239_, 1, v_x_5229_);
        crate::leanh::lean_closure_set(v___f_5239_, 2, v_x_5230_);
        v___f_5240_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_partition___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5240_, 0, v___x_5235_);
        crate::leanh::lean_closure_set(v___f_5240_, 1, v___f_5239_);
        v___x_5241_ = lean_nat_dec_le(v___x_5237_, v___x_5237_);
        if v___x_5241_ == 0 {
            if v___x_5238_ == 0 {
                crate::leanh::lean_dec_ref(v___f_5240_);
                crate::leanh::lean_dec_ref(v_buckets_5236_);
                return v___x_5234_;
            } else {
                let mut v___x_5242_: usize = 0;
                let mut v___x_5243_: usize = 0;
                let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5242_ = 0usize;
                v___x_5243_ = lean_usize_of_nat(v___x_5237_);
                v___x_5244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5235_,
                    v___f_5240_,
                    v_buckets_5236_,
                    v___x_5242_,
                    v___x_5243_,
                    v___x_5234_,
                );
                return v___x_5244_;
            }
        } else {
            let mut v___x_5245_: usize = 0;
            let mut v___x_5246_: usize = 0;
            let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5245_ = 0usize;
            v___x_5246_ = lean_usize_of_nat(v___x_5237_);
            v___x_5247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5235_,
                v___f_5240_,
                v_buckets_5236_,
                v___x_5245_,
                v___x_5246_,
                v___x_5234_,
            );
            return v___x_5247_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_partition(
    mut v_00_u03b1_5248_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5249_: *mut crate::leanh::LeanObject,
    mut v_x_5250_: *mut crate::leanh::LeanObject,
    mut v_x_5251_: *mut crate::leanh::LeanObject,
    mut v_f_5252_: *mut crate::leanh::LeanObject,
    mut v_m_5253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    v___x_5254_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5255_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_partition___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_DHashMap_partition___redArg___closed__0_once),
        _init_l_Std_DHashMap_partition___redArg___closed__0,
    );
    v___x_5256_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_5257_ = crate::leanh::lean_ctor_get(v_m_5253_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5257_);
    crate::leanh::lean_dec_ref(v_m_5253_);
    v___x_5258_ = lean_array_get_size(v_buckets_5257_);
    v___x_5259_ = lean_nat_dec_lt(v___x_5254_, v___x_5258_);
    if v___x_5259_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5257_);
        crate::leanh::lean_dec_ref(v_f_5252_);
        crate::leanh::lean_dec_ref(v_x_5251_);
        crate::leanh::lean_dec_ref(v_x_5250_);
        return v___x_5255_;
    } else {
        let mut v___f_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5262_: u8 = 0;
        v___f_5260_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
            6,
            3,
        );
        crate::leanh::lean_closure_set(v___f_5260_, 0, v_f_5252_);
        crate::leanh::lean_closure_set(v___f_5260_, 1, v_x_5250_);
        crate::leanh::lean_closure_set(v___f_5260_, 2, v_x_5251_);
        v___f_5261_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_partition___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5261_, 0, v___x_5256_);
        crate::leanh::lean_closure_set(v___f_5261_, 1, v___f_5260_);
        v___x_5262_ = lean_nat_dec_le(v___x_5258_, v___x_5258_);
        if v___x_5262_ == 0 {
            if v___x_5259_ == 0 {
                crate::leanh::lean_dec_ref(v___f_5261_);
                crate::leanh::lean_dec_ref(v_buckets_5257_);
                return v___x_5255_;
            } else {
                let mut v___x_5263_: usize = 0;
                let mut v___x_5264_: usize = 0;
                let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5263_ = 0usize;
                v___x_5264_ = lean_usize_of_nat(v___x_5258_);
                v___x_5265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5256_,
                    v___f_5261_,
                    v_buckets_5257_,
                    v___x_5263_,
                    v___x_5264_,
                    v___x_5255_,
                );
                return v___x_5265_;
            }
        } else {
            let mut v___x_5266_: usize = 0;
            let mut v___x_5267_: usize = 0;
            let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5266_ = 0usize;
            v___x_5267_ = lean_usize_of_nat(v___x_5258_);
            v___x_5268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5256_,
                v___f_5261_,
                v_buckets_5257_,
                v___x_5266_,
                v___x_5267_,
                v___x_5255_,
            );
            return v___x_5268_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_values___redArg___lam__0(
    mut v_a_5269_: *mut crate::leanh::LeanObject,
    mut v_b_5270_: *mut crate::leanh::LeanObject,
    mut v_d_5271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5272_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5272_, 0, v_b_5270_);
    crate::leanh::lean_ctor_set(v___x_5272_, 1, v_d_5271_);
    return v___x_5272_;
}
pub unsafe fn l_Std_DHashMap_values___redArg___lam__0___boxed(
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_b_5274_: *mut crate::leanh::LeanObject,
    mut v_d_5275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5276_ = l_Std_DHashMap_values___redArg___lam__0(v_a_5273_, v_b_5274_, v_d_5275_);
    crate::leanh::lean_dec(v_a_5273_);
    return v_res_5276_;
}
pub unsafe fn l_Std_DHashMap_values___redArg(
    mut v_m_5281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    v___x_5282_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_5283_ = crate::leanh::lean_ctor_get(v_m_5281_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5283_);
    crate::leanh::lean_dec_ref(v_m_5281_);
    v___x_5284_ = crate::leanh::lean_box(0);
    v___x_5285_ = lean_array_get_size(v_buckets_5283_);
    v___x_5286_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5287_ = lean_nat_dec_lt(v___x_5286_, v___x_5285_);
    if v___x_5287_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5283_);
        return v___x_5284_;
    } else {
        let mut v___f_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5289_: usize = 0;
        let mut v___x_5290_: usize = 0;
        let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5288_ = l_Std_DHashMap_values___redArg___closed__1;
        v___x_5289_ = lean_usize_of_nat(v___x_5285_);
        v___x_5290_ = 0usize;
        v___x_5291_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5282_,
            v___f_5288_,
            v_buckets_5283_,
            v___x_5289_,
            v___x_5290_,
            v___x_5284_,
        );
        return v___x_5291_;
    }
}
pub unsafe fn l_Std_DHashMap_values(
    mut v_00_u03b1_5292_: *mut crate::leanh::LeanObject,
    mut v_x_5293_: *mut crate::leanh::LeanObject,
    mut v_x_5294_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5295_: *mut crate::leanh::LeanObject,
    mut v_m_5296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: u8 = 0;
    v___x_5297_ = l_Std_DHashMap_keys___redArg___closed__9;
    v_buckets_5298_ = crate::leanh::lean_ctor_get(v_m_5296_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5298_);
    crate::leanh::lean_dec_ref(v_m_5296_);
    v___x_5299_ = crate::leanh::lean_box(0);
    v___x_5300_ = lean_array_get_size(v_buckets_5298_);
    v___x_5301_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5302_ = lean_nat_dec_lt(v___x_5301_, v___x_5300_);
    if v___x_5302_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5298_);
        return v___x_5299_;
    } else {
        let mut v___f_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5304_: usize = 0;
        let mut v___x_5305_: usize = 0;
        let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_5303_ = l_Std_DHashMap_values___redArg___closed__1;
        v___x_5304_ = lean_usize_of_nat(v___x_5300_);
        v___x_5305_ = 0usize;
        v___x_5306_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5297_,
            v___f_5303_,
            v_buckets_5298_,
            v___x_5304_,
            v___x_5305_,
            v___x_5299_,
        );
        return v___x_5306_;
    }
}
pub unsafe fn l_Std_DHashMap_values___boxed(
    mut v_00_u03b1_5307_: *mut crate::leanh::LeanObject,
    mut v_x_5308_: *mut crate::leanh::LeanObject,
    mut v_x_5309_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5310_: *mut crate::leanh::LeanObject,
    mut v_m_5311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Std_DHashMap_values(
        v_00_u03b1_5307_,
        v_x_5308_,
        v_x_5309_,
        v_00_u03b2_5310_,
        v_m_5311_,
    );
    crate::leanh::lean_dec_ref(v_x_5309_);
    crate::leanh::lean_dec_ref(v_x_5308_);
    return v_res_5312_;
}
pub unsafe fn l_Std_DHashMap_valuesArray___redArg___lam__0(
    mut v_x1_5313_: *mut crate::leanh::LeanObject,
    mut v_x2_5314_: *mut crate::leanh::LeanObject,
    mut v_x3_5315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5316_ = lean_array_push(v_x1_5313_, v_x3_5315_);
    return v___x_5316_;
}
pub unsafe fn l_Std_DHashMap_valuesArray___redArg___lam__0___boxed(
    mut v_x1_5317_: *mut crate::leanh::LeanObject,
    mut v_x2_5318_: *mut crate::leanh::LeanObject,
    mut v_x3_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5320_ = l_Std_DHashMap_valuesArray___redArg___lam__0(v_x1_5317_, v_x2_5318_, v_x3_5319_);
    crate::leanh::lean_dec(v_x2_5318_);
    return v_res_5320_;
}
pub unsafe fn l_Std_DHashMap_valuesArray___redArg(
    mut v_m_5325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: u8 = 0;
    v_size_5326_ = crate::leanh::lean_ctor_get(v_m_5325_, 0);
    crate::leanh::lean_inc(v_size_5326_);
    v_buckets_5327_ = crate::leanh::lean_ctor_get(v_m_5325_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5327_);
    crate::leanh::lean_dec_ref(v_m_5325_);
    v___x_5328_ = lean_mk_empty_array_with_capacity(v_size_5326_);
    crate::leanh::lean_dec(v_size_5326_);
    v___x_5329_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_5330_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5331_ = lean_array_get_size(v_buckets_5327_);
    v___x_5332_ = lean_nat_dec_lt(v___x_5330_, v___x_5331_);
    if v___x_5332_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5327_);
        return v___x_5328_;
    } else {
        let mut v___f_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5334_: u8 = 0;
        v___f_5333_ = l_Std_DHashMap_valuesArray___redArg___closed__1;
        v___x_5334_ = lean_nat_dec_le(v___x_5331_, v___x_5331_);
        if v___x_5334_ == 0 {
            if v___x_5332_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_5327_);
                return v___x_5328_;
            } else {
                let mut v___x_5335_: usize = 0;
                let mut v___x_5336_: usize = 0;
                let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5335_ = 0usize;
                v___x_5336_ = lean_usize_of_nat(v___x_5331_);
                v___x_5337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5329_,
                    v___f_5333_,
                    v_buckets_5327_,
                    v___x_5335_,
                    v___x_5336_,
                    v___x_5328_,
                );
                return v___x_5337_;
            }
        } else {
            let mut v___x_5338_: usize = 0;
            let mut v___x_5339_: usize = 0;
            let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5338_ = 0usize;
            v___x_5339_ = lean_usize_of_nat(v___x_5331_);
            v___x_5340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5329_,
                v___f_5333_,
                v_buckets_5327_,
                v___x_5338_,
                v___x_5339_,
                v___x_5328_,
            );
            return v___x_5340_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_valuesArray(
    mut v_00_u03b1_5341_: *mut crate::leanh::LeanObject,
    mut v_x_5342_: *mut crate::leanh::LeanObject,
    mut v_x_5343_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5344_: *mut crate::leanh::LeanObject,
    mut v_m_5345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    v_size_5346_ = crate::leanh::lean_ctor_get(v_m_5345_, 0);
    crate::leanh::lean_inc(v_size_5346_);
    v_buckets_5347_ = crate::leanh::lean_ctor_get(v_m_5345_, 1);
    crate::leanh::lean_inc_ref(v_buckets_5347_);
    crate::leanh::lean_dec_ref(v_m_5345_);
    v___x_5348_ = lean_mk_empty_array_with_capacity(v_size_5346_);
    crate::leanh::lean_dec(v_size_5346_);
    v___x_5349_ = l_Std_DHashMap_keys___redArg___closed__9;
    v___x_5350_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5351_ = lean_array_get_size(v_buckets_5347_);
    v___x_5352_ = lean_nat_dec_lt(v___x_5350_, v___x_5351_);
    if v___x_5352_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_5347_);
        return v___x_5348_;
    } else {
        let mut v___f_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5354_: u8 = 0;
        v___f_5353_ = l_Std_DHashMap_valuesArray___redArg___closed__1;
        v___x_5354_ = lean_nat_dec_le(v___x_5351_, v___x_5351_);
        if v___x_5354_ == 0 {
            if v___x_5352_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_5347_);
                return v___x_5348_;
            } else {
                let mut v___x_5355_: usize = 0;
                let mut v___x_5356_: usize = 0;
                let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5355_ = 0usize;
                v___x_5356_ = lean_usize_of_nat(v___x_5351_);
                v___x_5357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5349_,
                    v___f_5353_,
                    v_buckets_5347_,
                    v___x_5355_,
                    v___x_5356_,
                    v___x_5348_,
                );
                return v___x_5357_;
            }
        } else {
            let mut v___x_5358_: usize = 0;
            let mut v___x_5359_: usize = 0;
            let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5358_ = 0usize;
            v___x_5359_ = lean_usize_of_nat(v___x_5351_);
            v___x_5360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5349_,
                v___f_5353_,
                v_buckets_5347_,
                v___x_5358_,
                v___x_5359_,
                v___x_5348_,
            );
            return v___x_5360_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_valuesArray___boxed(
    mut v_00_u03b1_5361_: *mut crate::leanh::LeanObject,
    mut v_x_5362_: *mut crate::leanh::LeanObject,
    mut v_x_5363_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5364_: *mut crate::leanh::LeanObject,
    mut v_m_5365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5366_ = l_Std_DHashMap_valuesArray(
        v_00_u03b1_5361_,
        v_x_5362_,
        v_x_5363_,
        v_00_u03b2_5364_,
        v_m_5365_,
    );
    crate::leanh::lean_dec_ref(v_x_5363_);
    crate::leanh::lean_dec_ref(v_x_5362_);
    return v_res_5366_;
}
pub unsafe fn l_Std_DHashMap_Const_unitOfArray___redArg(
    mut v_inst_5371_: *mut crate::leanh::LeanObject,
    mut v_inst_5372_: *mut crate::leanh::LeanObject,
    mut v_l_5373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5374_ = l_Std_DHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_5375_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5376_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_5374_,
        v_inst_5371_,
        v_inst_5372_,
        v___x_5375_,
        v_l_5373_,
    );
    return v___x_5376_;
}
pub unsafe fn l_Std_DHashMap_Const_unitOfArray(
    mut v_00_u03b1_5377_: *mut crate::leanh::LeanObject,
    mut v_inst_5378_: *mut crate::leanh::LeanObject,
    mut v_inst_5379_: *mut crate::leanh::LeanObject,
    mut v_l_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5381_ = l_Std_DHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_5382_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5383_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_5381_,
        v_inst_5378_,
        v_inst_5379_,
        v___x_5382_,
        v_l_5380_,
    );
    return v___x_5383_;
}
pub unsafe fn l_Std_DHashMap_Internal_numBuckets___redArg(
    mut v_m_5384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5385_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_5384_);
    return v___x_5385_;
}
pub unsafe fn l_Std_DHashMap_Internal_numBuckets___redArg___boxed(
    mut v_m_5386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5387_ = l_Std_DHashMap_Internal_numBuckets___redArg(v_m_5386_);
    crate::leanh::lean_dec_ref(v_m_5386_);
    return v_res_5387_;
}
pub unsafe fn l_Std_DHashMap_Internal_numBuckets(
    mut v_00_u03b1_5388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5389_: *mut crate::leanh::LeanObject,
    mut v_x_5390_: *mut crate::leanh::LeanObject,
    mut v_x_5391_: *mut crate::leanh::LeanObject,
    mut v_m_5392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5393_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_5392_);
    return v___x_5393_;
}
pub unsafe fn l_Std_DHashMap_Internal_numBuckets___boxed(
    mut v_00_u03b1_5394_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5395_: *mut crate::leanh::LeanObject,
    mut v_x_5396_: *mut crate::leanh::LeanObject,
    mut v_x_5397_: *mut crate::leanh::LeanObject,
    mut v_m_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5399_ = l_Std_DHashMap_Internal_numBuckets(
        v_00_u03b1_5394_,
        v_00_u03b2_5395_,
        v_x_5396_,
        v_x_5397_,
        v_m_5398_,
    );
    crate::leanh::lean_dec_ref(v_m_5398_);
    crate::leanh::lean_dec_ref(v_x_5397_);
    crate::leanh::lean_dec_ref(v_x_5396_);
    return v_res_5399_;
}
pub unsafe fn l_Std_DHashMap_instRepr___redArg___lam__2(
    mut v___x_5403_: *mut crate::leanh::LeanObject,
    mut v___f_5404_: *mut crate::leanh::LeanObject,
    mut v_m_5405_: *mut crate::leanh::LeanObject,
    mut v_prec_5406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: u8 = 0;
    let mut v___f_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: usize = 0;
    let mut v___x_5426_: usize = 0;
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v_unused_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5407_ = l_Std_DHashMap_keys___redArg___closed__9;
                v_buckets_5408_ = crate::leanh::lean_ctor_get(v_m_5405_, 1);
                v_isSharedCheck_5428_ = (!crate::leanh::lean_is_exclusive(v_m_5405_)) as u8;
                if v_isSharedCheck_5428_ == 0 {
                    v_unused_5429_ = crate::leanh::lean_ctor_get(v_m_5405_, 0);
                    crate::leanh::lean_dec(v_unused_5429_);
                    v___x_5410_ = v_m_5405_;
                    v_isShared_5411_ = v_isSharedCheck_5428_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5408_);
                    crate::leanh::lean_dec(v_m_5405_);
                    v___x_5410_ = crate::leanh::lean_box(0);
                    v_isShared_5411_ = v_isSharedCheck_5428_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5412_ = l_Std_DHashMap_instRepr___redArg___lam__2___closed__1;
                v___x_5420_ = crate::leanh::lean_box(0);
                v___x_5421_ = lean_array_get_size(v_buckets_5408_);
                v___x_5422_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5423_ = lean_nat_dec_lt(v___x_5422_, v___x_5421_);
                if v___x_5423_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_5408_);
                    crate::leanh::lean_dec_ref(v___f_5404_);
                    v___y_5414_ = v___x_5420_;
                    state = 2;
                    continue;
                } else {
                    v___f_5424_ = crate::leanh::lean_alloc_closure(
                        l_Std_DHashMap_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_5424_, 0, v___x_5407_);
                    crate::leanh::lean_closure_set(v___f_5424_, 1, v___f_5404_);
                    v___x_5425_ = lean_usize_of_nat(v___x_5421_);
                    v___x_5426_ = 0usize;
                    v___x_5427_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5407_,
                        v___f_5424_,
                        v_buckets_5408_,
                        v___x_5425_,
                        v___x_5426_,
                        v___x_5420_,
                    );
                    v___y_5414_ = v___x_5427_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5415_ = l_List_repr___redArg(v___x_5403_, v___y_5414_);
                if v_isShared_5411_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5410_, 5);
                    crate::leanh::lean_ctor_set(v___x_5410_, 1, v___x_5415_);
                    crate::leanh::lean_ctor_set(v___x_5410_, 0, v___x_5412_);
                    v___x_5417_ = v___x_5410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 1, v___x_5415_);
                    v___x_5417_ = v_reuseFailAlloc_5419_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5418_ = l_Repr_addAppParen(v___x_5417_, v_prec_5406_);
                return v___x_5418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_instRepr___redArg___lam__2___boxed(
    mut v___x_5430_: *mut crate::leanh::LeanObject,
    mut v___f_5431_: *mut crate::leanh::LeanObject,
    mut v_m_5432_: *mut crate::leanh::LeanObject,
    mut v_prec_5433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5434_ = l_Std_DHashMap_instRepr___redArg___lam__2(
        v___x_5430_,
        v___f_5431_,
        v_m_5432_,
        v_prec_5433_,
    );
    crate::leanh::lean_dec(v_prec_5433_);
    return v_res_5434_;
}
pub unsafe fn l_Std_DHashMap_instRepr___redArg(
    mut v_inst_5435_: *mut crate::leanh::LeanObject,
    mut v_inst_5436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5437_ = l_Std_DHashMap_toList___redArg___closed__0;
    v___x_5438_ =
        crate::leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_5438_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5438_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5438_, 2, v_inst_5435_);
    crate::leanh::lean_closure_set(v___x_5438_, 3, v_inst_5436_);
    v___f_5439_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5439_, 0, v___x_5438_);
    crate::leanh::lean_closure_set(v___f_5439_, 1, v___f_5437_);
    return v___f_5439_;
}
pub unsafe fn l_Std_DHashMap_instRepr(
    mut v_00_u03b1_5440_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5441_: *mut crate::leanh::LeanObject,
    mut v_inst_5442_: *mut crate::leanh::LeanObject,
    mut v_inst_5443_: *mut crate::leanh::LeanObject,
    mut v_inst_5444_: *mut crate::leanh::LeanObject,
    mut v_inst_5445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5446_ = l_Std_DHashMap_instRepr___redArg(v_inst_5444_, v_inst_5445_);
    return v___x_5446_;
}
pub unsafe fn l_Std_DHashMap_instRepr___boxed(
    mut v_00_u03b1_5447_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5448_: *mut crate::leanh::LeanObject,
    mut v_inst_5449_: *mut crate::leanh::LeanObject,
    mut v_inst_5450_: *mut crate::leanh::LeanObject,
    mut v_inst_5451_: *mut crate::leanh::LeanObject,
    mut v_inst_5452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5453_ = l_Std_DHashMap_instRepr(
        v_00_u03b1_5447_,
        v_00_u03b2_5448_,
        v_inst_5449_,
        v_inst_5450_,
        v_inst_5451_,
        v_inst_5452_,
    );
    crate::leanh::lean_dec_ref(v_inst_5450_);
    crate::leanh::lean_dec_ref(v_inst_5449_);
    return v_res_5453_;
}
pub unsafe fn l_Std_DHashMap_ofList___redArg(
    mut v_inst_5458_: *mut crate::leanh::LeanObject,
    mut v_inst_5459_: *mut crate::leanh::LeanObject,
    mut v_l_5460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5461_ = l_Std_DHashMap_ofList___redArg___closed__1;
    v___x_5462_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5463_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v___f_5461_,
        v_inst_5458_,
        v_inst_5459_,
        v___x_5462_,
        v_l_5460_,
    );
    return v___x_5463_;
}
pub unsafe fn l_Std_DHashMap_ofList(
    mut v_00_u03b1_5464_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5465_: *mut crate::leanh::LeanObject,
    mut v_inst_5466_: *mut crate::leanh::LeanObject,
    mut v_inst_5467_: *mut crate::leanh::LeanObject,
    mut v_l_5468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5469_ = l_Std_DHashMap_ofList___redArg___closed__1;
    v___x_5470_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5471_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v___f_5469_,
        v_inst_5466_,
        v_inst_5467_,
        v___x_5470_,
        v_l_5468_,
    );
    return v___x_5471_;
}
pub unsafe fn l_Std_DHashMap_ofArray___redArg(
    mut v_inst_5472_: *mut crate::leanh::LeanObject,
    mut v_inst_5473_: *mut crate::leanh::LeanObject,
    mut v_l_5474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5475_ = l_Std_DHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_5476_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5477_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v___f_5475_,
        v_inst_5472_,
        v_inst_5473_,
        v___x_5476_,
        v_l_5474_,
    );
    return v___x_5477_;
}
pub unsafe fn l_Std_DHashMap_ofArray(
    mut v_00_u03b1_5478_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5479_: *mut crate::leanh::LeanObject,
    mut v_inst_5480_: *mut crate::leanh::LeanObject,
    mut v_inst_5481_: *mut crate::leanh::LeanObject,
    mut v_l_5482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5483_ = l_Std_DHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_5484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5485_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v___f_5483_,
        v_inst_5480_,
        v_inst_5481_,
        v___x_5484_,
        v_l_5482_,
    );
    return v___x_5485_;
}
pub unsafe fn l_Std_DHashMap_Const_ofList___redArg(
    mut v_inst_5486_: *mut crate::leanh::LeanObject,
    mut v_inst_5487_: *mut crate::leanh::LeanObject,
    mut v_l_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5489_ = l_Std_DHashMap_ofList___redArg___closed__1;
    v___x_5490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_5489_,
        v_inst_5486_,
        v_inst_5487_,
        v___x_5490_,
        v_l_5488_,
    );
    return v___x_5491_;
}
pub unsafe fn l_Std_DHashMap_Const_ofList(
    mut v_00_u03b1_5492_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5493_: *mut crate::leanh::LeanObject,
    mut v_inst_5494_: *mut crate::leanh::LeanObject,
    mut v_inst_5495_: *mut crate::leanh::LeanObject,
    mut v_l_5496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5497_ = l_Std_DHashMap_ofList___redArg___closed__1;
    v___x_5498_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_5497_,
        v_inst_5494_,
        v_inst_5495_,
        v___x_5498_,
        v_l_5496_,
    );
    return v___x_5499_;
}
pub unsafe fn l_Std_DHashMap_Const_ofArray___redArg(
    mut v_inst_5500_: *mut crate::leanh::LeanObject,
    mut v_inst_5501_: *mut crate::leanh::LeanObject,
    mut v_l_5502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5503_ = l_Std_DHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_5504_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_5503_,
        v_inst_5500_,
        v_inst_5501_,
        v___x_5504_,
        v_l_5502_,
    );
    return v___x_5505_;
}
pub unsafe fn l_Std_DHashMap_Const_ofArray(
    mut v_00_u03b1_5506_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5507_: *mut crate::leanh::LeanObject,
    mut v_inst_5508_: *mut crate::leanh::LeanObject,
    mut v_inst_5509_: *mut crate::leanh::LeanObject,
    mut v_l_5510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5511_ = l_Std_DHashMap_Const_unitOfArray___redArg___closed__1;
    v___x_5512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_5511_,
        v_inst_5508_,
        v_inst_5509_,
        v___x_5512_,
        v_l_5510_,
    );
    return v___x_5513_;
}
pub unsafe fn l_Std_DHashMap_Const_unitOfList___redArg(
    mut v_inst_5514_: *mut crate::leanh::LeanObject,
    mut v_inst_5515_: *mut crate::leanh::LeanObject,
    mut v_l_5516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5517_ = l_Std_DHashMap_ofList___redArg___closed__1;
    v___x_5518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_5517_,
        v_inst_5514_,
        v_inst_5515_,
        v___x_5518_,
        v_l_5516_,
    );
    return v___x_5519_;
}
pub unsafe fn l_Std_DHashMap_Const_unitOfList(
    mut v_00_u03b1_5520_: *mut crate::leanh::LeanObject,
    mut v_inst_5521_: *mut crate::leanh::LeanObject,
    mut v_inst_5522_: *mut crate::leanh::LeanObject,
    mut v_l_5523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5524_ = l_Std_DHashMap_ofList___redArg___closed__1;
    v___x_5525_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_instEmptyCollection___closed__1,
    );
    v___x_5526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_5524_,
        v_inst_5521_,
        v_inst_5522_,
        v___x_5525_,
        v_l_5523_,
    );
    return v___x_5526_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Basic(builtin);
}
