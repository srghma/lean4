// Lean compiler output
// Module: Std.Data.HashSet.Basic
// Imports: Std.Data.HashMap.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0,
};
use crate::r#gen::Init::Data::List::Control::l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go,
    l_Std_DHashMap_Internal_AssocList_contains___redArg,
    l_Std_DHashMap_Internal_AssocList_foldlM___redArg,
    l_Std_DHashMap_Internal_AssocList_foldrM___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_erase___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_expand___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_inter___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Raw::l_Std_DHashMap_Raw_Internal_numBuckets___redArg;
use crate::r#gen::Std::Data::DHashMap::RawDef::l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2;
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
static mut l_Std_HashSet_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashSet_instEmptyCollection___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_instEmptyCollection___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashSet_term___x7em___00__closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_HashSet_term___x7em___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__1_value: leanh::LeanStringObject<8> =
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
        m_data: [72, 97, 115, 104, 83, 101, 116, 0],
    };
static mut l_Std_HashSet_term___x7em___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_HashSet_term___x7em___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__2_value)
        as *mut leanh::LeanObject;
static l_Std_HashSet_term___x7em___00__closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_HashSet_term___x7em___00__closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__1_value)
                as *mut leanh::LeanObject,
            4197276704451117917 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_HashSet_term___x7em___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__2_value)
                as *mut leanh::LeanObject,
            13252601509913869343 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_term___x7em___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__4_value: leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Std_HashSet_term___x7em___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__4_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_term___x7em___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__6_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 126, 109, 32, 0],
    };
static mut l_Std_HashSet_term___x7em___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_term___x7em___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__8_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Std_HashSet_term___x7em___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__8_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_term___x7em___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__9_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_term___x7em___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_term___x7em___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_term___x7em___00__closed__12_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__3_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_term___x7em___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_HashSet_term___x7em__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,6049842283740396800 as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7_value) as *mut leanh::LeanObject;
static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_term___x7em___00__closed__1_value) as *mut leanh::LeanObject,4197276704451117917 as *mut leanh::LeanObject] };
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,13289216293186885598 as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_toList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_toList___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_toList___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_toList___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_toList___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_toList___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_toList___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_toList___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_toList___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__10_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashSet_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_toList___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toList___redArg___closed__11_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_HashSet_toList___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_toList___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_ofList___redArg___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_ofList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_ofList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_ofList___redArg___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_ofList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_ofList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_ofList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toArray___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashSet_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_toArray___redArg___closed__1_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_HashSet_toArray___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_toArray___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_all___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_HashSet_all___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_all___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_union___redArg___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_union___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_union___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_HashSet_beq___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_beq___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashSet_partition___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_partition___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashSet_ofArray___redArg___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_toList___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_ofArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_ofArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_ofArray___redArg___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_ofArray___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_ofArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_ofArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_instRepr___redArg___lam__2___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 72, 97, 115, 104, 83, 101, 116, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Std_HashSet_instRepr___redArg___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_instRepr___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_instRepr___redArg___lam__2___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_instRepr___redArg___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_instRepr___redArg___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_instRepr___redArg___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_HashSet_emptyWithCapacity___redArg(
    mut v_capacity_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = leanh::lean_unsigned_to_nat(0);
    v___x_1463_ = leanh::lean_unsigned_to_nat(4);
    v___x_1464_ = lean_nat_mul(v_capacity_1461_, v___x_1463_);
    v___x_1465_ = leanh::lean_unsigned_to_nat(3);
    v___x_1466_ = lean_nat_div(v___x_1464_, v___x_1465_);
    leanh::lean_dec(v___x_1464_);
    v___x_1467_ = l_Nat_nextPowerOfTwo(v___x_1466_);
    leanh::lean_dec(v___x_1466_);
    v___x_1468_ = leanh::lean_box(0);
    v___x_1469_ = lean_mk_array(v___x_1467_, v___x_1468_);
    v___x_1470_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1470_, 0, v___x_1462_);
    leanh::lean_ctor_set(v___x_1470_, 1, v___x_1469_);
    return v___x_1470_;
}
pub unsafe fn l_Std_HashSet_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Std_HashSet_emptyWithCapacity___redArg(v_capacity_1471_);
    leanh::lean_dec(v_capacity_1471_);
    return v_res_1472_;
}
pub unsafe fn l_Std_HashSet_emptyWithCapacity(
    mut v_00_u03b1_1473_: *mut leanh::LeanObject,
    mut v_inst_1474_: *mut leanh::LeanObject,
    mut v_inst_1475_: *mut leanh::LeanObject,
    mut v_capacity_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = leanh::lean_unsigned_to_nat(0);
    v___x_1478_ = leanh::lean_unsigned_to_nat(4);
    v___x_1479_ = lean_nat_mul(v_capacity_1476_, v___x_1478_);
    v___x_1480_ = leanh::lean_unsigned_to_nat(3);
    v___x_1481_ = lean_nat_div(v___x_1479_, v___x_1480_);
    leanh::lean_dec(v___x_1479_);
    v___x_1482_ = l_Nat_nextPowerOfTwo(v___x_1481_);
    leanh::lean_dec(v___x_1481_);
    v___x_1483_ = leanh::lean_box(0);
    v___x_1484_ = lean_mk_array(v___x_1482_, v___x_1483_);
    v___x_1485_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1485_, 0, v___x_1477_);
    leanh::lean_ctor_set(v___x_1485_, 1, v___x_1484_);
    return v___x_1485_;
}
pub unsafe fn l_Std_HashSet_emptyWithCapacity___boxed(
    mut v_00_u03b1_1486_: *mut leanh::LeanObject,
    mut v_inst_1487_: *mut leanh::LeanObject,
    mut v_inst_1488_: *mut leanh::LeanObject,
    mut v_capacity_1489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1490_ = l_Std_HashSet_emptyWithCapacity(
        v_00_u03b1_1486_,
        v_inst_1487_,
        v_inst_1488_,
        v_capacity_1489_,
    );
    leanh::lean_dec(v_capacity_1489_);
    leanh::lean_dec_ref(v_inst_1488_);
    leanh::lean_dec_ref(v_inst_1487_);
    return v_res_1490_;
}
pub unsafe fn _init_l_Std_HashSet_instEmptyCollection___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = leanh::lean_box(0);
    v___x_1492_ = leanh::lean_unsigned_to_nat(16);
    v___x_1493_ = lean_mk_array(v___x_1492_, v___x_1491_);
    return v___x_1493_;
}
pub unsafe fn _init_l_Std_HashSet_instEmptyCollection___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__0_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__0,
    );
    v___x_1495_ = leanh::lean_unsigned_to_nat(0);
    v___x_1496_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1496_, 0, v___x_1495_);
    leanh::lean_ctor_set(v___x_1496_, 1, v___x_1494_);
    return v___x_1496_;
}
pub unsafe fn l_Std_HashSet_instEmptyCollection(
    mut v_00_u03b1_1497_: *mut leanh::LeanObject,
    mut v_inst_1498_: *mut leanh::LeanObject,
    mut v_inst_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    return v___x_1500_;
}
pub unsafe fn l_Std_HashSet_instEmptyCollection___boxed(
    mut v_00_u03b1_1501_: *mut leanh::LeanObject,
    mut v_inst_1502_: *mut leanh::LeanObject,
    mut v_inst_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_Std_HashSet_instEmptyCollection(v_00_u03b1_1501_, v_inst_1502_, v_inst_1503_);
    leanh::lean_dec_ref(v_inst_1503_);
    leanh::lean_dec_ref(v_inst_1502_);
    return v_res_1504_;
}
pub unsafe fn l_Std_HashSet_instInhabited(
    mut v_00_u03b1_1505_: *mut leanh::LeanObject,
    mut v_inst_1506_: *mut leanh::LeanObject,
    mut v_inst_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    return v___x_1508_;
}
pub unsafe fn l_Std_HashSet_instInhabited___boxed(
    mut v_00_u03b1_1509_: *mut leanh::LeanObject,
    mut v_inst_1510_: *mut leanh::LeanObject,
    mut v_inst_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1512_ = l_Std_HashSet_instInhabited(v_00_u03b1_1509_, v_inst_1510_, v_inst_1511_);
    leanh::lean_dec_ref(v_inst_1511_);
    leanh::lean_dec_ref(v_inst_1510_);
    return v_res_1512_;
}
pub unsafe fn _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5;
    v___x_1552_ = l_String_toRawSubstring_x27(v___x_1551_);
    return v___x_1552_;
}
pub unsafe fn l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(
    mut v_x_1573_: *mut leanh::LeanObject,
    mut v_a_1574_: *mut leanh::LeanObject,
    mut v_a_1575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    v___x_1576_ = l_Std_HashSet_term___x7em___00__closed__3;
    leanh::lean_inc(v_x_1573_);
    v___x_1577_ = l_Lean_Syntax_isOfKind(v_x_1573_, v___x_1576_);
    if v___x_1577_ == 0 {
        let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1573_);
        v___x_1578_ = leanh::lean_box(1);
        v___x_1579_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1579_, 0, v___x_1578_);
        leanh::lean_ctor_set(v___x_1579_, 1, v_a_1575_);
        return v___x_1579_;
    } else {
        let mut v_quotContext_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: u8 = 0;
        let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1580_ = leanh::lean_ctor_get(v_a_1574_, 1);
        v_currMacroScope_1581_ = leanh::lean_ctor_get(v_a_1574_, 2);
        v_ref_1582_ = leanh::lean_ctor_get(v_a_1574_, 5);
        v___x_1583_ = leanh::lean_unsigned_to_nat(0);
        v___x_1584_ = l_Lean_Syntax_getArg(v_x_1573_, v___x_1583_);
        v___x_1585_ = leanh::lean_unsigned_to_nat(2);
        v___x_1586_ = l_Lean_Syntax_getArg(v_x_1573_, v___x_1585_);
        leanh::lean_dec(v_x_1573_);
        v___x_1587_ = 0;
        v___x_1588_ = l_Lean_SourceInfo_fromRef(v_ref_1582_, v___x_1587_);
        v___x_1589_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4;
        v___x_1590_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once), _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6);
        v___x_1591_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7;
        leanh::lean_inc(v_currMacroScope_1581_);
        leanh::lean_inc(v_quotContext_1580_);
        v___x_1592_ =
            l_Lean_addMacroScope(v_quotContext_1580_, v___x_1591_, v_currMacroScope_1581_);
        v___x_1593_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12;
        leanh::lean_inc_n(v___x_1588_, 2);
        v___x_1594_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1594_, 0, v___x_1588_);
        leanh::lean_ctor_set(v___x_1594_, 1, v___x_1590_);
        leanh::lean_ctor_set(v___x_1594_, 2, v___x_1592_);
        leanh::lean_ctor_set(v___x_1594_, 3, v___x_1593_);
        v___x_1595_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14;
        v___x_1596_ = l_Lean_Syntax_node2(v___x_1588_, v___x_1595_, v___x_1584_, v___x_1586_);
        v___x_1597_ = l_Lean_Syntax_node2(v___x_1588_, v___x_1589_, v___x_1594_, v___x_1596_);
        v___x_1598_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1598_, 0, v___x_1597_);
        leanh::lean_ctor_set(v___x_1598_, 1, v_a_1575_);
        return v___x_1598_;
    }
}
pub unsafe fn l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___boxed(
    mut v_x_1599_: *mut leanh::LeanObject,
    mut v_a_1600_: *mut leanh::LeanObject,
    mut v_a_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(v_x_1599_, v_a_1600_, v_a_1601_);
    leanh::lean_dec_ref(v_a_1600_);
    return v_res_1602_;
}
pub unsafe fn l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(
    mut v_x_1606_: *mut leanh::LeanObject,
    mut v_a_1607_: *mut leanh::LeanObject,
    mut v_a_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    v___x_1609_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4;
    leanh::lean_inc(v_x_1606_);
    v___x_1610_ = l_Lean_Syntax_isOfKind(v_x_1606_, v___x_1609_);
    if v___x_1610_ == 0 {
        let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1606_);
        v___x_1611_ = leanh::lean_box(0);
        v___x_1612_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1612_, 0, v___x_1611_);
        leanh::lean_ctor_set(v___x_1612_, 1, v_a_1608_);
        return v___x_1612_;
    } else {
        let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1616_: u8 = 0;
        v___x_1613_ = leanh::lean_unsigned_to_nat(0);
        v___x_1614_ = l_Lean_Syntax_getArg(v_x_1606_, v___x_1613_);
        v___x_1615_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1;
        leanh::lean_inc(v___x_1614_);
        v___x_1616_ = l_Lean_Syntax_isOfKind(v___x_1614_, v___x_1615_);
        if v___x_1616_ == 0 {
            let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1614_);
            leanh::lean_dec(v_x_1606_);
            v___x_1617_ = leanh::lean_box(0);
            v___x_1618_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1618_, 0, v___x_1617_);
            leanh::lean_ctor_set(v___x_1618_, 1, v_a_1608_);
            return v___x_1618_;
        } else {
            let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1622_: u8 = 0;
            v___x_1619_ = leanh::lean_unsigned_to_nat(1);
            v___x_1620_ = l_Lean_Syntax_getArg(v_x_1606_, v___x_1619_);
            leanh::lean_dec(v_x_1606_);
            v___x_1621_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1620_);
            v___x_1622_ = l_Lean_Syntax_matchesNull(v___x_1620_, v___x_1621_);
            if v___x_1622_ == 0 {
                let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1620_);
                leanh::lean_dec(v___x_1614_);
                v___x_1623_ = leanh::lean_box(0);
                v___x_1624_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1624_, 0, v___x_1623_);
                leanh::lean_ctor_set(v___x_1624_, 1, v_a_1608_);
                return v___x_1624_;
            } else {
                let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1628_: u8 = 0;
                let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1625_ = l_Lean_Syntax_getArg(v___x_1620_, v___x_1613_);
                v___x_1626_ = l_Lean_Syntax_getArg(v___x_1620_, v___x_1619_);
                leanh::lean_dec(v___x_1620_);
                v_ref_1627_ = l_Lean_replaceRef(v___x_1614_, v_a_1607_);
                leanh::lean_dec(v___x_1614_);
                v___x_1628_ = 0;
                v___x_1629_ = l_Lean_SourceInfo_fromRef(v_ref_1627_, v___x_1628_);
                leanh::lean_dec(v_ref_1627_);
                v___x_1630_ = l_Std_HashSet_term___x7em___00__closed__3;
                v___x_1631_ = l_Std_HashSet_term___x7em___00__closed__6;
                leanh::lean_inc(v___x_1629_);
                v___x_1632_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1632_, 0, v___x_1629_);
                leanh::lean_ctor_set(v___x_1632_, 1, v___x_1631_);
                v___x_1633_ = l_Lean_Syntax_node3(
                    v___x_1629_,
                    v___x_1630_,
                    v___x_1625_,
                    v___x_1632_,
                    v___x_1626_,
                );
                v___x_1634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1634_, 0, v___x_1633_);
                leanh::lean_ctor_set(v___x_1634_, 1, v_a_1608_);
                return v___x_1634_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(
    mut v_x_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ =
        l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(
            v_x_1635_, v_a_1636_, v_a_1637_,
        );
    leanh::lean_dec(v_a_1636_);
    return v_res_1638_;
}
pub unsafe fn l_Std_HashSet_insert___redArg(
    mut v_x_1639_: *mut leanh::LeanObject,
    mut v_x_1640_: *mut leanh::LeanObject,
    mut v_m_1641_: *mut leanh::LeanObject,
    mut v_a_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1643_ = leanh::lean_box(0);
    v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1639_,
        v_x_1640_,
        v_m_1641_,
        v_a_1642_,
        v___x_1643_,
    );
    return v___x_1644_;
}
pub unsafe fn l_Std_HashSet_insert(
    mut v_00_u03b1_1645_: *mut leanh::LeanObject,
    mut v_x_1646_: *mut leanh::LeanObject,
    mut v_x_1647_: *mut leanh::LeanObject,
    mut v_m_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = leanh::lean_box(0);
    v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1646_,
        v_x_1647_,
        v_m_1648_,
        v_a_1649_,
        v___x_1650_,
    );
    return v___x_1651_;
}
pub unsafe fn l_Std_HashSet_instSingleton___redArg___lam__0(
    mut v_x_1652_: *mut leanh::LeanObject,
    mut v_x_1653_: *mut leanh::LeanObject,
    mut v_a_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    v___x_1656_ = leanh::lean_box(0);
    v___x_1657_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1652_,
        v_x_1653_,
        v___x_1655_,
        v_a_1654_,
        v___x_1656_,
    );
    return v___x_1657_;
}
pub unsafe fn l_Std_HashSet_instSingleton___redArg(
    mut v_x_1658_: *mut leanh::LeanObject,
    mut v_x_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1660_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1660_, 0, v_x_1658_);
    leanh::lean_closure_set(v___f_1660_, 1, v_x_1659_);
    return v___f_1660_;
}
pub unsafe fn l_Std_HashSet_instSingleton(
    mut v_00_u03b1_1661_: *mut leanh::LeanObject,
    mut v_x_1662_: *mut leanh::LeanObject,
    mut v_x_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1664_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instSingleton___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1664_, 0, v_x_1662_);
    leanh::lean_closure_set(v___f_1664_, 1, v_x_1663_);
    return v___f_1664_;
}
pub unsafe fn l_Std_HashSet_instInsert___redArg___lam__0(
    mut v_x_1665_: *mut leanh::LeanObject,
    mut v_x_1666_: *mut leanh::LeanObject,
    mut v_a_1667_: *mut leanh::LeanObject,
    mut v_s_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = leanh::lean_box(0);
    v___x_1670_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1665_,
        v_x_1666_,
        v_s_1668_,
        v_a_1667_,
        v___x_1669_,
    );
    return v___x_1670_;
}
pub unsafe fn l_Std_HashSet_instInsert___redArg(
    mut v_x_1671_: *mut leanh::LeanObject,
    mut v_x_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1673_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1673_, 0, v_x_1671_);
    leanh::lean_closure_set(v___f_1673_, 1, v_x_1672_);
    return v___f_1673_;
}
pub unsafe fn l_Std_HashSet_instInsert(
    mut v_00_u03b1_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
    mut v_x_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1677_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instInsert___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1677_, 0, v_x_1675_);
    leanh::lean_closure_set(v___f_1677_, 1, v_x_1676_);
    return v___f_1677_;
}
pub unsafe fn l_Std_HashSet_containsThenInsert___redArg(
    mut v_x_1678_: *mut leanh::LeanObject,
    mut v_x_1679_: *mut leanh::LeanObject,
    mut v_m_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u64 = 0;
    let mut v___x_1687_: u64 = 0;
    let mut v___x_1688_: u64 = 0;
    let mut v___x_1689_: u64 = 0;
    let mut v_fold_1690_: u64 = 0;
    let mut v___x_1691_: u64 = 0;
    let mut v___x_1692_: u64 = 0;
    let mut v___x_1693_: u64 = 0;
    let mut v___x_1694_: usize = 0;
    let mut v___x_1695_: usize = 0;
    let mut v___x_1696_: usize = 0;
    let mut v___x_1697_: usize = 0;
    let mut v___x_1698_: usize = 0;
    let mut v_bkt_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: u8 = 0;
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u8 = 0;
    let mut v_val_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1726_: u8 = 0;
    let mut v_unused_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1682_ = leanh::lean_ctor_get(v_m_1680_, 0);
                v_buckets_1683_ = leanh::lean_ctor_get(v_m_1680_, 1);
                v___x_1684_ = lean_array_get_size(v_buckets_1683_);
                leanh::lean_inc_ref(v_x_1679_);
                leanh::lean_inc_n(v_a_1681_, 2);
                v___x_1685_ = leanh::lean_apply_1(v_x_1679_, v_a_1681_);
                v___x_1686_ = 32u64;
                v___x_1687_ = leanh::lean_unbox_uint64(v___x_1685_);
                v___x_1688_ = lean_uint64_shift_right(v___x_1687_, v___x_1686_);
                v___x_1689_ = leanh::lean_unbox_uint64(v___x_1685_);
                leanh::lean_dec_ref(v___x_1685_);
                v_fold_1690_ = lean_uint64_xor(v___x_1689_, v___x_1688_);
                v___x_1691_ = 16u64;
                v___x_1692_ = lean_uint64_shift_right(v_fold_1690_, v___x_1691_);
                v___x_1693_ = lean_uint64_xor(v_fold_1690_, v___x_1692_);
                v___x_1694_ = lean_uint64_to_usize(v___x_1693_);
                v___x_1695_ = lean_usize_of_nat(v___x_1684_);
                v___x_1696_ = 1usize;
                v___x_1697_ = lean_usize_sub(v___x_1695_, v___x_1696_);
                v___x_1698_ = lean_usize_land(v___x_1694_, v___x_1697_);
                v_bkt_1699_ = lean_array_uget_borrowed(v_buckets_1683_, v___x_1698_);
                leanh::lean_inc(v_bkt_1699_);
                v___x_1700_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1678_,
                    v_a_1681_,
                    v_bkt_1699_,
                );
                if v___x_1700_ == 0 {
                    leanh::lean_inc_ref(v_buckets_1683_);
                    leanh::lean_inc(v_size_1682_);
                    v_isSharedCheck_1726_ = (!leanh::lean_is_exclusive(v_m_1680_)) as u8;
                    if v_isSharedCheck_1726_ == 0 {
                        v_unused_1727_ = leanh::lean_ctor_get(v_m_1680_, 1);
                        leanh::lean_dec(v_unused_1727_);
                        v_unused_1728_ = leanh::lean_ctor_get(v_m_1680_, 0);
                        leanh::lean_dec(v_unused_1728_);
                        v___x_1702_ = v_m_1680_;
                        v_isShared_1703_ = v_isSharedCheck_1726_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_1680_);
                        v___x_1702_ = leanh::lean_box(0);
                        v_isShared_1703_ = v_isSharedCheck_1726_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1681_);
                    leanh::lean_dec_ref(v_x_1679_);
                    v___x_1729_ = leanh::lean_box((v___x_1700_) as usize);
                    v___x_1730_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1730_, 0, v___x_1729_);
                    leanh::lean_ctor_set(v___x_1730_, 1, v_m_1680_);
                    return v___x_1730_;
                }
            }
            1 => {
                v___x_1704_ = leanh::lean_box(0);
                v___x_1705_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1706_ = lean_nat_add(v_size_1682_, v___x_1705_);
                leanh::lean_dec(v_size_1682_);
                leanh::lean_inc(v_bkt_1699_);
                v___x_1707_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1707_, 0, v_a_1681_);
                leanh::lean_ctor_set(v___x_1707_, 1, v___x_1704_);
                leanh::lean_ctor_set(v___x_1707_, 2, v_bkt_1699_);
                v_buckets_x27_1708_ = lean_array_uset(v_buckets_1683_, v___x_1698_, v___x_1707_);
                v___x_1709_ = leanh::lean_unsigned_to_nat(4);
                v___x_1710_ = lean_nat_mul(v_size_x27_1706_, v___x_1709_);
                v___x_1711_ = leanh::lean_unsigned_to_nat(3);
                v___x_1712_ = lean_nat_div(v___x_1710_, v___x_1711_);
                leanh::lean_dec(v___x_1710_);
                v___x_1713_ = lean_array_get_size(v_buckets_x27_1708_);
                v___x_1714_ = lean_nat_dec_le(v___x_1712_, v___x_1713_);
                leanh::lean_dec(v___x_1712_);
                if v___x_1714_ == 0 {
                    v_val_1715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1679_,
                        v_buckets_x27_1708_,
                    );
                    if v_isShared_1703_ == 0 {
                        leanh::lean_ctor_set(v___x_1702_, 1, v_val_1715_);
                        leanh::lean_ctor_set(v___x_1702_, 0, v_size_x27_1706_);
                        v___x_1717_ = v___x_1702_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1720_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_size_x27_1706_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_val_1715_);
                        v___x_1717_ = v_reuseFailAlloc_1720_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1679_);
                    if v_isShared_1703_ == 0 {
                        leanh::lean_ctor_set(v___x_1702_, 1, v_buckets_x27_1708_);
                        leanh::lean_ctor_set(v___x_1702_, 0, v_size_x27_1706_);
                        v___x_1722_ = v___x_1702_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1725_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_size_x27_1706_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_buckets_x27_1708_);
                        v___x_1722_ = v_reuseFailAlloc_1725_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1718_ = leanh::lean_box((v___x_1700_) as usize);
                v___x_1719_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1719_, 0, v___x_1718_);
                leanh::lean_ctor_set(v___x_1719_, 1, v___x_1717_);
                return v___x_1719_;
            }
            3 => {
                v___x_1723_ = leanh::lean_box((v___x_1700_) as usize);
                v___x_1724_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1724_, 0, v___x_1723_);
                leanh::lean_ctor_set(v___x_1724_, 1, v___x_1722_);
                return v___x_1724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_containsThenInsert(
    mut v_00_u03b1_1731_: *mut leanh::LeanObject,
    mut v_x_1732_: *mut leanh::LeanObject,
    mut v_x_1733_: *mut leanh::LeanObject,
    mut v_m_1734_: *mut leanh::LeanObject,
    mut v_a_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u64 = 0;
    let mut v___x_1741_: u64 = 0;
    let mut v___x_1742_: u64 = 0;
    let mut v___x_1743_: u64 = 0;
    let mut v_fold_1744_: u64 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1746_: u64 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v___x_1748_: usize = 0;
    let mut v___x_1749_: usize = 0;
    let mut v___x_1750_: usize = 0;
    let mut v___x_1751_: usize = 0;
    let mut v___x_1752_: usize = 0;
    let mut v_bkt_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1757_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v_val_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut v_unused_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1736_ = leanh::lean_ctor_get(v_m_1734_, 0);
                v_buckets_1737_ = leanh::lean_ctor_get(v_m_1734_, 1);
                v___x_1738_ = lean_array_get_size(v_buckets_1737_);
                leanh::lean_inc_ref(v_x_1733_);
                leanh::lean_inc_n(v_a_1735_, 2);
                v___x_1739_ = leanh::lean_apply_1(v_x_1733_, v_a_1735_);
                v___x_1740_ = 32u64;
                v___x_1741_ = leanh::lean_unbox_uint64(v___x_1739_);
                v___x_1742_ = lean_uint64_shift_right(v___x_1741_, v___x_1740_);
                v___x_1743_ = leanh::lean_unbox_uint64(v___x_1739_);
                leanh::lean_dec_ref(v___x_1739_);
                v_fold_1744_ = lean_uint64_xor(v___x_1743_, v___x_1742_);
                v___x_1745_ = 16u64;
                v___x_1746_ = lean_uint64_shift_right(v_fold_1744_, v___x_1745_);
                v___x_1747_ = lean_uint64_xor(v_fold_1744_, v___x_1746_);
                v___x_1748_ = lean_uint64_to_usize(v___x_1747_);
                v___x_1749_ = lean_usize_of_nat(v___x_1738_);
                v___x_1750_ = 1usize;
                v___x_1751_ = lean_usize_sub(v___x_1749_, v___x_1750_);
                v___x_1752_ = lean_usize_land(v___x_1748_, v___x_1751_);
                v_bkt_1753_ = lean_array_uget_borrowed(v_buckets_1737_, v___x_1752_);
                leanh::lean_inc(v_bkt_1753_);
                v___x_1754_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_1732_,
                    v_a_1735_,
                    v_bkt_1753_,
                );
                if v___x_1754_ == 0 {
                    leanh::lean_inc_ref(v_buckets_1737_);
                    leanh::lean_inc(v_size_1736_);
                    v_isSharedCheck_1780_ = (!leanh::lean_is_exclusive(v_m_1734_)) as u8;
                    if v_isSharedCheck_1780_ == 0 {
                        v_unused_1781_ = leanh::lean_ctor_get(v_m_1734_, 1);
                        leanh::lean_dec(v_unused_1781_);
                        v_unused_1782_ = leanh::lean_ctor_get(v_m_1734_, 0);
                        leanh::lean_dec(v_unused_1782_);
                        v___x_1756_ = v_m_1734_;
                        v_isShared_1757_ = v_isSharedCheck_1780_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_1734_);
                        v___x_1756_ = leanh::lean_box(0);
                        v_isShared_1757_ = v_isSharedCheck_1780_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1735_);
                    leanh::lean_dec_ref(v_x_1733_);
                    v___x_1783_ = leanh::lean_box((v___x_1754_) as usize);
                    v___x_1784_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1784_, 0, v___x_1783_);
                    leanh::lean_ctor_set(v___x_1784_, 1, v_m_1734_);
                    return v___x_1784_;
                }
            }
            1 => {
                v___x_1758_ = leanh::lean_box(0);
                v___x_1759_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1760_ = lean_nat_add(v_size_1736_, v___x_1759_);
                leanh::lean_dec(v_size_1736_);
                leanh::lean_inc(v_bkt_1753_);
                v___x_1761_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1761_, 0, v_a_1735_);
                leanh::lean_ctor_set(v___x_1761_, 1, v___x_1758_);
                leanh::lean_ctor_set(v___x_1761_, 2, v_bkt_1753_);
                v_buckets_x27_1762_ = lean_array_uset(v_buckets_1737_, v___x_1752_, v___x_1761_);
                v___x_1763_ = leanh::lean_unsigned_to_nat(4);
                v___x_1764_ = lean_nat_mul(v_size_x27_1760_, v___x_1763_);
                v___x_1765_ = leanh::lean_unsigned_to_nat(3);
                v___x_1766_ = lean_nat_div(v___x_1764_, v___x_1765_);
                leanh::lean_dec(v___x_1764_);
                v___x_1767_ = lean_array_get_size(v_buckets_x27_1762_);
                v___x_1768_ = lean_nat_dec_le(v___x_1766_, v___x_1767_);
                leanh::lean_dec(v___x_1766_);
                if v___x_1768_ == 0 {
                    v_val_1769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_1733_,
                        v_buckets_x27_1762_,
                    );
                    if v_isShared_1757_ == 0 {
                        leanh::lean_ctor_set(v___x_1756_, 1, v_val_1769_);
                        leanh::lean_ctor_set(v___x_1756_, 0, v_size_x27_1760_);
                        v___x_1771_ = v___x_1756_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1774_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_size_x27_1760_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_val_1769_);
                        v___x_1771_ = v_reuseFailAlloc_1774_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1733_);
                    if v_isShared_1757_ == 0 {
                        leanh::lean_ctor_set(v___x_1756_, 1, v_buckets_x27_1762_);
                        leanh::lean_ctor_set(v___x_1756_, 0, v_size_x27_1760_);
                        v___x_1776_ = v___x_1756_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1779_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_size_x27_1760_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_buckets_x27_1762_);
                        v___x_1776_ = v_reuseFailAlloc_1779_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1772_ = leanh::lean_box((v___x_1754_) as usize);
                v___x_1773_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1773_, 0, v___x_1772_);
                leanh::lean_ctor_set(v___x_1773_, 1, v___x_1771_);
                return v___x_1773_;
            }
            3 => {
                v___x_1777_ = leanh::lean_box((v___x_1754_) as usize);
                v___x_1778_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
                leanh::lean_ctor_set(v___x_1778_, 1, v___x_1776_);
                return v___x_1778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_contains___redArg(
    mut v_x_1785_: *mut leanh::LeanObject,
    mut v_x_1786_: *mut leanh::LeanObject,
    mut v_m_1787_: *mut leanh::LeanObject,
    mut v_a_1788_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1789_: u8 = 0;
    v___x_1789_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_1785_, v_x_1786_, v_m_1787_, v_a_1788_,
    );
    return v___x_1789_;
}
pub unsafe fn l_Std_HashSet_contains___redArg___boxed(
    mut v_x_1790_: *mut leanh::LeanObject,
    mut v_x_1791_: *mut leanh::LeanObject,
    mut v_m_1792_: *mut leanh::LeanObject,
    mut v_a_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1794_: u8 = 0;
    let mut v_r_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Std_HashSet_contains___redArg(v_x_1790_, v_x_1791_, v_m_1792_, v_a_1793_);
    leanh::lean_dec_ref(v_m_1792_);
    v_r_1795_ = leanh::lean_box((v_res_1794_) as usize);
    return v_r_1795_;
}
pub unsafe fn l_Std_HashSet_contains(
    mut v_00_u03b1_1796_: *mut leanh::LeanObject,
    mut v_x_1797_: *mut leanh::LeanObject,
    mut v_x_1798_: *mut leanh::LeanObject,
    mut v_m_1799_: *mut leanh::LeanObject,
    mut v_a_1800_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1801_: u8 = 0;
    v___x_1801_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_1797_, v_x_1798_, v_m_1799_, v_a_1800_,
    );
    return v___x_1801_;
}
pub unsafe fn l_Std_HashSet_contains___boxed(
    mut v_00_u03b1_1802_: *mut leanh::LeanObject,
    mut v_x_1803_: *mut leanh::LeanObject,
    mut v_x_1804_: *mut leanh::LeanObject,
    mut v_m_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1807_: u8 = 0;
    let mut v_r_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ =
        l_Std_HashSet_contains(v_00_u03b1_1802_, v_x_1803_, v_x_1804_, v_m_1805_, v_a_1806_);
    leanh::lean_dec_ref(v_m_1805_);
    v_r_1808_ = leanh::lean_box((v_res_1807_) as usize);
    return v_r_1808_;
}
pub unsafe fn l_Std_HashSet_instMembership(
    mut v_00_u03b1_1809_: *mut leanh::LeanObject,
    mut v_inst_1810_: *mut leanh::LeanObject,
    mut v_inst_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1812_ = leanh::lean_box(0);
    return v___x_1812_;
}
pub unsafe fn l_Std_HashSet_instMembership___boxed(
    mut v_00_u03b1_1813_: *mut leanh::LeanObject,
    mut v_inst_1814_: *mut leanh::LeanObject,
    mut v_inst_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Std_HashSet_instMembership(v_00_u03b1_1813_, v_inst_1814_, v_inst_1815_);
    leanh::lean_dec_ref(v_inst_1815_);
    leanh::lean_dec_ref(v_inst_1814_);
    return v_res_1816_;
}
pub unsafe fn l_Std_HashSet_instDecidableMem___redArg(
    mut v_inst_1817_: *mut leanh::LeanObject,
    mut v_inst_1818_: *mut leanh::LeanObject,
    mut v_m_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1821_: u8 = 0;
    v___x_1821_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_1817_,
        v_inst_1818_,
        v_m_1819_,
        v_a_1820_,
    );
    return v___x_1821_;
}
pub unsafe fn l_Std_HashSet_instDecidableMem___redArg___boxed(
    mut v_inst_1822_: *mut leanh::LeanObject,
    mut v_inst_1823_: *mut leanh::LeanObject,
    mut v_m_1824_: *mut leanh::LeanObject,
    mut v_a_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1826_: u8 = 0;
    let mut v_r_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1826_ =
        l_Std_HashSet_instDecidableMem___redArg(v_inst_1822_, v_inst_1823_, v_m_1824_, v_a_1825_);
    leanh::lean_dec_ref(v_m_1824_);
    v_r_1827_ = leanh::lean_box((v_res_1826_) as usize);
    return v_r_1827_;
}
pub unsafe fn l_Std_HashSet_instDecidableMem(
    mut v_00_u03b1_1828_: *mut leanh::LeanObject,
    mut v_inst_1829_: *mut leanh::LeanObject,
    mut v_inst_1830_: *mut leanh::LeanObject,
    mut v_m_1831_: *mut leanh::LeanObject,
    mut v_a_1832_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1833_: u8 = 0;
    v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_1829_,
        v_inst_1830_,
        v_m_1831_,
        v_a_1832_,
    );
    return v___x_1833_;
}
pub unsafe fn l_Std_HashSet_instDecidableMem___boxed(
    mut v_00_u03b1_1834_: *mut leanh::LeanObject,
    mut v_inst_1835_: *mut leanh::LeanObject,
    mut v_inst_1836_: *mut leanh::LeanObject,
    mut v_m_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1839_: u8 = 0;
    let mut v_r_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Std_HashSet_instDecidableMem(
        v_00_u03b1_1834_,
        v_inst_1835_,
        v_inst_1836_,
        v_m_1837_,
        v_a_1838_,
    );
    leanh::lean_dec_ref(v_m_1837_);
    v_r_1840_ = leanh::lean_box((v_res_1839_) as usize);
    return v_r_1840_;
}
pub unsafe fn l_Std_HashSet_erase___redArg(
    mut v_x_1841_: *mut leanh::LeanObject,
    mut v_x_1842_: *mut leanh::LeanObject,
    mut v_m_1843_: *mut leanh::LeanObject,
    mut v_a_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1845_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_1841_, v_x_1842_, v_m_1843_, v_a_1844_,
    );
    return v___x_1845_;
}
pub unsafe fn l_Std_HashSet_erase(
    mut v_00_u03b1_1846_: *mut leanh::LeanObject,
    mut v_x_1847_: *mut leanh::LeanObject,
    mut v_x_1848_: *mut leanh::LeanObject,
    mut v_m_1849_: *mut leanh::LeanObject,
    mut v_a_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_1847_, v_x_1848_, v_m_1849_, v_a_1850_,
    );
    return v___x_1851_;
}
pub unsafe fn l_Std_HashSet_size___redArg(
    mut v_m_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_1853_ = leanh::lean_ctor_get(v_m_1852_, 0);
    leanh::lean_inc(v_size_1853_);
    return v_size_1853_;
}
pub unsafe fn l_Std_HashSet_size___redArg___boxed(
    mut v_m_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Std_HashSet_size___redArg(v_m_1854_);
    leanh::lean_dec_ref(v_m_1854_);
    return v_res_1855_;
}
pub unsafe fn l_Std_HashSet_size(
    mut v_00_u03b1_1856_: *mut leanh::LeanObject,
    mut v_x_1857_: *mut leanh::LeanObject,
    mut v_x_1858_: *mut leanh::LeanObject,
    mut v_m_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_1860_ = leanh::lean_ctor_get(v_m_1859_, 0);
    leanh::lean_inc(v_size_1860_);
    return v_size_1860_;
}
pub unsafe fn l_Std_HashSet_size___boxed(
    mut v_00_u03b1_1861_: *mut leanh::LeanObject,
    mut v_x_1862_: *mut leanh::LeanObject,
    mut v_x_1863_: *mut leanh::LeanObject,
    mut v_m_1864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1865_ = l_Std_HashSet_size(v_00_u03b1_1861_, v_x_1862_, v_x_1863_, v_m_1864_);
    leanh::lean_dec_ref(v_m_1864_);
    leanh::lean_dec_ref(v_x_1863_);
    leanh::lean_dec_ref(v_x_1862_);
    return v_res_1865_;
}
pub unsafe fn l_Std_HashSet_get_x3f___redArg(
    mut v_x_1866_: *mut leanh::LeanObject,
    mut v_x_1867_: *mut leanh::LeanObject,
    mut v_m_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_1866_, v_x_1867_, v_m_1868_, v_a_1869_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Std_HashSet_get_x3f___redArg___boxed(
    mut v_x_1871_: *mut leanh::LeanObject,
    mut v_x_1872_: *mut leanh::LeanObject,
    mut v_m_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1875_ = l_Std_HashSet_get_x3f___redArg(v_x_1871_, v_x_1872_, v_m_1873_, v_a_1874_);
    leanh::lean_dec_ref(v_m_1873_);
    return v_res_1875_;
}
pub unsafe fn l_Std_HashSet_get_x3f(
    mut v_00_u03b1_1876_: *mut leanh::LeanObject,
    mut v_x_1877_: *mut leanh::LeanObject,
    mut v_x_1878_: *mut leanh::LeanObject,
    mut v_m_1879_: *mut leanh::LeanObject,
    mut v_a_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_1877_, v_x_1878_, v_m_1879_, v_a_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn l_Std_HashSet_get_x3f___boxed(
    mut v_00_u03b1_1882_: *mut leanh::LeanObject,
    mut v_x_1883_: *mut leanh::LeanObject,
    mut v_x_1884_: *mut leanh::LeanObject,
    mut v_m_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ =
        l_Std_HashSet_get_x3f(v_00_u03b1_1882_, v_x_1883_, v_x_1884_, v_m_1885_, v_a_1886_);
    leanh::lean_dec_ref(v_m_1885_);
    return v_res_1887_;
}
pub unsafe fn l_Std_HashSet_get___redArg(
    mut v_inst_1888_: *mut leanh::LeanObject,
    mut v_inst_1889_: *mut leanh::LeanObject,
    mut v_m_1890_: *mut leanh::LeanObject,
    mut v_a_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1888_,
        v_inst_1889_,
        v_m_1890_,
        v_a_1891_,
    );
    return v___x_1892_;
}
pub unsafe fn l_Std_HashSet_get___redArg___boxed(
    mut v_inst_1893_: *mut leanh::LeanObject,
    mut v_inst_1894_: *mut leanh::LeanObject,
    mut v_m_1895_: *mut leanh::LeanObject,
    mut v_a_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Std_HashSet_get___redArg(v_inst_1893_, v_inst_1894_, v_m_1895_, v_a_1896_);
    leanh::lean_dec_ref(v_m_1895_);
    return v_res_1897_;
}
pub unsafe fn l_Std_HashSet_get(
    mut v_00_u03b1_1898_: *mut leanh::LeanObject,
    mut v_inst_1899_: *mut leanh::LeanObject,
    mut v_inst_1900_: *mut leanh::LeanObject,
    mut v_m_1901_: *mut leanh::LeanObject,
    mut v_a_1902_: *mut leanh::LeanObject,
    mut v_h_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1899_,
        v_inst_1900_,
        v_m_1901_,
        v_a_1902_,
    );
    return v___x_1904_;
}
pub unsafe fn l_Std_HashSet_get___boxed(
    mut v_00_u03b1_1905_: *mut leanh::LeanObject,
    mut v_inst_1906_: *mut leanh::LeanObject,
    mut v_inst_1907_: *mut leanh::LeanObject,
    mut v_m_1908_: *mut leanh::LeanObject,
    mut v_a_1909_: *mut leanh::LeanObject,
    mut v_h_1910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1911_ = l_Std_HashSet_get(
        v_00_u03b1_1905_,
        v_inst_1906_,
        v_inst_1907_,
        v_m_1908_,
        v_a_1909_,
        v_h_1910_,
    );
    leanh::lean_dec_ref(v_m_1908_);
    return v_res_1911_;
}
pub unsafe fn l_Std_HashSet_getD___redArg(
    mut v_inst_1912_: *mut leanh::LeanObject,
    mut v_inst_1913_: *mut leanh::LeanObject,
    mut v_m_1914_: *mut leanh::LeanObject,
    mut v_a_1915_: *mut leanh::LeanObject,
    mut v_fallback_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_inst_1912_,
        v_inst_1913_,
        v_m_1914_,
        v_a_1915_,
        v_fallback_1916_,
    );
    return v___x_1917_;
}
pub unsafe fn l_Std_HashSet_getD___redArg___boxed(
    mut v_inst_1918_: *mut leanh::LeanObject,
    mut v_inst_1919_: *mut leanh::LeanObject,
    mut v_m_1920_: *mut leanh::LeanObject,
    mut v_a_1921_: *mut leanh::LeanObject,
    mut v_fallback_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Std_HashSet_getD___redArg(
        v_inst_1918_,
        v_inst_1919_,
        v_m_1920_,
        v_a_1921_,
        v_fallback_1922_,
    );
    leanh::lean_dec(v_fallback_1922_);
    leanh::lean_dec_ref(v_m_1920_);
    return v_res_1923_;
}
pub unsafe fn l_Std_HashSet_getD(
    mut v_00_u03b1_1924_: *mut leanh::LeanObject,
    mut v_inst_1925_: *mut leanh::LeanObject,
    mut v_inst_1926_: *mut leanh::LeanObject,
    mut v_m_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
    mut v_fallback_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_inst_1925_,
        v_inst_1926_,
        v_m_1927_,
        v_a_1928_,
        v_fallback_1929_,
    );
    return v___x_1930_;
}
pub unsafe fn l_Std_HashSet_getD___boxed(
    mut v_00_u03b1_1931_: *mut leanh::LeanObject,
    mut v_inst_1932_: *mut leanh::LeanObject,
    mut v_inst_1933_: *mut leanh::LeanObject,
    mut v_m_1934_: *mut leanh::LeanObject,
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_fallback_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1937_ = l_Std_HashSet_getD(
        v_00_u03b1_1931_,
        v_inst_1932_,
        v_inst_1933_,
        v_m_1934_,
        v_a_1935_,
        v_fallback_1936_,
    );
    leanh::lean_dec(v_fallback_1936_);
    leanh::lean_dec_ref(v_m_1934_);
    return v_res_1937_;
}
pub unsafe fn l_Std_HashSet_get_x21___redArg(
    mut v_inst_1938_: *mut leanh::LeanObject,
    mut v_inst_1939_: *mut leanh::LeanObject,
    mut v_inst_1940_: *mut leanh::LeanObject,
    mut v_m_1941_: *mut leanh::LeanObject,
    mut v_a_1942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_inst_1938_,
        v_inst_1939_,
        v_inst_1940_,
        v_m_1941_,
        v_a_1942_,
    );
    return v___x_1943_;
}
pub unsafe fn l_Std_HashSet_get_x21___redArg___boxed(
    mut v_inst_1944_: *mut leanh::LeanObject,
    mut v_inst_1945_: *mut leanh::LeanObject,
    mut v_inst_1946_: *mut leanh::LeanObject,
    mut v_m_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Std_HashSet_get_x21___redArg(
        v_inst_1944_,
        v_inst_1945_,
        v_inst_1946_,
        v_m_1947_,
        v_a_1948_,
    );
    leanh::lean_dec_ref(v_m_1947_);
    leanh::lean_dec(v_inst_1946_);
    return v_res_1949_;
}
pub unsafe fn l_Std_HashSet_get_x21(
    mut v_00_u03b1_1950_: *mut leanh::LeanObject,
    mut v_inst_1951_: *mut leanh::LeanObject,
    mut v_inst_1952_: *mut leanh::LeanObject,
    mut v_inst_1953_: *mut leanh::LeanObject,
    mut v_m_1954_: *mut leanh::LeanObject,
    mut v_a_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1956_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_inst_1951_,
        v_inst_1952_,
        v_inst_1953_,
        v_m_1954_,
        v_a_1955_,
    );
    return v___x_1956_;
}
pub unsafe fn l_Std_HashSet_get_x21___boxed(
    mut v_00_u03b1_1957_: *mut leanh::LeanObject,
    mut v_inst_1958_: *mut leanh::LeanObject,
    mut v_inst_1959_: *mut leanh::LeanObject,
    mut v_inst_1960_: *mut leanh::LeanObject,
    mut v_m_1961_: *mut leanh::LeanObject,
    mut v_a_1962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Std_HashSet_get_x21(
        v_00_u03b1_1957_,
        v_inst_1958_,
        v_inst_1959_,
        v_inst_1960_,
        v_m_1961_,
        v_a_1962_,
    );
    leanh::lean_dec_ref(v_m_1961_);
    leanh::lean_dec(v_inst_1960_);
    return v_res_1963_;
}
pub unsafe fn l_Std_HashSet_isEmpty___redArg(mut v_m_1964_: *mut leanh::LeanObject) -> u8 {
    let mut v_size_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: u8 = 0;
    v_size_1965_ = leanh::lean_ctor_get(v_m_1964_, 0);
    v___x_1966_ = leanh::lean_unsigned_to_nat(0);
    v___x_1967_ = lean_nat_dec_eq(v_size_1965_, v___x_1966_);
    return v___x_1967_;
}
pub unsafe fn l_Std_HashSet_isEmpty___redArg___boxed(
    mut v_m_1968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1969_: u8 = 0;
    let mut v_r_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_Std_HashSet_isEmpty___redArg(v_m_1968_);
    leanh::lean_dec_ref(v_m_1968_);
    v_r_1970_ = leanh::lean_box((v_res_1969_) as usize);
    return v_r_1970_;
}
pub unsafe fn l_Std_HashSet_isEmpty(
    mut v_00_u03b1_1971_: *mut leanh::LeanObject,
    mut v_x_1972_: *mut leanh::LeanObject,
    mut v_x_1973_: *mut leanh::LeanObject,
    mut v_m_1974_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    v_size_1975_ = leanh::lean_ctor_get(v_m_1974_, 0);
    v___x_1976_ = leanh::lean_unsigned_to_nat(0);
    v___x_1977_ = lean_nat_dec_eq(v_size_1975_, v___x_1976_);
    return v___x_1977_;
}
pub unsafe fn l_Std_HashSet_isEmpty___boxed(
    mut v_00_u03b1_1978_: *mut leanh::LeanObject,
    mut v_x_1979_: *mut leanh::LeanObject,
    mut v_x_1980_: *mut leanh::LeanObject,
    mut v_m_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1982_: u8 = 0;
    let mut v_r_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1982_ = l_Std_HashSet_isEmpty(v_00_u03b1_1978_, v_x_1979_, v_x_1980_, v_m_1981_);
    leanh::lean_dec_ref(v_m_1981_);
    leanh::lean_dec_ref(v_x_1980_);
    leanh::lean_dec_ref(v_x_1979_);
    v_r_1983_ = leanh::lean_box((v_res_1982_) as usize);
    return v_r_1983_;
}
pub unsafe fn l_Std_HashSet_toList___redArg___lam__0(
    mut v_a_1984_: *mut leanh::LeanObject,
    mut v_b_1985_: *mut leanh::LeanObject,
    mut v_d_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1987_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1987_, 0, v_a_1984_);
    leanh::lean_ctor_set(v___x_1987_, 1, v_d_1986_);
    return v___x_1987_;
}
pub unsafe fn l_Std_HashSet_toList___redArg___lam__1(
    mut v___x_1988_: *mut leanh::LeanObject,
    mut v___f_1989_: *mut leanh::LeanObject,
    mut v_l_1990_: *mut leanh::LeanObject,
    mut v_acc_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1992_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1988_,
        v___f_1989_,
        v_acc_1991_,
        v_l_1990_,
    );
    return v___x_1992_;
}
pub unsafe fn l_Std_HashSet_toList___redArg(
    mut v_m_2016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: u8 = 0;
    v___x_2017_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2018_ = leanh::lean_ctor_get(v_m_2016_, 1);
    leanh::lean_inc_ref(v_buckets_2018_);
    leanh::lean_dec_ref(v_m_2016_);
    v___x_2019_ = leanh::lean_box(0);
    v___x_2020_ = lean_array_get_size(v_buckets_2018_);
    v___x_2021_ = leanh::lean_unsigned_to_nat(0);
    v___x_2022_ = lean_nat_dec_lt(v___x_2021_, v___x_2020_);
    if v___x_2022_ == 0 {
        leanh::lean_dec_ref(v_buckets_2018_);
        return v___x_2019_;
    } else {
        let mut v___f_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2024_: usize = 0;
        let mut v___x_2025_: usize = 0;
        let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2023_ = l_Std_HashSet_toList___redArg___closed__11;
        v___x_2024_ = lean_usize_of_nat(v___x_2020_);
        v___x_2025_ = 0usize;
        v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2017_,
            v___f_2023_,
            v_buckets_2018_,
            v___x_2024_,
            v___x_2025_,
            v___x_2019_,
        );
        return v___x_2026_;
    }
}
pub unsafe fn l_Std_HashSet_toList(
    mut v_00_u03b1_2027_: *mut leanh::LeanObject,
    mut v_x_2028_: *mut leanh::LeanObject,
    mut v_x_2029_: *mut leanh::LeanObject,
    mut v_m_2030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    v___x_2031_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2032_ = leanh::lean_ctor_get(v_m_2030_, 1);
    leanh::lean_inc_ref(v_buckets_2032_);
    leanh::lean_dec_ref(v_m_2030_);
    v___x_2033_ = leanh::lean_box(0);
    v___x_2034_ = lean_array_get_size(v_buckets_2032_);
    v___x_2035_ = leanh::lean_unsigned_to_nat(0);
    v___x_2036_ = lean_nat_dec_lt(v___x_2035_, v___x_2034_);
    if v___x_2036_ == 0 {
        leanh::lean_dec_ref(v_buckets_2032_);
        return v___x_2033_;
    } else {
        let mut v___f_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: usize = 0;
        let mut v___x_2039_: usize = 0;
        let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2037_ = l_Std_HashSet_toList___redArg___closed__11;
        v___x_2038_ = lean_usize_of_nat(v___x_2034_);
        v___x_2039_ = 0usize;
        v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2031_,
            v___f_2037_,
            v_buckets_2032_,
            v___x_2038_,
            v___x_2039_,
            v___x_2033_,
        );
        return v___x_2040_;
    }
}
pub unsafe fn l_Std_HashSet_toList___boxed(
    mut v_00_u03b1_2041_: *mut leanh::LeanObject,
    mut v_x_2042_: *mut leanh::LeanObject,
    mut v_x_2043_: *mut leanh::LeanObject,
    mut v_m_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2045_ = l_Std_HashSet_toList(v_00_u03b1_2041_, v_x_2042_, v_x_2043_, v_m_2044_);
    leanh::lean_dec_ref(v_x_2043_);
    leanh::lean_dec_ref(v_x_2042_);
    return v_res_2045_;
}
pub unsafe fn l_Std_HashSet_ofList___redArg(
    mut v_inst_2050_: *mut leanh::LeanObject,
    mut v_inst_2051_: *mut leanh::LeanObject,
    mut v_l_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2053_ = l_Std_HashSet_ofList___redArg___closed__1;
    v___x_2054_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    v___x_2055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2053_,
        v_inst_2050_,
        v_inst_2051_,
        v___x_2054_,
        v_l_2052_,
    );
    return v___x_2055_;
}
pub unsafe fn l_Std_HashSet_ofList(
    mut v_00_u03b1_2056_: *mut leanh::LeanObject,
    mut v_inst_2057_: *mut leanh::LeanObject,
    mut v_inst_2058_: *mut leanh::LeanObject,
    mut v_l_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2060_ = l_Std_HashSet_ofList___redArg___closed__1;
    v___x_2061_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    v___x_2062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2060_,
        v_inst_2057_,
        v_inst_2058_,
        v___x_2061_,
        v_l_2059_,
    );
    return v___x_2062_;
}
pub unsafe fn l_Std_HashSet_foldM___redArg___lam__0(
    mut v_f_2063_: *mut leanh::LeanObject,
    mut v_b_2064_: *mut leanh::LeanObject,
    mut v_a_2065_: *mut leanh::LeanObject,
    mut v_x_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = leanh::lean_apply_2(v_f_2063_, v_b_2064_, v_a_2065_);
    return v___x_2067_;
}
pub unsafe fn l_Std_HashSet_foldM___redArg___lam__1(
    mut v_inst_2068_: *mut leanh::LeanObject,
    mut v___f_2069_: *mut leanh::LeanObject,
    mut v_acc_2070_: *mut leanh::LeanObject,
    mut v_l_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2068_,
        v___f_2069_,
        v_acc_2070_,
        v_l_2071_,
    );
    return v___x_2072_;
}
pub unsafe fn l_Std_HashSet_foldM___redArg(
    mut v_inst_2073_: *mut leanh::LeanObject,
    mut v_f_2074_: *mut leanh::LeanObject,
    mut v_init_2075_: *mut leanh::LeanObject,
    mut v_b_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: u8 = 0;
    v_buckets_2077_ = leanh::lean_ctor_get(v_b_2076_, 1);
    leanh::lean_inc_ref(v_buckets_2077_);
    leanh::lean_dec_ref(v_b_2076_);
    v___x_2078_ = leanh::lean_unsigned_to_nat(0);
    v___x_2079_ = lean_array_get_size(v_buckets_2077_);
    v___x_2080_ = lean_nat_dec_lt(v___x_2078_, v___x_2079_);
    if v___x_2080_ == 0 {
        let mut v_toApplicative_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2077_);
        leanh::lean_dec(v_f_2074_);
        v_toApplicative_2081_ = leanh::lean_ctor_get(v_inst_2073_, 0);
        leanh::lean_inc_ref(v_toApplicative_2081_);
        leanh::lean_dec_ref(v_inst_2073_);
        v_toPure_2082_ = leanh::lean_ctor_get(v_toApplicative_2081_, 1);
        leanh::lean_inc(v_toPure_2082_);
        leanh::lean_dec_ref(v_toApplicative_2081_);
        v___x_2083_ =
            leanh::lean_apply_2(v_toPure_2082_, leanh::lean_box(0), v_init_2075_);
        return v___x_2083_;
    } else {
        let mut v___f_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: u8 = 0;
        v___f_2084_ = leanh::lean_alloc_closure(
            l_Std_HashSet_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2084_, 0, v_f_2074_);
        leanh::lean_inc_ref(v_inst_2073_);
        v___f_2085_ = leanh::lean_alloc_closure(
            l_Std_HashSet_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2085_, 0, v_inst_2073_);
        leanh::lean_closure_set(v___f_2085_, 1, v___f_2084_);
        v___x_2086_ = lean_nat_dec_le(v___x_2079_, v___x_2079_);
        if v___x_2086_ == 0 {
            if v___x_2080_ == 0 {
                let mut v_toApplicative_2087_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2085_);
                leanh::lean_dec_ref(v_buckets_2077_);
                v_toApplicative_2087_ = leanh::lean_ctor_get(v_inst_2073_, 0);
                leanh::lean_inc_ref(v_toApplicative_2087_);
                leanh::lean_dec_ref(v_inst_2073_);
                v_toPure_2088_ = leanh::lean_ctor_get(v_toApplicative_2087_, 1);
                leanh::lean_inc(v_toPure_2088_);
                leanh::lean_dec_ref(v_toApplicative_2087_);
                v___x_2089_ = leanh::lean_apply_2(
                    v_toPure_2088_,
                    leanh::lean_box(0),
                    v_init_2075_,
                );
                return v___x_2089_;
            } else {
                let mut v___x_2090_: usize = 0;
                let mut v___x_2091_: usize = 0;
                let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2090_ = 0usize;
                v___x_2091_ = lean_usize_of_nat(v___x_2079_);
                v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_2073_,
                    v___f_2085_,
                    v_buckets_2077_,
                    v___x_2090_,
                    v___x_2091_,
                    v_init_2075_,
                );
                return v___x_2092_;
            }
        } else {
            let mut v___x_2093_: usize = 0;
            let mut v___x_2094_: usize = 0;
            let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2093_ = 0usize;
            v___x_2094_ = lean_usize_of_nat(v___x_2079_);
            v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_2073_,
                v___f_2085_,
                v_buckets_2077_,
                v___x_2093_,
                v___x_2094_,
                v_init_2075_,
            );
            return v___x_2095_;
        }
    }
}
pub unsafe fn l_Std_HashSet_foldM(
    mut v_00_u03b1_2096_: *mut leanh::LeanObject,
    mut v_x_2097_: *mut leanh::LeanObject,
    mut v_x_2098_: *mut leanh::LeanObject,
    mut v_m_2099_: *mut leanh::LeanObject,
    mut v_inst_2100_: *mut leanh::LeanObject,
    mut v_00_u03b2_2101_: *mut leanh::LeanObject,
    mut v_f_2102_: *mut leanh::LeanObject,
    mut v_init_2103_: *mut leanh::LeanObject,
    mut v_b_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    v_buckets_2105_ = leanh::lean_ctor_get(v_b_2104_, 1);
    leanh::lean_inc_ref(v_buckets_2105_);
    leanh::lean_dec_ref(v_b_2104_);
    v___x_2106_ = leanh::lean_unsigned_to_nat(0);
    v___x_2107_ = lean_array_get_size(v_buckets_2105_);
    v___x_2108_ = lean_nat_dec_lt(v___x_2106_, v___x_2107_);
    if v___x_2108_ == 0 {
        let mut v_toApplicative_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2105_);
        leanh::lean_dec(v_f_2102_);
        v_toApplicative_2109_ = leanh::lean_ctor_get(v_inst_2100_, 0);
        leanh::lean_inc_ref(v_toApplicative_2109_);
        leanh::lean_dec_ref(v_inst_2100_);
        v_toPure_2110_ = leanh::lean_ctor_get(v_toApplicative_2109_, 1);
        leanh::lean_inc(v_toPure_2110_);
        leanh::lean_dec_ref(v_toApplicative_2109_);
        v___x_2111_ =
            leanh::lean_apply_2(v_toPure_2110_, leanh::lean_box(0), v_init_2103_);
        return v___x_2111_;
    } else {
        let mut v___f_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: u8 = 0;
        v___f_2112_ = leanh::lean_alloc_closure(
            l_Std_HashSet_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2112_, 0, v_f_2102_);
        leanh::lean_inc_ref(v_inst_2100_);
        v___f_2113_ = leanh::lean_alloc_closure(
            l_Std_HashSet_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2113_, 0, v_inst_2100_);
        leanh::lean_closure_set(v___f_2113_, 1, v___f_2112_);
        v___x_2114_ = lean_nat_dec_le(v___x_2107_, v___x_2107_);
        if v___x_2114_ == 0 {
            if v___x_2108_ == 0 {
                let mut v_toApplicative_2115_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2113_);
                leanh::lean_dec_ref(v_buckets_2105_);
                v_toApplicative_2115_ = leanh::lean_ctor_get(v_inst_2100_, 0);
                leanh::lean_inc_ref(v_toApplicative_2115_);
                leanh::lean_dec_ref(v_inst_2100_);
                v_toPure_2116_ = leanh::lean_ctor_get(v_toApplicative_2115_, 1);
                leanh::lean_inc(v_toPure_2116_);
                leanh::lean_dec_ref(v_toApplicative_2115_);
                v___x_2117_ = leanh::lean_apply_2(
                    v_toPure_2116_,
                    leanh::lean_box(0),
                    v_init_2103_,
                );
                return v___x_2117_;
            } else {
                let mut v___x_2118_: usize = 0;
                let mut v___x_2119_: usize = 0;
                let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2118_ = 0usize;
                v___x_2119_ = lean_usize_of_nat(v___x_2107_);
                v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_2100_,
                    v___f_2113_,
                    v_buckets_2105_,
                    v___x_2118_,
                    v___x_2119_,
                    v_init_2103_,
                );
                return v___x_2120_;
            }
        } else {
            let mut v___x_2121_: usize = 0;
            let mut v___x_2122_: usize = 0;
            let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2121_ = 0usize;
            v___x_2122_ = lean_usize_of_nat(v___x_2107_);
            v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_2100_,
                v___f_2113_,
                v_buckets_2105_,
                v___x_2121_,
                v___x_2122_,
                v_init_2103_,
            );
            return v___x_2123_;
        }
    }
}
pub unsafe fn l_Std_HashSet_foldM___boxed(
    mut v_00_u03b1_2124_: *mut leanh::LeanObject,
    mut v_x_2125_: *mut leanh::LeanObject,
    mut v_x_2126_: *mut leanh::LeanObject,
    mut v_m_2127_: *mut leanh::LeanObject,
    mut v_inst_2128_: *mut leanh::LeanObject,
    mut v_00_u03b2_2129_: *mut leanh::LeanObject,
    mut v_f_2130_: *mut leanh::LeanObject,
    mut v_init_2131_: *mut leanh::LeanObject,
    mut v_b_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2133_ = l_Std_HashSet_foldM(
        v_00_u03b1_2124_,
        v_x_2125_,
        v_x_2126_,
        v_m_2127_,
        v_inst_2128_,
        v_00_u03b2_2129_,
        v_f_2130_,
        v_init_2131_,
        v_b_2132_,
    );
    leanh::lean_dec_ref(v_x_2126_);
    leanh::lean_dec_ref(v_x_2125_);
    return v_res_2133_;
}
pub unsafe fn l_Std_HashSet_fold___redArg___lam__0(
    mut v_f_2134_: *mut leanh::LeanObject,
    mut v_x1_2135_: *mut leanh::LeanObject,
    mut v_x2_2136_: *mut leanh::LeanObject,
    mut v_x3_2137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2138_ = leanh::lean_apply_2(v_f_2134_, v_x1_2135_, v_x2_2136_);
    return v___x_2138_;
}
pub unsafe fn l_Std_HashSet_fold___redArg___lam__1(
    mut v___x_2139_: *mut leanh::LeanObject,
    mut v___f_2140_: *mut leanh::LeanObject,
    mut v_acc_2141_: *mut leanh::LeanObject,
    mut v_l_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2139_,
        v___f_2140_,
        v_acc_2141_,
        v_l_2142_,
    );
    return v___x_2143_;
}
pub unsafe fn l_Std_HashSet_fold___redArg(
    mut v_f_2144_: *mut leanh::LeanObject,
    mut v_init_2145_: *mut leanh::LeanObject,
    mut v_m_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    v___x_2147_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2148_ = leanh::lean_ctor_get(v_m_2146_, 1);
    leanh::lean_inc_ref(v_buckets_2148_);
    leanh::lean_dec_ref(v_m_2146_);
    v___x_2149_ = leanh::lean_unsigned_to_nat(0);
    v___x_2150_ = lean_array_get_size(v_buckets_2148_);
    v___x_2151_ = lean_nat_dec_lt(v___x_2149_, v___x_2150_);
    if v___x_2151_ == 0 {
        leanh::lean_dec_ref(v_buckets_2148_);
        leanh::lean_dec(v_f_2144_);
        return v_init_2145_;
    } else {
        let mut v___f_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: u8 = 0;
        v___f_2152_ = leanh::lean_alloc_closure(
            l_Std_HashSet_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2152_, 0, v_f_2144_);
        v___f_2153_ = leanh::lean_alloc_closure(
            l_Std_HashSet_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2153_, 0, v___x_2147_);
        leanh::lean_closure_set(v___f_2153_, 1, v___f_2152_);
        v___x_2154_ = lean_nat_dec_le(v___x_2150_, v___x_2150_);
        if v___x_2154_ == 0 {
            if v___x_2151_ == 0 {
                leanh::lean_dec_ref(v___f_2153_);
                leanh::lean_dec_ref(v_buckets_2148_);
                return v_init_2145_;
            } else {
                let mut v___x_2155_: usize = 0;
                let mut v___x_2156_: usize = 0;
                let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2155_ = 0usize;
                v___x_2156_ = lean_usize_of_nat(v___x_2150_);
                v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2147_,
                    v___f_2153_,
                    v_buckets_2148_,
                    v___x_2155_,
                    v___x_2156_,
                    v_init_2145_,
                );
                return v___x_2157_;
            }
        } else {
            let mut v___x_2158_: usize = 0;
            let mut v___x_2159_: usize = 0;
            let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2158_ = 0usize;
            v___x_2159_ = lean_usize_of_nat(v___x_2150_);
            v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2147_,
                v___f_2153_,
                v_buckets_2148_,
                v___x_2158_,
                v___x_2159_,
                v_init_2145_,
            );
            return v___x_2160_;
        }
    }
}
pub unsafe fn l_Std_HashSet_fold(
    mut v_00_u03b1_2161_: *mut leanh::LeanObject,
    mut v_x_2162_: *mut leanh::LeanObject,
    mut v_x_2163_: *mut leanh::LeanObject,
    mut v_00_u03b2_2164_: *mut leanh::LeanObject,
    mut v_f_2165_: *mut leanh::LeanObject,
    mut v_init_2166_: *mut leanh::LeanObject,
    mut v_m_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u8 = 0;
    v___x_2168_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2169_ = leanh::lean_ctor_get(v_m_2167_, 1);
    leanh::lean_inc_ref(v_buckets_2169_);
    leanh::lean_dec_ref(v_m_2167_);
    v___x_2170_ = leanh::lean_unsigned_to_nat(0);
    v___x_2171_ = lean_array_get_size(v_buckets_2169_);
    v___x_2172_ = lean_nat_dec_lt(v___x_2170_, v___x_2171_);
    if v___x_2172_ == 0 {
        leanh::lean_dec_ref(v_buckets_2169_);
        leanh::lean_dec(v_f_2165_);
        return v_init_2166_;
    } else {
        let mut v___f_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2175_: u8 = 0;
        v___f_2173_ = leanh::lean_alloc_closure(
            l_Std_HashSet_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2173_, 0, v_f_2165_);
        v___f_2174_ = leanh::lean_alloc_closure(
            l_Std_HashSet_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2174_, 0, v___x_2168_);
        leanh::lean_closure_set(v___f_2174_, 1, v___f_2173_);
        v___x_2175_ = lean_nat_dec_le(v___x_2171_, v___x_2171_);
        if v___x_2175_ == 0 {
            if v___x_2172_ == 0 {
                leanh::lean_dec_ref(v___f_2174_);
                leanh::lean_dec_ref(v_buckets_2169_);
                return v_init_2166_;
            } else {
                let mut v___x_2176_: usize = 0;
                let mut v___x_2177_: usize = 0;
                let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2176_ = 0usize;
                v___x_2177_ = lean_usize_of_nat(v___x_2171_);
                v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2168_,
                    v___f_2174_,
                    v_buckets_2169_,
                    v___x_2176_,
                    v___x_2177_,
                    v_init_2166_,
                );
                return v___x_2178_;
            }
        } else {
            let mut v___x_2179_: usize = 0;
            let mut v___x_2180_: usize = 0;
            let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2179_ = 0usize;
            v___x_2180_ = lean_usize_of_nat(v___x_2171_);
            v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2168_,
                v___f_2174_,
                v_buckets_2169_,
                v___x_2179_,
                v___x_2180_,
                v_init_2166_,
            );
            return v___x_2181_;
        }
    }
}
pub unsafe fn l_Std_HashSet_fold___boxed(
    mut v_00_u03b1_2182_: *mut leanh::LeanObject,
    mut v_x_2183_: *mut leanh::LeanObject,
    mut v_x_2184_: *mut leanh::LeanObject,
    mut v_00_u03b2_2185_: *mut leanh::LeanObject,
    mut v_f_2186_: *mut leanh::LeanObject,
    mut v_init_2187_: *mut leanh::LeanObject,
    mut v_m_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2189_ = l_Std_HashSet_fold(
        v_00_u03b1_2182_,
        v_x_2183_,
        v_x_2184_,
        v_00_u03b2_2185_,
        v_f_2186_,
        v_init_2187_,
        v_m_2188_,
    );
    leanh::lean_dec_ref(v_x_2184_);
    leanh::lean_dec_ref(v_x_2183_);
    return v_res_2189_;
}
pub unsafe fn l_Std_HashSet_forM___redArg___lam__0(
    mut v_f_2190_: *mut leanh::LeanObject,
    mut v_x_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = leanh::lean_apply_1(v_f_2190_, v___y_2192_);
    return v___x_2194_;
}
pub unsafe fn l_Std_HashSet_forM___redArg___lam__1(
    mut v_inst_2195_: *mut leanh::LeanObject,
    mut v___f_2196_: *mut leanh::LeanObject,
    mut v_x_2197_: *mut leanh::LeanObject,
    mut v___y_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = leanh::lean_box(0);
    v___x_2200_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2195_,
        v___f_2196_,
        v___x_2199_,
        v___y_2198_,
    );
    return v___x_2200_;
}
pub unsafe fn l_Std_HashSet_forM___redArg(
    mut v_inst_2201_: *mut leanh::LeanObject,
    mut v_f_2202_: *mut leanh::LeanObject,
    mut v_b_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    v_buckets_2204_ = leanh::lean_ctor_get(v_b_2203_, 1);
    leanh::lean_inc_ref(v_buckets_2204_);
    leanh::lean_dec_ref(v_b_2203_);
    v___x_2205_ = leanh::lean_unsigned_to_nat(0);
    v___x_2206_ = lean_array_get_size(v_buckets_2204_);
    v___x_2207_ = leanh::lean_box(0);
    v___x_2208_ = lean_nat_dec_lt(v___x_2205_, v___x_2206_);
    if v___x_2208_ == 0 {
        let mut v_toApplicative_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2204_);
        leanh::lean_dec(v_f_2202_);
        v_toApplicative_2209_ = leanh::lean_ctor_get(v_inst_2201_, 0);
        leanh::lean_inc_ref(v_toApplicative_2209_);
        leanh::lean_dec_ref(v_inst_2201_);
        v_toPure_2210_ = leanh::lean_ctor_get(v_toApplicative_2209_, 1);
        leanh::lean_inc(v_toPure_2210_);
        leanh::lean_dec_ref(v_toApplicative_2209_);
        v___x_2211_ =
            leanh::lean_apply_2(v_toPure_2210_, leanh::lean_box(0), v___x_2207_);
        return v___x_2211_;
    } else {
        let mut v___f_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2214_: u8 = 0;
        v___f_2212_ = leanh::lean_alloc_closure(
            l_Std_HashSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2212_, 0, v_f_2202_);
        leanh::lean_inc_ref(v_inst_2201_);
        v___f_2213_ = leanh::lean_alloc_closure(
            l_Std_HashSet_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2213_, 0, v_inst_2201_);
        leanh::lean_closure_set(v___f_2213_, 1, v___f_2212_);
        v___x_2214_ = lean_nat_dec_le(v___x_2206_, v___x_2206_);
        if v___x_2214_ == 0 {
            if v___x_2208_ == 0 {
                let mut v_toApplicative_2215_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2213_);
                leanh::lean_dec_ref(v_buckets_2204_);
                v_toApplicative_2215_ = leanh::lean_ctor_get(v_inst_2201_, 0);
                leanh::lean_inc_ref(v_toApplicative_2215_);
                leanh::lean_dec_ref(v_inst_2201_);
                v_toPure_2216_ = leanh::lean_ctor_get(v_toApplicative_2215_, 1);
                leanh::lean_inc(v_toPure_2216_);
                leanh::lean_dec_ref(v_toApplicative_2215_);
                v___x_2217_ = leanh::lean_apply_2(
                    v_toPure_2216_,
                    leanh::lean_box(0),
                    v___x_2207_,
                );
                return v___x_2217_;
            } else {
                let mut v___x_2218_: usize = 0;
                let mut v___x_2219_: usize = 0;
                let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2218_ = 0usize;
                v___x_2219_ = lean_usize_of_nat(v___x_2206_);
                v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_2201_,
                    v___f_2213_,
                    v_buckets_2204_,
                    v___x_2218_,
                    v___x_2219_,
                    v___x_2207_,
                );
                return v___x_2220_;
            }
        } else {
            let mut v___x_2221_: usize = 0;
            let mut v___x_2222_: usize = 0;
            let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2221_ = 0usize;
            v___x_2222_ = lean_usize_of_nat(v___x_2206_);
            v___x_2223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_2201_,
                v___f_2213_,
                v_buckets_2204_,
                v___x_2221_,
                v___x_2222_,
                v___x_2207_,
            );
            return v___x_2223_;
        }
    }
}
pub unsafe fn l_Std_HashSet_forM(
    mut v_00_u03b1_2224_: *mut leanh::LeanObject,
    mut v_x_2225_: *mut leanh::LeanObject,
    mut v_x_2226_: *mut leanh::LeanObject,
    mut v_m_2227_: *mut leanh::LeanObject,
    mut v_inst_2228_: *mut leanh::LeanObject,
    mut v_f_2229_: *mut leanh::LeanObject,
    mut v_b_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    v_buckets_2231_ = leanh::lean_ctor_get(v_b_2230_, 1);
    leanh::lean_inc_ref(v_buckets_2231_);
    leanh::lean_dec_ref(v_b_2230_);
    v___x_2232_ = leanh::lean_unsigned_to_nat(0);
    v___x_2233_ = lean_array_get_size(v_buckets_2231_);
    v___x_2234_ = leanh::lean_box(0);
    v___x_2235_ = lean_nat_dec_lt(v___x_2232_, v___x_2233_);
    if v___x_2235_ == 0 {
        let mut v_toApplicative_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2231_);
        leanh::lean_dec(v_f_2229_);
        v_toApplicative_2236_ = leanh::lean_ctor_get(v_inst_2228_, 0);
        leanh::lean_inc_ref(v_toApplicative_2236_);
        leanh::lean_dec_ref(v_inst_2228_);
        v_toPure_2237_ = leanh::lean_ctor_get(v_toApplicative_2236_, 1);
        leanh::lean_inc(v_toPure_2237_);
        leanh::lean_dec_ref(v_toApplicative_2236_);
        v___x_2238_ =
            leanh::lean_apply_2(v_toPure_2237_, leanh::lean_box(0), v___x_2234_);
        return v___x_2238_;
    } else {
        let mut v___f_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: u8 = 0;
        v___f_2239_ = leanh::lean_alloc_closure(
            l_Std_HashSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2239_, 0, v_f_2229_);
        leanh::lean_inc_ref(v_inst_2228_);
        v___f_2240_ = leanh::lean_alloc_closure(
            l_Std_HashSet_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2240_, 0, v_inst_2228_);
        leanh::lean_closure_set(v___f_2240_, 1, v___f_2239_);
        v___x_2241_ = lean_nat_dec_le(v___x_2233_, v___x_2233_);
        if v___x_2241_ == 0 {
            if v___x_2235_ == 0 {
                let mut v_toApplicative_2242_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2240_);
                leanh::lean_dec_ref(v_buckets_2231_);
                v_toApplicative_2242_ = leanh::lean_ctor_get(v_inst_2228_, 0);
                leanh::lean_inc_ref(v_toApplicative_2242_);
                leanh::lean_dec_ref(v_inst_2228_);
                v_toPure_2243_ = leanh::lean_ctor_get(v_toApplicative_2242_, 1);
                leanh::lean_inc(v_toPure_2243_);
                leanh::lean_dec_ref(v_toApplicative_2242_);
                v___x_2244_ = leanh::lean_apply_2(
                    v_toPure_2243_,
                    leanh::lean_box(0),
                    v___x_2234_,
                );
                return v___x_2244_;
            } else {
                let mut v___x_2245_: usize = 0;
                let mut v___x_2246_: usize = 0;
                let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2245_ = 0usize;
                v___x_2246_ = lean_usize_of_nat(v___x_2233_);
                v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_2228_,
                    v___f_2240_,
                    v_buckets_2231_,
                    v___x_2245_,
                    v___x_2246_,
                    v___x_2234_,
                );
                return v___x_2247_;
            }
        } else {
            let mut v___x_2248_: usize = 0;
            let mut v___x_2249_: usize = 0;
            let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2248_ = 0usize;
            v___x_2249_ = lean_usize_of_nat(v___x_2233_);
            v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_2228_,
                v___f_2240_,
                v_buckets_2231_,
                v___x_2248_,
                v___x_2249_,
                v___x_2234_,
            );
            return v___x_2250_;
        }
    }
}
pub unsafe fn l_Std_HashSet_forM___boxed(
    mut v_00_u03b1_2251_: *mut leanh::LeanObject,
    mut v_x_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
    mut v_m_2254_: *mut leanh::LeanObject,
    mut v_inst_2255_: *mut leanh::LeanObject,
    mut v_f_2256_: *mut leanh::LeanObject,
    mut v_b_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_Std_HashSet_forM(
        v_00_u03b1_2251_,
        v_x_2252_,
        v_x_2253_,
        v_m_2254_,
        v_inst_2255_,
        v_f_2256_,
        v_b_2257_,
    );
    leanh::lean_dec_ref(v_x_2253_);
    leanh::lean_dec_ref(v_x_2252_);
    return v_res_2258_;
}
pub unsafe fn l_Std_HashSet_forIn___redArg___lam__0(
    mut v_f_2259_: *mut leanh::LeanObject,
    mut v_a_2260_: *mut leanh::LeanObject,
    mut v_x_2261_: *mut leanh::LeanObject,
    mut v_acc_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = leanh::lean_apply_2(v_f_2259_, v_a_2260_, v_acc_2262_);
    return v___x_2263_;
}
pub unsafe fn l_Std_HashSet_forIn___redArg___lam__1(
    mut v_inst_2264_: *mut leanh::LeanObject,
    mut v___f_2265_: *mut leanh::LeanObject,
    mut v_a_2266_: *mut leanh::LeanObject,
    mut v_x_2267_: *mut leanh::LeanObject,
    mut v___y_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2269_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_inst_2264_, v___f_2265_, v_a_2266_, v___y_2268_);
    return v___x_2269_;
}
pub unsafe fn l_Std_HashSet_forIn___redArg(
    mut v_inst_2270_: *mut leanh::LeanObject,
    mut v_f_2271_: *mut leanh::LeanObject,
    mut v_init_2272_: *mut leanh::LeanObject,
    mut v_b_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2277_: usize = 0;
    let mut v___x_2278_: usize = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2274_ = leanh::lean_ctor_get(v_b_2273_, 1);
    leanh::lean_inc_ref(v_buckets_2274_);
    leanh::lean_dec_ref(v_b_2273_);
    v___f_2275_ = leanh::lean_alloc_closure(
        l_Std_HashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2275_, 0, v_f_2271_);
    leanh::lean_inc_ref(v_inst_2270_);
    v___f_2276_ = leanh::lean_alloc_closure(
        l_Std_HashSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2276_, 0, v_inst_2270_);
    leanh::lean_closure_set(v___f_2276_, 1, v___f_2275_);
    v_sz_2277_ = lean_array_size(v_buckets_2274_);
    v___x_2278_ = 0usize;
    v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2270_,
        v_buckets_2274_,
        v___f_2276_,
        v_sz_2277_,
        v___x_2278_,
        v_init_2272_,
    );
    return v___x_2279_;
}
pub unsafe fn l_Std_HashSet_forIn(
    mut v_00_u03b1_2280_: *mut leanh::LeanObject,
    mut v_x_2281_: *mut leanh::LeanObject,
    mut v_x_2282_: *mut leanh::LeanObject,
    mut v_m_2283_: *mut leanh::LeanObject,
    mut v_inst_2284_: *mut leanh::LeanObject,
    mut v_00_u03b2_2285_: *mut leanh::LeanObject,
    mut v_f_2286_: *mut leanh::LeanObject,
    mut v_init_2287_: *mut leanh::LeanObject,
    mut v_b_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2292_: usize = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2289_ = leanh::lean_ctor_get(v_b_2288_, 1);
    leanh::lean_inc_ref(v_buckets_2289_);
    leanh::lean_dec_ref(v_b_2288_);
    v___f_2290_ = leanh::lean_alloc_closure(
        l_Std_HashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2290_, 0, v_f_2286_);
    leanh::lean_inc_ref(v_inst_2284_);
    v___f_2291_ = leanh::lean_alloc_closure(
        l_Std_HashSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2291_, 0, v_inst_2284_);
    leanh::lean_closure_set(v___f_2291_, 1, v___f_2290_);
    v_sz_2292_ = lean_array_size(v_buckets_2289_);
    v___x_2293_ = 0usize;
    v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2284_,
        v_buckets_2289_,
        v___f_2291_,
        v_sz_2292_,
        v___x_2293_,
        v_init_2287_,
    );
    return v___x_2294_;
}
pub unsafe fn l_Std_HashSet_forIn___boxed(
    mut v_00_u03b1_2295_: *mut leanh::LeanObject,
    mut v_x_2296_: *mut leanh::LeanObject,
    mut v_x_2297_: *mut leanh::LeanObject,
    mut v_m_2298_: *mut leanh::LeanObject,
    mut v_inst_2299_: *mut leanh::LeanObject,
    mut v_00_u03b2_2300_: *mut leanh::LeanObject,
    mut v_f_2301_: *mut leanh::LeanObject,
    mut v_init_2302_: *mut leanh::LeanObject,
    mut v_b_2303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2304_ = l_Std_HashSet_forIn(
        v_00_u03b1_2295_,
        v_x_2296_,
        v_x_2297_,
        v_m_2298_,
        v_inst_2299_,
        v_00_u03b2_2300_,
        v_f_2301_,
        v_init_2302_,
        v_b_2303_,
    );
    leanh::lean_dec_ref(v_x_2297_);
    leanh::lean_dec_ref(v_x_2296_);
    return v_res_2304_;
}
pub unsafe fn l_Std_HashSet_instForMOfMonad___redArg___lam__2(
    mut v_inst_2305_: *mut leanh::LeanObject,
    mut v_m_2306_: *mut leanh::LeanObject,
    mut v_f_2307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: u8 = 0;
    v_buckets_2308_ = leanh::lean_ctor_get(v_m_2306_, 1);
    leanh::lean_inc_ref(v_buckets_2308_);
    leanh::lean_dec_ref(v_m_2306_);
    v___x_2309_ = leanh::lean_unsigned_to_nat(0);
    v___x_2310_ = lean_array_get_size(v_buckets_2308_);
    v___x_2311_ = leanh::lean_box(0);
    v___x_2312_ = lean_nat_dec_lt(v___x_2309_, v___x_2310_);
    if v___x_2312_ == 0 {
        let mut v_toApplicative_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2308_);
        leanh::lean_dec(v_f_2307_);
        v_toApplicative_2313_ = leanh::lean_ctor_get(v_inst_2305_, 0);
        leanh::lean_inc_ref(v_toApplicative_2313_);
        leanh::lean_dec_ref(v_inst_2305_);
        v_toPure_2314_ = leanh::lean_ctor_get(v_toApplicative_2313_, 1);
        leanh::lean_inc(v_toPure_2314_);
        leanh::lean_dec_ref(v_toApplicative_2313_);
        v___x_2315_ =
            leanh::lean_apply_2(v_toPure_2314_, leanh::lean_box(0), v___x_2311_);
        return v___x_2315_;
    } else {
        let mut v___f_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2318_: u8 = 0;
        v___f_2316_ = leanh::lean_alloc_closure(
            l_Std_HashSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2316_, 0, v_f_2307_);
        leanh::lean_inc_ref(v_inst_2305_);
        v___f_2317_ = leanh::lean_alloc_closure(
            l_Std_HashSet_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2317_, 0, v_inst_2305_);
        leanh::lean_closure_set(v___f_2317_, 1, v___f_2316_);
        v___x_2318_ = lean_nat_dec_le(v___x_2310_, v___x_2310_);
        if v___x_2318_ == 0 {
            if v___x_2312_ == 0 {
                let mut v_toApplicative_2319_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2317_);
                leanh::lean_dec_ref(v_buckets_2308_);
                v_toApplicative_2319_ = leanh::lean_ctor_get(v_inst_2305_, 0);
                leanh::lean_inc_ref(v_toApplicative_2319_);
                leanh::lean_dec_ref(v_inst_2305_);
                v_toPure_2320_ = leanh::lean_ctor_get(v_toApplicative_2319_, 1);
                leanh::lean_inc(v_toPure_2320_);
                leanh::lean_dec_ref(v_toApplicative_2319_);
                v___x_2321_ = leanh::lean_apply_2(
                    v_toPure_2320_,
                    leanh::lean_box(0),
                    v___x_2311_,
                );
                return v___x_2321_;
            } else {
                let mut v___x_2322_: usize = 0;
                let mut v___x_2323_: usize = 0;
                let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2322_ = 0usize;
                v___x_2323_ = lean_usize_of_nat(v___x_2310_);
                v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_2305_,
                    v___f_2317_,
                    v_buckets_2308_,
                    v___x_2322_,
                    v___x_2323_,
                    v___x_2311_,
                );
                return v___x_2324_;
            }
        } else {
            let mut v___x_2325_: usize = 0;
            let mut v___x_2326_: usize = 0;
            let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2325_ = 0usize;
            v___x_2326_ = lean_usize_of_nat(v___x_2310_);
            v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_2305_,
                v___f_2317_,
                v_buckets_2308_,
                v___x_2325_,
                v___x_2326_,
                v___x_2311_,
            );
            return v___x_2327_;
        }
    }
}
pub unsafe fn l_Std_HashSet_instForMOfMonad___redArg(
    mut v_inst_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2329_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2329_, 0, v_inst_2328_);
    return v___f_2329_;
}
pub unsafe fn l_Std_HashSet_instForMOfMonad(
    mut v_00_u03b1_2330_: *mut leanh::LeanObject,
    mut v_inst_2331_: *mut leanh::LeanObject,
    mut v_inst_2332_: *mut leanh::LeanObject,
    mut v_m_2333_: *mut leanh::LeanObject,
    mut v_inst_2334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2335_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2335_, 0, v_inst_2334_);
    return v___f_2335_;
}
pub unsafe fn l_Std_HashSet_instForMOfMonad___boxed(
    mut v_00_u03b1_2336_: *mut leanh::LeanObject,
    mut v_inst_2337_: *mut leanh::LeanObject,
    mut v_inst_2338_: *mut leanh::LeanObject,
    mut v_m_2339_: *mut leanh::LeanObject,
    mut v_inst_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Std_HashSet_instForMOfMonad(
        v_00_u03b1_2336_,
        v_inst_2337_,
        v_inst_2338_,
        v_m_2339_,
        v_inst_2340_,
    );
    leanh::lean_dec_ref(v_inst_2338_);
    leanh::lean_dec_ref(v_inst_2337_);
    return v_res_2341_;
}
pub unsafe fn l_Std_HashSet_instForInOfMonad___redArg___lam__2(
    mut v_inst_2342_: *mut leanh::LeanObject,
    mut v_00_u03b2_2343_: *mut leanh::LeanObject,
    mut v_m_2344_: *mut leanh::LeanObject,
    mut v_init_2345_: *mut leanh::LeanObject,
    mut v_f_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2350_: usize = 0;
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2347_ = leanh::lean_ctor_get(v_m_2344_, 1);
    leanh::lean_inc_ref(v_buckets_2347_);
    leanh::lean_dec_ref(v_m_2344_);
    v___f_2348_ = leanh::lean_alloc_closure(
        l_Std_HashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2348_, 0, v_f_2346_);
    leanh::lean_inc_ref(v_inst_2342_);
    v___f_2349_ = leanh::lean_alloc_closure(
        l_Std_HashSet_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2349_, 0, v_inst_2342_);
    leanh::lean_closure_set(v___f_2349_, 1, v___f_2348_);
    v_sz_2350_ = lean_array_size(v_buckets_2347_);
    v___x_2351_ = 0usize;
    v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2342_,
        v_buckets_2347_,
        v___f_2349_,
        v_sz_2350_,
        v___x_2351_,
        v_init_2345_,
    );
    return v___x_2352_;
}
pub unsafe fn l_Std_HashSet_instForInOfMonad___redArg(
    mut v_inst_2353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2354_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2354_, 0, v_inst_2353_);
    return v___f_2354_;
}
pub unsafe fn l_Std_HashSet_instForInOfMonad(
    mut v_00_u03b1_2355_: *mut leanh::LeanObject,
    mut v_inst_2356_: *mut leanh::LeanObject,
    mut v_inst_2357_: *mut leanh::LeanObject,
    mut v_m_2358_: *mut leanh::LeanObject,
    mut v_inst_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2360_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2360_, 0, v_inst_2359_);
    return v___f_2360_;
}
pub unsafe fn l_Std_HashSet_instForInOfMonad___boxed(
    mut v_00_u03b1_2361_: *mut leanh::LeanObject,
    mut v_inst_2362_: *mut leanh::LeanObject,
    mut v_inst_2363_: *mut leanh::LeanObject,
    mut v_m_2364_: *mut leanh::LeanObject,
    mut v_inst_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2366_ = l_Std_HashSet_instForInOfMonad(
        v_00_u03b1_2361_,
        v_inst_2362_,
        v_inst_2363_,
        v_m_2364_,
        v_inst_2365_,
    );
    leanh::lean_dec_ref(v_inst_2363_);
    leanh::lean_dec_ref(v_inst_2362_);
    return v_res_2366_;
}
pub unsafe fn l_Std_HashSet_filter___redArg___lam__0(
    mut v_f_2367_: *mut leanh::LeanObject,
    mut v_a_2368_: *mut leanh::LeanObject,
    mut v_x_2369_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    v___x_2370_ = leanh::lean_apply_1(v_f_2367_, v_a_2368_);
    v___x_2371_ = (leanh::lean_unbox(v___x_2370_) as u8);
    return v___x_2371_;
}
pub unsafe fn l_Std_HashSet_filter___redArg___lam__0___boxed(
    mut v_f_2372_: *mut leanh::LeanObject,
    mut v_a_2373_: *mut leanh::LeanObject,
    mut v_x_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2375_: u8 = 0;
    let mut v_r_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2375_ = l_Std_HashSet_filter___redArg___lam__0(v_f_2372_, v_a_2373_, v_x_2374_);
    v_r_2376_ = leanh::lean_box((v_res_2375_) as usize);
    return v_r_2376_;
}
pub unsafe fn l_Std_HashSet_filter___redArg(
    mut v_f_2377_: *mut leanh::LeanObject,
    mut v_m_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2379_ = leanh::lean_alloc_closure(
        l_Std_HashSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2379_, 0, v_f_2377_);
    v___x_2380_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2379_, v_m_2378_);
    return v___x_2380_;
}
pub unsafe fn l_Std_HashSet_filter(
    mut v_00_u03b1_2381_: *mut leanh::LeanObject,
    mut v_x_2382_: *mut leanh::LeanObject,
    mut v_x_2383_: *mut leanh::LeanObject,
    mut v_f_2384_: *mut leanh::LeanObject,
    mut v_m_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2386_ = leanh::lean_alloc_closure(
        l_Std_HashSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2386_, 0, v_f_2384_);
    v___x_2387_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2386_, v_m_2385_);
    return v___x_2387_;
}
pub unsafe fn l_Std_HashSet_filter___boxed(
    mut v_00_u03b1_2388_: *mut leanh::LeanObject,
    mut v_x_2389_: *mut leanh::LeanObject,
    mut v_x_2390_: *mut leanh::LeanObject,
    mut v_f_2391_: *mut leanh::LeanObject,
    mut v_m_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2393_ =
        l_Std_HashSet_filter(v_00_u03b1_2388_, v_x_2389_, v_x_2390_, v_f_2391_, v_m_2392_);
    leanh::lean_dec_ref(v_x_2390_);
    leanh::lean_dec_ref(v_x_2389_);
    return v_res_2393_;
}
pub unsafe fn l_Std_HashSet_insertMany___redArg(
    mut v_x_2394_: *mut leanh::LeanObject,
    mut v_x_2395_: *mut leanh::LeanObject,
    mut v_inst_2396_: *mut leanh::LeanObject,
    mut v_m_2397_: *mut leanh::LeanObject,
    mut v_l_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v_inst_2396_,
        v_x_2394_,
        v_x_2395_,
        v_m_2397_,
        v_l_2398_,
    );
    return v___x_2399_;
}
pub unsafe fn l_Std_HashSet_insertMany(
    mut v_00_u03b1_2400_: *mut leanh::LeanObject,
    mut v_x_2401_: *mut leanh::LeanObject,
    mut v_x_2402_: *mut leanh::LeanObject,
    mut v_00_u03c1_2403_: *mut leanh::LeanObject,
    mut v_inst_2404_: *mut leanh::LeanObject,
    mut v_m_2405_: *mut leanh::LeanObject,
    mut v_l_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v_inst_2404_,
        v_x_2401_,
        v_x_2402_,
        v_m_2405_,
        v_l_2406_,
    );
    return v___x_2407_;
}
pub unsafe fn l_Std_HashSet_toArray___redArg___lam__0(
    mut v_x1_2408_: *mut leanh::LeanObject,
    mut v_x2_2409_: *mut leanh::LeanObject,
    mut v_x3_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = lean_array_push(v_x1_2408_, v_x2_2409_);
    return v___x_2411_;
}
pub unsafe fn l_Std_HashSet_toArray___redArg___lam__1(
    mut v___x_2412_: *mut leanh::LeanObject,
    mut v___f_2413_: *mut leanh::LeanObject,
    mut v_acc_2414_: *mut leanh::LeanObject,
    mut v_l_2415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2412_,
        v___f_2413_,
        v_acc_2414_,
        v_l_2415_,
    );
    return v___x_2416_;
}
pub unsafe fn l_Std_HashSet_toArray___redArg(
    mut v_m_2421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: u8 = 0;
    v_size_2422_ = leanh::lean_ctor_get(v_m_2421_, 0);
    leanh::lean_inc(v_size_2422_);
    v_buckets_2423_ = leanh::lean_ctor_get(v_m_2421_, 1);
    leanh::lean_inc_ref(v_buckets_2423_);
    leanh::lean_dec_ref(v_m_2421_);
    v___x_2424_ = lean_mk_empty_array_with_capacity(v_size_2422_);
    leanh::lean_dec(v_size_2422_);
    v___x_2425_ = l_Std_HashSet_toList___redArg___closed__9;
    v___x_2426_ = leanh::lean_unsigned_to_nat(0);
    v___x_2427_ = lean_array_get_size(v_buckets_2423_);
    v___x_2428_ = lean_nat_dec_lt(v___x_2426_, v___x_2427_);
    if v___x_2428_ == 0 {
        leanh::lean_dec_ref(v_buckets_2423_);
        return v___x_2424_;
    } else {
        let mut v___f_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2430_: u8 = 0;
        v___f_2429_ = l_Std_HashSet_toArray___redArg___closed__1;
        v___x_2430_ = lean_nat_dec_le(v___x_2427_, v___x_2427_);
        if v___x_2430_ == 0 {
            if v___x_2428_ == 0 {
                leanh::lean_dec_ref(v_buckets_2423_);
                return v___x_2424_;
            } else {
                let mut v___x_2431_: usize = 0;
                let mut v___x_2432_: usize = 0;
                let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2431_ = 0usize;
                v___x_2432_ = lean_usize_of_nat(v___x_2427_);
                v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2425_,
                    v___f_2429_,
                    v_buckets_2423_,
                    v___x_2431_,
                    v___x_2432_,
                    v___x_2424_,
                );
                return v___x_2433_;
            }
        } else {
            let mut v___x_2434_: usize = 0;
            let mut v___x_2435_: usize = 0;
            let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2434_ = 0usize;
            v___x_2435_ = lean_usize_of_nat(v___x_2427_);
            v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2425_,
                v___f_2429_,
                v_buckets_2423_,
                v___x_2434_,
                v___x_2435_,
                v___x_2424_,
            );
            return v___x_2436_;
        }
    }
}
pub unsafe fn l_Std_HashSet_toArray(
    mut v_00_u03b1_2437_: *mut leanh::LeanObject,
    mut v_x_2438_: *mut leanh::LeanObject,
    mut v_x_2439_: *mut leanh::LeanObject,
    mut v_m_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    v_size_2441_ = leanh::lean_ctor_get(v_m_2440_, 0);
    leanh::lean_inc(v_size_2441_);
    v_buckets_2442_ = leanh::lean_ctor_get(v_m_2440_, 1);
    leanh::lean_inc_ref(v_buckets_2442_);
    leanh::lean_dec_ref(v_m_2440_);
    v___x_2443_ = lean_mk_empty_array_with_capacity(v_size_2441_);
    leanh::lean_dec(v_size_2441_);
    v___x_2444_ = l_Std_HashSet_toList___redArg___closed__9;
    v___x_2445_ = leanh::lean_unsigned_to_nat(0);
    v___x_2446_ = lean_array_get_size(v_buckets_2442_);
    v___x_2447_ = lean_nat_dec_lt(v___x_2445_, v___x_2446_);
    if v___x_2447_ == 0 {
        leanh::lean_dec_ref(v_buckets_2442_);
        return v___x_2443_;
    } else {
        let mut v___f_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2449_: u8 = 0;
        v___f_2448_ = l_Std_HashSet_toArray___redArg___closed__1;
        v___x_2449_ = lean_nat_dec_le(v___x_2446_, v___x_2446_);
        if v___x_2449_ == 0 {
            if v___x_2447_ == 0 {
                leanh::lean_dec_ref(v_buckets_2442_);
                return v___x_2443_;
            } else {
                let mut v___x_2450_: usize = 0;
                let mut v___x_2451_: usize = 0;
                let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2450_ = 0usize;
                v___x_2451_ = lean_usize_of_nat(v___x_2446_);
                v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2444_,
                    v___f_2448_,
                    v_buckets_2442_,
                    v___x_2450_,
                    v___x_2451_,
                    v___x_2443_,
                );
                return v___x_2452_;
            }
        } else {
            let mut v___x_2453_: usize = 0;
            let mut v___x_2454_: usize = 0;
            let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2453_ = 0usize;
            v___x_2454_ = lean_usize_of_nat(v___x_2446_);
            v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2444_,
                v___f_2448_,
                v_buckets_2442_,
                v___x_2453_,
                v___x_2454_,
                v___x_2443_,
            );
            return v___x_2455_;
        }
    }
}
pub unsafe fn l_Std_HashSet_toArray___boxed(
    mut v_00_u03b1_2456_: *mut leanh::LeanObject,
    mut v_x_2457_: *mut leanh::LeanObject,
    mut v_x_2458_: *mut leanh::LeanObject,
    mut v_m_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2460_ = l_Std_HashSet_toArray(v_00_u03b1_2456_, v_x_2457_, v_x_2458_, v_m_2459_);
    leanh::lean_dec_ref(v_x_2458_);
    leanh::lean_dec_ref(v_x_2457_);
    return v_res_2460_;
}
pub unsafe fn l_Std_HashSet_all___redArg___lam__0(
    mut v_p_2461_: *mut leanh::LeanObject,
    mut v___x_2462_: *mut leanh::LeanObject,
    mut v___x_2463_: *mut leanh::LeanObject,
    mut v_a_2464_: *mut leanh::LeanObject,
    mut v_b_2465_: *mut leanh::LeanObject,
    mut v_acc_2466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: u8 = 0;
    v___x_2467_ = leanh::lean_apply_1(v_p_2461_, v_a_2464_);
    v___x_2468_ = (leanh::lean_unbox(v___x_2467_) as u8);
    if v___x_2468_ == 0 {
        let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2463_);
        v___x_2469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2469_, 0, v___x_2467_);
        v___x_2470_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2470_, 0, v___x_2469_);
        leanh::lean_ctor_set(v___x_2470_, 1, v___x_2462_);
        v___x_2471_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2471_, 0, v___x_2470_);
        return v___x_2471_;
    } else {
        let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2472_, 0, v___x_2463_);
        return v___x_2472_;
    }
}
pub unsafe fn l_Std_HashSet_all___redArg___lam__0___boxed(
    mut v_p_2473_: *mut leanh::LeanObject,
    mut v___x_2474_: *mut leanh::LeanObject,
    mut v___x_2475_: *mut leanh::LeanObject,
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_b_2477_: *mut leanh::LeanObject,
    mut v_acc_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_Std_HashSet_all___redArg___lam__0(
        v_p_2473_,
        v___x_2474_,
        v___x_2475_,
        v_a_2476_,
        v_b_2477_,
        v_acc_2478_,
    );
    leanh::lean_dec_ref(v_acc_2478_);
    return v_res_2479_;
}
pub unsafe fn l_Std_HashSet_all___redArg___lam__1(
    mut v___x_2480_: *mut leanh::LeanObject,
    mut v___f_2481_: *mut leanh::LeanObject,
    mut v_a_2482_: *mut leanh::LeanObject,
    mut v_x_2483_: *mut leanh::LeanObject,
    mut v___y_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_2480_, v___f_2481_, v_a_2482_, v___y_2484_);
    return v___x_2485_;
}
pub unsafe fn l_Std_HashSet_all___redArg(
    mut v_m_2489_: *mut leanh::LeanObject,
    mut v_p_2490_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2497_: usize = 0;
    let mut v___x_2498_: usize = 0;
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2492_ = leanh::lean_ctor_get(v_m_2489_, 1);
    leanh::lean_inc_ref(v_buckets_2492_);
    leanh::lean_dec_ref(v_m_2489_);
    v___x_2493_ = leanh::lean_box(0);
    v___x_2494_ = l_Std_HashSet_all___redArg___closed__0;
    v___f_2495_ = leanh::lean_alloc_closure(
        l_Std_HashSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2495_, 0, v_p_2490_);
    leanh::lean_closure_set(v___f_2495_, 1, v___x_2493_);
    leanh::lean_closure_set(v___f_2495_, 2, v___x_2494_);
    v___f_2496_ = leanh::lean_alloc_closure(
        l_Std_HashSet_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2496_, 0, v___x_2491_);
    leanh::lean_closure_set(v___f_2496_, 1, v___f_2495_);
    v_sz_2497_ = lean_array_size(v_buckets_2492_);
    v___x_2498_ = 0usize;
    v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2491_,
        v_buckets_2492_,
        v___f_2496_,
        v_sz_2497_,
        v___x_2498_,
        v___x_2494_,
    );
    v_fst_2500_ = leanh::lean_ctor_get(v___x_2499_, 0);
    leanh::lean_inc(v_fst_2500_);
    leanh::lean_dec(v___x_2499_);
    if leanh::lean_obj_tag(v_fst_2500_) == 0 {
        let mut v___x_2501_: u8 = 0;
        v___x_2501_ = 1;
        return v___x_2501_;
    } else {
        let mut v_val_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2503_: u8 = 0;
        v_val_2502_ = leanh::lean_ctor_get(v_fst_2500_, 0);
        leanh::lean_inc(v_val_2502_);
        leanh::lean_dec_ref_known(v_fst_2500_, 1);
        v___x_2503_ = (leanh::lean_unbox(v_val_2502_) as u8);
        leanh::lean_dec(v_val_2502_);
        return v___x_2503_;
    }
}
pub unsafe fn l_Std_HashSet_all___redArg___boxed(
    mut v_m_2504_: *mut leanh::LeanObject,
    mut v_p_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2506_: u8 = 0;
    let mut v_r_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2506_ = l_Std_HashSet_all___redArg(v_m_2504_, v_p_2505_);
    v_r_2507_ = leanh::lean_box((v_res_2506_) as usize);
    return v_r_2507_;
}
pub unsafe fn l_Std_HashSet_all(
    mut v_00_u03b1_2508_: *mut leanh::LeanObject,
    mut v_x_2509_: *mut leanh::LeanObject,
    mut v_x_2510_: *mut leanh::LeanObject,
    mut v_m_2511_: *mut leanh::LeanObject,
    mut v_p_2512_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2519_: usize = 0;
    let mut v___x_2520_: usize = 0;
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2514_ = leanh::lean_ctor_get(v_m_2511_, 1);
    leanh::lean_inc_ref(v_buckets_2514_);
    leanh::lean_dec_ref(v_m_2511_);
    v___x_2515_ = leanh::lean_box(0);
    v___x_2516_ = l_Std_HashSet_all___redArg___closed__0;
    v___f_2517_ = leanh::lean_alloc_closure(
        l_Std_HashSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2517_, 0, v_p_2512_);
    leanh::lean_closure_set(v___f_2517_, 1, v___x_2515_);
    leanh::lean_closure_set(v___f_2517_, 2, v___x_2516_);
    v___f_2518_ = leanh::lean_alloc_closure(
        l_Std_HashSet_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2518_, 0, v___x_2513_);
    leanh::lean_closure_set(v___f_2518_, 1, v___f_2517_);
    v_sz_2519_ = lean_array_size(v_buckets_2514_);
    v___x_2520_ = 0usize;
    v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2513_,
        v_buckets_2514_,
        v___f_2518_,
        v_sz_2519_,
        v___x_2520_,
        v___x_2516_,
    );
    v_fst_2522_ = leanh::lean_ctor_get(v___x_2521_, 0);
    leanh::lean_inc(v_fst_2522_);
    leanh::lean_dec(v___x_2521_);
    if leanh::lean_obj_tag(v_fst_2522_) == 0 {
        let mut v___x_2523_: u8 = 0;
        v___x_2523_ = 1;
        return v___x_2523_;
    } else {
        let mut v_val_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2525_: u8 = 0;
        v_val_2524_ = leanh::lean_ctor_get(v_fst_2522_, 0);
        leanh::lean_inc(v_val_2524_);
        leanh::lean_dec_ref_known(v_fst_2522_, 1);
        v___x_2525_ = (leanh::lean_unbox(v_val_2524_) as u8);
        leanh::lean_dec(v_val_2524_);
        return v___x_2525_;
    }
}
pub unsafe fn l_Std_HashSet_all___boxed(
    mut v_00_u03b1_2526_: *mut leanh::LeanObject,
    mut v_x_2527_: *mut leanh::LeanObject,
    mut v_x_2528_: *mut leanh::LeanObject,
    mut v_m_2529_: *mut leanh::LeanObject,
    mut v_p_2530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2531_: u8 = 0;
    let mut v_r_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2531_ = l_Std_HashSet_all(v_00_u03b1_2526_, v_x_2527_, v_x_2528_, v_m_2529_, v_p_2530_);
    leanh::lean_dec_ref(v_x_2528_);
    leanh::lean_dec_ref(v_x_2527_);
    v_r_2532_ = leanh::lean_box((v_res_2531_) as usize);
    return v_r_2532_;
}
pub unsafe fn l_Std_HashSet_any___redArg___lam__0(
    mut v_p_2533_: *mut leanh::LeanObject,
    mut v___x_2534_: *mut leanh::LeanObject,
    mut v___x_2535_: *mut leanh::LeanObject,
    mut v_a_2536_: *mut leanh::LeanObject,
    mut v_b_2537_: *mut leanh::LeanObject,
    mut v_acc_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    v___x_2539_ = leanh::lean_apply_1(v_p_2533_, v_a_2536_);
    v___x_2540_ = (leanh::lean_unbox(v___x_2539_) as u8);
    if v___x_2540_ == 0 {
        let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2541_, 0, v___x_2534_);
        return v___x_2541_;
    } else {
        let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2534_);
        v___x_2542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2542_, 0, v___x_2539_);
        v___x_2543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2543_, 0, v___x_2542_);
        leanh::lean_ctor_set(v___x_2543_, 1, v___x_2535_);
        v___x_2544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2544_, 0, v___x_2543_);
        return v___x_2544_;
    }
}
pub unsafe fn l_Std_HashSet_any___redArg___lam__0___boxed(
    mut v_p_2545_: *mut leanh::LeanObject,
    mut v___x_2546_: *mut leanh::LeanObject,
    mut v___x_2547_: *mut leanh::LeanObject,
    mut v_a_2548_: *mut leanh::LeanObject,
    mut v_b_2549_: *mut leanh::LeanObject,
    mut v_acc_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_Std_HashSet_any___redArg___lam__0(
        v_p_2545_,
        v___x_2546_,
        v___x_2547_,
        v_a_2548_,
        v_b_2549_,
        v_acc_2550_,
    );
    leanh::lean_dec_ref(v_acc_2550_);
    return v_res_2551_;
}
pub unsafe fn l_Std_HashSet_any___redArg(
    mut v_m_2552_: *mut leanh::LeanObject,
    mut v_p_2553_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2560_: usize = 0;
    let mut v___x_2561_: usize = 0;
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2555_ = leanh::lean_ctor_get(v_m_2552_, 1);
    leanh::lean_inc_ref(v_buckets_2555_);
    leanh::lean_dec_ref(v_m_2552_);
    v___x_2556_ = leanh::lean_box(0);
    v___x_2557_ = l_Std_HashSet_all___redArg___closed__0;
    v___f_2558_ = leanh::lean_alloc_closure(
        l_Std_HashSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2558_, 0, v_p_2553_);
    leanh::lean_closure_set(v___f_2558_, 1, v___x_2557_);
    leanh::lean_closure_set(v___f_2558_, 2, v___x_2556_);
    v___f_2559_ = leanh::lean_alloc_closure(
        l_Std_HashSet_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2559_, 0, v___x_2554_);
    leanh::lean_closure_set(v___f_2559_, 1, v___f_2558_);
    v_sz_2560_ = lean_array_size(v_buckets_2555_);
    v___x_2561_ = 0usize;
    v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2554_,
        v_buckets_2555_,
        v___f_2559_,
        v_sz_2560_,
        v___x_2561_,
        v___x_2557_,
    );
    v_fst_2563_ = leanh::lean_ctor_get(v___x_2562_, 0);
    leanh::lean_inc(v_fst_2563_);
    leanh::lean_dec(v___x_2562_);
    if leanh::lean_obj_tag(v_fst_2563_) == 0 {
        let mut v___x_2564_: u8 = 0;
        v___x_2564_ = 0;
        return v___x_2564_;
    } else {
        let mut v_val_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2566_: u8 = 0;
        v_val_2565_ = leanh::lean_ctor_get(v_fst_2563_, 0);
        leanh::lean_inc(v_val_2565_);
        leanh::lean_dec_ref_known(v_fst_2563_, 1);
        v___x_2566_ = (leanh::lean_unbox(v_val_2565_) as u8);
        leanh::lean_dec(v_val_2565_);
        return v___x_2566_;
    }
}
pub unsafe fn l_Std_HashSet_any___redArg___boxed(
    mut v_m_2567_: *mut leanh::LeanObject,
    mut v_p_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2569_: u8 = 0;
    let mut v_r_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Std_HashSet_any___redArg(v_m_2567_, v_p_2568_);
    v_r_2570_ = leanh::lean_box((v_res_2569_) as usize);
    return v_r_2570_;
}
pub unsafe fn l_Std_HashSet_any(
    mut v_00_u03b1_2571_: *mut leanh::LeanObject,
    mut v_x_2572_: *mut leanh::LeanObject,
    mut v_x_2573_: *mut leanh::LeanObject,
    mut v_m_2574_: *mut leanh::LeanObject,
    mut v_p_2575_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2582_: usize = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Std_HashSet_toList___redArg___closed__9;
    v_buckets_2577_ = leanh::lean_ctor_get(v_m_2574_, 1);
    leanh::lean_inc_ref(v_buckets_2577_);
    leanh::lean_dec_ref(v_m_2574_);
    v___x_2578_ = leanh::lean_box(0);
    v___x_2579_ = l_Std_HashSet_all___redArg___closed__0;
    v___f_2580_ = leanh::lean_alloc_closure(
        l_Std_HashSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2580_, 0, v_p_2575_);
    leanh::lean_closure_set(v___f_2580_, 1, v___x_2579_);
    leanh::lean_closure_set(v___f_2580_, 2, v___x_2578_);
    v___f_2581_ = leanh::lean_alloc_closure(
        l_Std_HashSet_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2581_, 0, v___x_2576_);
    leanh::lean_closure_set(v___f_2581_, 1, v___f_2580_);
    v_sz_2582_ = lean_array_size(v_buckets_2577_);
    v___x_2583_ = 0usize;
    v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2576_,
        v_buckets_2577_,
        v___f_2581_,
        v_sz_2582_,
        v___x_2583_,
        v___x_2579_,
    );
    v_fst_2585_ = leanh::lean_ctor_get(v___x_2584_, 0);
    leanh::lean_inc(v_fst_2585_);
    leanh::lean_dec(v___x_2584_);
    if leanh::lean_obj_tag(v_fst_2585_) == 0 {
        let mut v___x_2586_: u8 = 0;
        v___x_2586_ = 0;
        return v___x_2586_;
    } else {
        let mut v_val_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2588_: u8 = 0;
        v_val_2587_ = leanh::lean_ctor_get(v_fst_2585_, 0);
        leanh::lean_inc(v_val_2587_);
        leanh::lean_dec_ref_known(v_fst_2585_, 1);
        v___x_2588_ = (leanh::lean_unbox(v_val_2587_) as u8);
        leanh::lean_dec(v_val_2587_);
        return v___x_2588_;
    }
}
pub unsafe fn l_Std_HashSet_any___boxed(
    mut v_00_u03b1_2589_: *mut leanh::LeanObject,
    mut v_x_2590_: *mut leanh::LeanObject,
    mut v_x_2591_: *mut leanh::LeanObject,
    mut v_m_2592_: *mut leanh::LeanObject,
    mut v_p_2593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2594_: u8 = 0;
    let mut v_r_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2594_ = l_Std_HashSet_any(v_00_u03b1_2589_, v_x_2590_, v_x_2591_, v_m_2592_, v_p_2593_);
    leanh::lean_dec_ref(v_x_2591_);
    leanh::lean_dec_ref(v_x_2590_);
    v_r_2595_ = leanh::lean_box((v_res_2594_) as usize);
    return v_r_2595_;
}
pub unsafe fn l_Std_HashSet_union___redArg___lam__0(
    mut v_inst_2596_: *mut leanh::LeanObject,
    mut v_inst_2597_: *mut leanh::LeanObject,
    mut v_a_2598_: *mut leanh::LeanObject,
    mut v_b_2599_: *mut leanh::LeanObject,
    mut v_acc_2600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_2601_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_2596_,
        v_inst_2597_,
        v_acc_2600_,
        v_a_2598_,
        v_b_2599_,
    );
    v___x_2602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2602_, 0, v_r_2601_);
    return v___x_2602_;
}
pub unsafe fn l_Std_HashSet_union___redArg___lam__1(
    mut v___x_2603_: *mut leanh::LeanObject,
    mut v___f_2604_: *mut leanh::LeanObject,
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_x_2606_: *mut leanh::LeanObject,
    mut v___y_2607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2608_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_2603_, v___f_2604_, v_a_2605_, v___y_2607_);
    return v___x_2608_;
}
pub unsafe fn l_Std_HashSet_union___redArg(
    mut v_inst_2611_: *mut leanh::LeanObject,
    mut v_inst_2612_: *mut leanh::LeanObject,
    mut v_m_u2081_2613_: *mut leanh::LeanObject,
    mut v_m_u2082_2614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: u8 = 0;
    v_size_2615_ = leanh::lean_ctor_get(v_m_u2081_2613_, 0);
    v_buckets_2616_ = leanh::lean_ctor_get(v_m_u2081_2613_, 1);
    v_size_2617_ = leanh::lean_ctor_get(v_m_u2082_2614_, 0);
    v___x_2618_ = lean_nat_dec_le(v_size_2615_, v_size_2617_);
    if v___x_2618_ == 0 {
        let mut v___f_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2619_ = l_Std_HashSet_union___redArg___closed__0;
        v___x_2620_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_2619_,
            v_inst_2611_,
            v_inst_2612_,
            v_m_u2081_2613_,
            v_m_u2082_2614_,
        );
        return v___x_2620_;
    } else {
        let mut v___f_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2624_: usize = 0;
        let mut v___x_2625_: usize = 0;
        let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_2616_);
        leanh::lean_dec_ref(v_m_u2081_2613_);
        v___f_2621_ = leanh::lean_alloc_closure(
            l_Std_HashSet_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_2621_, 0, v_inst_2611_);
        leanh::lean_closure_set(v___f_2621_, 1, v_inst_2612_);
        v___x_2622_ = l_Std_HashSet_toList___redArg___closed__9;
        v___f_2623_ = leanh::lean_alloc_closure(
            l_Std_HashSet_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_2623_, 0, v___x_2622_);
        leanh::lean_closure_set(v___f_2623_, 1, v___f_2621_);
        v_sz_2624_ = lean_array_size(v_buckets_2616_);
        v___x_2625_ = 0usize;
        v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2622_,
            v_buckets_2616_,
            v___f_2623_,
            v_sz_2624_,
            v___x_2625_,
            v_m_u2082_2614_,
        );
        return v___x_2626_;
    }
}
pub unsafe fn l_Std_HashSet_union(
    mut v_00_u03b1_2627_: *mut leanh::LeanObject,
    mut v_inst_2628_: *mut leanh::LeanObject,
    mut v_inst_2629_: *mut leanh::LeanObject,
    mut v_m_u2081_2630_: *mut leanh::LeanObject,
    mut v_m_u2082_2631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    v_size_2632_ = leanh::lean_ctor_get(v_m_u2081_2630_, 0);
    v_buckets_2633_ = leanh::lean_ctor_get(v_m_u2081_2630_, 1);
    v_size_2634_ = leanh::lean_ctor_get(v_m_u2082_2631_, 0);
    v___x_2635_ = lean_nat_dec_le(v_size_2632_, v_size_2634_);
    if v___x_2635_ == 0 {
        let mut v___f_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2636_ = l_Std_HashSet_union___redArg___closed__0;
        v___x_2637_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_2636_,
            v_inst_2628_,
            v_inst_2629_,
            v_m_u2081_2630_,
            v_m_u2082_2631_,
        );
        return v___x_2637_;
    } else {
        let mut v___f_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2641_: usize = 0;
        let mut v___x_2642_: usize = 0;
        let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_2633_);
        leanh::lean_dec_ref(v_m_u2081_2630_);
        v___f_2638_ = leanh::lean_alloc_closure(
            l_Std_HashSet_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_2638_, 0, v_inst_2628_);
        leanh::lean_closure_set(v___f_2638_, 1, v_inst_2629_);
        v___x_2639_ = l_Std_HashSet_toList___redArg___closed__9;
        v___f_2640_ = leanh::lean_alloc_closure(
            l_Std_HashSet_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_2640_, 0, v___x_2639_);
        leanh::lean_closure_set(v___f_2640_, 1, v___f_2638_);
        v_sz_2641_ = lean_array_size(v_buckets_2633_);
        v___x_2642_ = 0usize;
        v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2639_,
            v_buckets_2633_,
            v___f_2640_,
            v_sz_2641_,
            v___x_2642_,
            v_m_u2082_2631_,
        );
        return v___x_2643_;
    }
}
pub unsafe fn l_Std_HashSet_instUnion___redArg(
    mut v_inst_2644_: *mut leanh::LeanObject,
    mut v_inst_2645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2646_ =
        leanh::lean_alloc_closure(l_Std_HashSet_union as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2646_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2646_, 1, v_inst_2644_);
    leanh::lean_closure_set(v___x_2646_, 2, v_inst_2645_);
    return v___x_2646_;
}
pub unsafe fn l_Std_HashSet_instUnion(
    mut v_00_u03b1_2647_: *mut leanh::LeanObject,
    mut v_inst_2648_: *mut leanh::LeanObject,
    mut v_inst_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ =
        leanh::lean_alloc_closure(l_Std_HashSet_union as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2650_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2650_, 1, v_inst_2648_);
    leanh::lean_closure_set(v___x_2650_, 2, v_inst_2649_);
    return v___x_2650_;
}
pub unsafe fn l_Std_HashSet_inter___redArg(
    mut v_inst_2651_: *mut leanh::LeanObject,
    mut v_inst_2652_: *mut leanh::LeanObject,
    mut v_m_u2081_2653_: *mut leanh::LeanObject,
    mut v_m_u2082_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_inst_2651_,
        v_inst_2652_,
        v_m_u2081_2653_,
        v_m_u2082_2654_,
    );
    return v___x_2655_;
}
pub unsafe fn l_Std_HashSet_inter(
    mut v_00_u03b1_2656_: *mut leanh::LeanObject,
    mut v_inst_2657_: *mut leanh::LeanObject,
    mut v_inst_2658_: *mut leanh::LeanObject,
    mut v_m_u2081_2659_: *mut leanh::LeanObject,
    mut v_m_u2082_2660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_inst_2657_,
        v_inst_2658_,
        v_m_u2081_2659_,
        v_m_u2082_2660_,
    );
    return v___x_2661_;
}
pub unsafe fn l_Std_HashSet_instInter___redArg(
    mut v_inst_2662_: *mut leanh::LeanObject,
    mut v_inst_2663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ =
        leanh::lean_alloc_closure(l_Std_HashSet_inter as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2664_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2664_, 1, v_inst_2662_);
    leanh::lean_closure_set(v___x_2664_, 2, v_inst_2663_);
    return v___x_2664_;
}
pub unsafe fn l_Std_HashSet_instInter(
    mut v_00_u03b1_2665_: *mut leanh::LeanObject,
    mut v_inst_2666_: *mut leanh::LeanObject,
    mut v_inst_2667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ =
        leanh::lean_alloc_closure(l_Std_HashSet_inter as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2668_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2668_, 1, v_inst_2666_);
    leanh::lean_closure_set(v___x_2668_, 2, v_inst_2667_);
    return v___x_2668_;
}
pub unsafe fn _init_l_Std_HashSet_beq___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_2670_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2670_, 0, v___x_2669_);
    return v___f_2670_;
}
pub unsafe fn l_Std_HashSet_beq___redArg(
    mut v_x_2671_: *mut leanh::LeanObject,
    mut v_inst_2672_: *mut leanh::LeanObject,
    mut v_m_u2081_2673_: *mut leanh::LeanObject,
    mut v_m_u2082_2674_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    v___f_2675_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_beq___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_beq___redArg___closed__0_once),
        _init_l_Std_HashSet_beq___redArg___closed__0,
    );
    v___x_2676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_2672_,
        v_x_2671_,
        v___f_2675_,
        v_m_u2081_2673_,
        v_m_u2082_2674_,
    );
    return v___x_2676_;
}
pub unsafe fn l_Std_HashSet_beq___redArg___boxed(
    mut v_x_2677_: *mut leanh::LeanObject,
    mut v_inst_2678_: *mut leanh::LeanObject,
    mut v_m_u2081_2679_: *mut leanh::LeanObject,
    mut v_m_u2082_2680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2681_: u8 = 0;
    let mut v_r_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2681_ =
        l_Std_HashSet_beq___redArg(v_x_2677_, v_inst_2678_, v_m_u2081_2679_, v_m_u2082_2680_);
    v_r_2682_ = leanh::lean_box((v_res_2681_) as usize);
    return v_r_2682_;
}
pub unsafe fn l_Std_HashSet_beq(
    mut v_00_u03b1_2683_: *mut leanh::LeanObject,
    mut v_x_2684_: *mut leanh::LeanObject,
    mut v_inst_2685_: *mut leanh::LeanObject,
    mut v_m_u2081_2686_: *mut leanh::LeanObject,
    mut v_m_u2082_2687_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2688_: u8 = 0;
    v___x_2688_ =
        l_Std_HashSet_beq___redArg(v_x_2684_, v_inst_2685_, v_m_u2081_2686_, v_m_u2082_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Std_HashSet_beq___boxed(
    mut v_00_u03b1_2689_: *mut leanh::LeanObject,
    mut v_x_2690_: *mut leanh::LeanObject,
    mut v_inst_2691_: *mut leanh::LeanObject,
    mut v_m_u2081_2692_: *mut leanh::LeanObject,
    mut v_m_u2082_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2694_: u8 = 0;
    let mut v_r_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Std_HashSet_beq(
        v_00_u03b1_2689_,
        v_x_2690_,
        v_inst_2691_,
        v_m_u2081_2692_,
        v_m_u2082_2693_,
    );
    v_r_2695_ = leanh::lean_box((v_res_2694_) as usize);
    return v_r_2695_;
}
pub unsafe fn l_Std_HashSet_instBEq___redArg(
    mut v_x_2696_: *mut leanh::LeanObject,
    mut v_inst_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2698_ =
        leanh::lean_alloc_closure(l_Std_HashSet_beq___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2698_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2698_, 1, v_x_2696_);
    leanh::lean_closure_set(v___x_2698_, 2, v_inst_2697_);
    return v___x_2698_;
}
pub unsafe fn l_Std_HashSet_instBEq(
    mut v_00_u03b1_2699_: *mut leanh::LeanObject,
    mut v_x_2700_: *mut leanh::LeanObject,
    mut v_inst_2701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ =
        leanh::lean_alloc_closure(l_Std_HashSet_beq___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2702_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2702_, 1, v_x_2700_);
    leanh::lean_closure_set(v___x_2702_, 2, v_inst_2701_);
    return v___x_2702_;
}
pub unsafe fn l_Std_HashSet_diff___redArg___lam__0(
    mut v_inst_2703_: *mut leanh::LeanObject,
    mut v_inst_2704_: *mut leanh::LeanObject,
    mut v_m_u2082_2705_: *mut leanh::LeanObject,
    mut v___x_2706_: u8,
    mut v_k_2707_: *mut leanh::LeanObject,
    mut v_x_2708_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2709_: u8 = 0;
    v___x_2709_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_2703_,
        v_inst_2704_,
        v_m_u2082_2705_,
        v_k_2707_,
    );
    if v___x_2709_ == 0 {
        return v___x_2706_;
    } else {
        let mut v___x_2710_: u8 = 0;
        v___x_2710_ = 0;
        return v___x_2710_;
    }
}
pub unsafe fn l_Std_HashSet_diff___redArg___lam__0___boxed(
    mut v_inst_2711_: *mut leanh::LeanObject,
    mut v_inst_2712_: *mut leanh::LeanObject,
    mut v_m_u2082_2713_: *mut leanh::LeanObject,
    mut v___x_2714_: *mut leanh::LeanObject,
    mut v_k_2715_: *mut leanh::LeanObject,
    mut v_x_2716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_83__boxed_2717_: u8 = 0;
    let mut v_res_2718_: u8 = 0;
    let mut v_r_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_83__boxed_2717_ = (leanh::lean_unbox(v___x_2714_) as u8);
    v_res_2718_ = l_Std_HashSet_diff___redArg___lam__0(
        v_inst_2711_,
        v_inst_2712_,
        v_m_u2082_2713_,
        v___x_83__boxed_2717_,
        v_k_2715_,
        v_x_2716_,
    );
    leanh::lean_dec_ref(v_m_u2082_2713_);
    v_r_2719_ = leanh::lean_box((v_res_2718_) as usize);
    return v_r_2719_;
}
pub unsafe fn l_Std_HashSet_diff___redArg(
    mut v_inst_2720_: *mut leanh::LeanObject,
    mut v_inst_2721_: *mut leanh::LeanObject,
    mut v_m_u2081_2722_: *mut leanh::LeanObject,
    mut v_m_u2082_2723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: u8 = 0;
    v_size_2724_ = leanh::lean_ctor_get(v_m_u2081_2722_, 0);
    v_size_2725_ = leanh::lean_ctor_get(v_m_u2082_2723_, 0);
    v___x_2726_ = lean_nat_dec_le(v_size_2724_, v_size_2725_);
    if v___x_2726_ == 0 {
        let mut v___f_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2727_ = l_Std_HashSet_union___redArg___closed__0;
        v___x_2728_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_2727_,
            v_inst_2720_,
            v_inst_2721_,
            v_m_u2081_2722_,
            v_m_u2082_2723_,
        );
        return v___x_2728_;
    } else {
        let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2729_ = leanh::lean_box((v___x_2726_) as usize);
        v___f_2730_ = leanh::lean_alloc_closure(
            l_Std_HashSet_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_2730_, 0, v_inst_2720_);
        leanh::lean_closure_set(v___f_2730_, 1, v_inst_2721_);
        leanh::lean_closure_set(v___f_2730_, 2, v_m_u2082_2723_);
        leanh::lean_closure_set(v___f_2730_, 3, v___x_2729_);
        v___x_2731_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2730_, v_m_u2081_2722_);
        return v___x_2731_;
    }
}
pub unsafe fn l_Std_HashSet_diff(
    mut v_00_u03b1_2732_: *mut leanh::LeanObject,
    mut v_inst_2733_: *mut leanh::LeanObject,
    mut v_inst_2734_: *mut leanh::LeanObject,
    mut v_m_u2081_2735_: *mut leanh::LeanObject,
    mut v_m_u2082_2736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    v_size_2737_ = leanh::lean_ctor_get(v_m_u2081_2735_, 0);
    v_size_2738_ = leanh::lean_ctor_get(v_m_u2082_2736_, 0);
    v___x_2739_ = lean_nat_dec_le(v_size_2737_, v_size_2738_);
    if v___x_2739_ == 0 {
        let mut v___f_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2740_ = l_Std_HashSet_union___redArg___closed__0;
        v___x_2741_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_2740_,
            v_inst_2733_,
            v_inst_2734_,
            v_m_u2081_2735_,
            v_m_u2082_2736_,
        );
        return v___x_2741_;
    } else {
        let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2742_ = leanh::lean_box((v___x_2739_) as usize);
        v___f_2743_ = leanh::lean_alloc_closure(
            l_Std_HashSet_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_2743_, 0, v_inst_2733_);
        leanh::lean_closure_set(v___f_2743_, 1, v_inst_2734_);
        leanh::lean_closure_set(v___f_2743_, 2, v_m_u2082_2736_);
        leanh::lean_closure_set(v___f_2743_, 3, v___x_2742_);
        v___x_2744_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2743_, v_m_u2081_2735_);
        return v___x_2744_;
    }
}
pub unsafe fn l_Std_HashSet_instSDiff___redArg(
    mut v_inst_2745_: *mut leanh::LeanObject,
    mut v_inst_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2747_ =
        leanh::lean_alloc_closure(l_Std_HashSet_diff as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2747_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2747_, 1, v_inst_2745_);
    leanh::lean_closure_set(v___x_2747_, 2, v_inst_2746_);
    return v___x_2747_;
}
pub unsafe fn l_Std_HashSet_instSDiff(
    mut v_00_u03b1_2748_: *mut leanh::LeanObject,
    mut v_inst_2749_: *mut leanh::LeanObject,
    mut v_inst_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ =
        leanh::lean_alloc_closure(l_Std_HashSet_diff as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2751_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2751_, 1, v_inst_2749_);
    leanh::lean_closure_set(v___x_2751_, 2, v_inst_2750_);
    return v___x_2751_;
}
pub unsafe fn l_Std_HashSet_partition___redArg___lam__0(
    mut v_f_2752_: *mut leanh::LeanObject,
    mut v_x_2753_: *mut leanh::LeanObject,
    mut v_x_2754_: *mut leanh::LeanObject,
    mut v_x1_2755_: *mut leanh::LeanObject,
    mut v_x2_2756_: *mut leanh::LeanObject,
    mut v_x3_2757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2762_: u8 = 0;
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2758_ = leanh::lean_ctor_get(v_x1_2755_, 0);
                v_snd_2759_ = leanh::lean_ctor_get(v_x1_2755_, 1);
                v_isSharedCheck_2773_ = (!leanh::lean_is_exclusive(v_x1_2755_)) as u8;
                if v_isSharedCheck_2773_ == 0 {
                    v___x_2761_ = v_x1_2755_;
                    v_isShared_2762_ = v_isSharedCheck_2773_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2759_);
                    leanh::lean_inc(v_fst_2758_);
                    leanh::lean_dec(v_x1_2755_);
                    v___x_2761_ = leanh::lean_box(0);
                    v_isShared_2762_ = v_isSharedCheck_2773_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_x2_2756_);
                v___x_2763_ = leanh::lean_apply_1(v_f_2752_, v_x2_2756_);
                v___x_2764_ = (leanh::lean_unbox(v___x_2763_) as u8);
                if v___x_2764_ == 0 {
                    v___x_2765_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_x_2753_,
                        v_x_2754_,
                        v_snd_2759_,
                        v_x2_2756_,
                        v_x3_2757_,
                    );
                    if v_isShared_2762_ == 0 {
                        leanh::lean_ctor_set(v___x_2761_, 1, v___x_2765_);
                        v___x_2767_ = v___x_2761_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_fst_2758_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2765_);
                        v___x_2767_ = v_reuseFailAlloc_2768_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2769_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_x_2753_,
                        v_x_2754_,
                        v_fst_2758_,
                        v_x2_2756_,
                        v_x3_2757_,
                    );
                    if v_isShared_2762_ == 0 {
                        leanh::lean_ctor_set(v___x_2761_, 0, v___x_2769_);
                        v___x_2771_ = v___x_2761_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2772_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_snd_2759_);
                        v___x_2771_ = v_reuseFailAlloc_2772_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2767_;
            }
            3 => {
                return v___x_2771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_partition___redArg___lam__1(
    mut v___x_2774_: *mut leanh::LeanObject,
    mut v___f_2775_: *mut leanh::LeanObject,
    mut v_acc_2776_: *mut leanh::LeanObject,
    mut v_l_2777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2774_,
        v___f_2775_,
        v_acc_2776_,
        v_l_2777_,
    );
    return v___x_2778_;
}
pub unsafe fn _init_l_Std_HashSet_partition___redArg___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2779_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    v___x_2780_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2780_, 0, v___x_2779_);
    leanh::lean_ctor_set(v___x_2780_, 1, v___x_2779_);
    return v___x_2780_;
}
pub unsafe fn l_Std_HashSet_partition___redArg(
    mut v_x_2781_: *mut leanh::LeanObject,
    mut v_x_2782_: *mut leanh::LeanObject,
    mut v_f_2783_: *mut leanh::LeanObject,
    mut v_m_2784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2791_: u8 = 0;
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    let mut v___f_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: usize = 0;
    let mut v___x_2806_: usize = 0;
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: usize = 0;
    let mut v___x_2809_: usize = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2796_ = leanh::lean_unsigned_to_nat(0);
                v___x_2797_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_HashSet_partition___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Std_HashSet_partition___redArg___closed__0_once),
                    _init_l_Std_HashSet_partition___redArg___closed__0,
                );
                v___x_2798_ = l_Std_HashSet_toList___redArg___closed__9;
                v_buckets_2799_ = leanh::lean_ctor_get(v_m_2784_, 1);
                leanh::lean_inc_ref(v_buckets_2799_);
                leanh::lean_dec_ref(v_m_2784_);
                v___x_2800_ = lean_array_get_size(v_buckets_2799_);
                v___x_2801_ = lean_nat_dec_lt(v___x_2796_, v___x_2800_);
                if v___x_2801_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2799_);
                    leanh::lean_dec_ref(v_f_2783_);
                    leanh::lean_dec_ref(v_x_2782_);
                    leanh::lean_dec_ref(v_x_2781_);
                    return v___x_2797_;
                } else {
                    v___f_2802_ = leanh::lean_alloc_closure(
                        l_Std_HashSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2802_, 0, v_f_2783_);
                    leanh::lean_closure_set(v___f_2802_, 1, v_x_2781_);
                    leanh::lean_closure_set(v___f_2802_, 2, v_x_2782_);
                    v___f_2803_ = leanh::lean_alloc_closure(
                        l_Std_HashSet_partition___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2803_, 0, v___x_2798_);
                    leanh::lean_closure_set(v___f_2803_, 1, v___f_2802_);
                    v___x_2804_ = lean_nat_dec_le(v___x_2800_, v___x_2800_);
                    if v___x_2804_ == 0 {
                        if v___x_2801_ == 0 {
                            leanh::lean_dec_ref(v___f_2803_);
                            leanh::lean_dec_ref(v_buckets_2799_);
                            return v___x_2797_;
                        } else {
                            v___x_2805_ = 0usize;
                            v___x_2806_ = lean_usize_of_nat(v___x_2800_);
                            v___x_2807_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2798_,
                                    v___f_2803_,
                                    v_buckets_2799_,
                                    v___x_2805_,
                                    v___x_2806_,
                                    v___x_2797_,
                                );
                            v___y_2786_ = v___x_2807_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2808_ = 0usize;
                        v___x_2809_ = lean_usize_of_nat(v___x_2800_);
                        v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2798_,
                            v___f_2803_,
                            v_buckets_2799_,
                            v___x_2808_,
                            v___x_2809_,
                            v___x_2797_,
                        );
                        v___y_2786_ = v___x_2810_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2787_ = leanh::lean_ctor_get(v___y_2786_, 0);
                v_snd_2788_ = leanh::lean_ctor_get(v___y_2786_, 1);
                v_isSharedCheck_2795_ = (!leanh::lean_is_exclusive(v___y_2786_)) as u8;
                if v_isSharedCheck_2795_ == 0 {
                    v___x_2790_ = v___y_2786_;
                    v_isShared_2791_ = v_isSharedCheck_2795_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2788_);
                    leanh::lean_inc(v_fst_2787_);
                    leanh::lean_dec(v___y_2786_);
                    v___x_2790_ = leanh::lean_box(0);
                    v_isShared_2791_ = v_isSharedCheck_2795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2791_ == 0 {
                    v___x_2793_ = v___x_2790_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_fst_2787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_snd_2788_);
                    v___x_2793_ = v_reuseFailAlloc_2794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_partition(
    mut v_00_u03b1_2811_: *mut leanh::LeanObject,
    mut v_x_2812_: *mut leanh::LeanObject,
    mut v_x_2813_: *mut leanh::LeanObject,
    mut v_f_2814_: *mut leanh::LeanObject,
    mut v_m_2815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v___f_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v___x_2836_: usize = 0;
    let mut v___x_2837_: usize = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: usize = 0;
    let mut v___x_2840_: usize = 0;
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2827_ = leanh::lean_unsigned_to_nat(0);
                v___x_2828_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_HashSet_partition___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Std_HashSet_partition___redArg___closed__0_once),
                    _init_l_Std_HashSet_partition___redArg___closed__0,
                );
                v___x_2829_ = l_Std_HashSet_toList___redArg___closed__9;
                v_buckets_2830_ = leanh::lean_ctor_get(v_m_2815_, 1);
                leanh::lean_inc_ref(v_buckets_2830_);
                leanh::lean_dec_ref(v_m_2815_);
                v___x_2831_ = lean_array_get_size(v_buckets_2830_);
                v___x_2832_ = lean_nat_dec_lt(v___x_2827_, v___x_2831_);
                if v___x_2832_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2830_);
                    leanh::lean_dec_ref(v_f_2814_);
                    leanh::lean_dec_ref(v_x_2813_);
                    leanh::lean_dec_ref(v_x_2812_);
                    return v___x_2828_;
                } else {
                    v___f_2833_ = leanh::lean_alloc_closure(
                        l_Std_HashSet_partition___redArg___lam__0 as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2833_, 0, v_f_2814_);
                    leanh::lean_closure_set(v___f_2833_, 1, v_x_2812_);
                    leanh::lean_closure_set(v___f_2833_, 2, v_x_2813_);
                    v___f_2834_ = leanh::lean_alloc_closure(
                        l_Std_HashSet_partition___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2834_, 0, v___x_2829_);
                    leanh::lean_closure_set(v___f_2834_, 1, v___f_2833_);
                    v___x_2835_ = lean_nat_dec_le(v___x_2831_, v___x_2831_);
                    if v___x_2835_ == 0 {
                        if v___x_2832_ == 0 {
                            leanh::lean_dec_ref(v___f_2834_);
                            leanh::lean_dec_ref(v_buckets_2830_);
                            return v___x_2828_;
                        } else {
                            v___x_2836_ = 0usize;
                            v___x_2837_ = lean_usize_of_nat(v___x_2831_);
                            v___x_2838_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2829_,
                                    v___f_2834_,
                                    v_buckets_2830_,
                                    v___x_2836_,
                                    v___x_2837_,
                                    v___x_2828_,
                                );
                            v___y_2817_ = v___x_2838_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2839_ = 0usize;
                        v___x_2840_ = lean_usize_of_nat(v___x_2831_);
                        v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2829_,
                            v___f_2834_,
                            v_buckets_2830_,
                            v___x_2839_,
                            v___x_2840_,
                            v___x_2828_,
                        );
                        v___y_2817_ = v___x_2841_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2818_ = leanh::lean_ctor_get(v___y_2817_, 0);
                v_snd_2819_ = leanh::lean_ctor_get(v___y_2817_, 1);
                v_isSharedCheck_2826_ = (!leanh::lean_is_exclusive(v___y_2817_)) as u8;
                if v_isSharedCheck_2826_ == 0 {
                    v___x_2821_ = v___y_2817_;
                    v_isShared_2822_ = v_isSharedCheck_2826_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2819_);
                    leanh::lean_inc(v_fst_2818_);
                    leanh::lean_dec(v___y_2817_);
                    v___x_2821_ = leanh::lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2822_ == 0 {
                    v___x_2824_ = v___x_2821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_fst_2818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_snd_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2825_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_ofArray___redArg(
    mut v_inst_2846_: *mut leanh::LeanObject,
    mut v_inst_2847_: *mut leanh::LeanObject,
    mut v_l_2848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2849_ = l_Std_HashSet_ofArray___redArg___closed__1;
    v___x_2850_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    v___x_2851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2849_,
        v_inst_2846_,
        v_inst_2847_,
        v___x_2850_,
        v_l_2848_,
    );
    return v___x_2851_;
}
pub unsafe fn l_Std_HashSet_ofArray(
    mut v_00_u03b1_2852_: *mut leanh::LeanObject,
    mut v_inst_2853_: *mut leanh::LeanObject,
    mut v_inst_2854_: *mut leanh::LeanObject,
    mut v_l_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2856_ = l_Std_HashSet_ofArray___redArg___closed__1;
    v___x_2857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_instEmptyCollection___closed__1,
    );
    v___x_2858_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_2856_,
        v_inst_2853_,
        v_inst_2854_,
        v___x_2857_,
        v_l_2855_,
    );
    return v___x_2858_;
}
pub unsafe fn l_Std_HashSet_Internal_numBuckets___redArg(
    mut v_m_2859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2859_);
    return v___x_2860_;
}
pub unsafe fn l_Std_HashSet_Internal_numBuckets___redArg___boxed(
    mut v_m_2861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_Std_HashSet_Internal_numBuckets___redArg(v_m_2861_);
    leanh::lean_dec_ref(v_m_2861_);
    return v_res_2862_;
}
pub unsafe fn l_Std_HashSet_Internal_numBuckets(
    mut v_00_u03b1_2863_: *mut leanh::LeanObject,
    mut v_x_2864_: *mut leanh::LeanObject,
    mut v_x_2865_: *mut leanh::LeanObject,
    mut v_m_2866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2866_);
    return v___x_2867_;
}
pub unsafe fn l_Std_HashSet_Internal_numBuckets___boxed(
    mut v_00_u03b1_2868_: *mut leanh::LeanObject,
    mut v_x_2869_: *mut leanh::LeanObject,
    mut v_x_2870_: *mut leanh::LeanObject,
    mut v_m_2871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2872_ =
        l_Std_HashSet_Internal_numBuckets(v_00_u03b1_2868_, v_x_2869_, v_x_2870_, v_m_2871_);
    leanh::lean_dec_ref(v_m_2871_);
    leanh::lean_dec_ref(v_x_2870_);
    leanh::lean_dec_ref(v_x_2869_);
    return v_res_2872_;
}
pub unsafe fn l_Std_HashSet_instRepr___redArg___lam__2(
    mut v_inst_2876_: *mut leanh::LeanObject,
    mut v___f_2877_: *mut leanh::LeanObject,
    mut v_m_2878_: *mut leanh::LeanObject,
    mut v_prec_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: u8 = 0;
    let mut v___f_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: usize = 0;
    let mut v___x_2899_: usize = 0;
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v_unused_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2880_ = l_Std_HashSet_toList___redArg___closed__9;
                v_buckets_2881_ = leanh::lean_ctor_get(v_m_2878_, 1);
                v_isSharedCheck_2901_ = (!leanh::lean_is_exclusive(v_m_2878_)) as u8;
                if v_isSharedCheck_2901_ == 0 {
                    v_unused_2902_ = leanh::lean_ctor_get(v_m_2878_, 0);
                    leanh::lean_dec(v_unused_2902_);
                    v___x_2883_ = v_m_2878_;
                    v_isShared_2884_ = v_isSharedCheck_2901_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2881_);
                    leanh::lean_dec(v_m_2878_);
                    v___x_2883_ = leanh::lean_box(0);
                    v_isShared_2884_ = v_isSharedCheck_2901_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2885_ = l_Std_HashSet_instRepr___redArg___lam__2___closed__1;
                v___x_2893_ = leanh::lean_box(0);
                v___x_2894_ = lean_array_get_size(v_buckets_2881_);
                v___x_2895_ = leanh::lean_unsigned_to_nat(0);
                v___x_2896_ = lean_nat_dec_lt(v___x_2895_, v___x_2894_);
                if v___x_2896_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2881_);
                    leanh::lean_dec_ref(v___f_2877_);
                    v___y_2887_ = v___x_2893_;
                    state = 2;
                    continue;
                } else {
                    v___f_2897_ = leanh::lean_alloc_closure(
                        l_Std_HashSet_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2897_, 0, v___x_2880_);
                    leanh::lean_closure_set(v___f_2897_, 1, v___f_2877_);
                    v___x_2898_ = lean_usize_of_nat(v___x_2894_);
                    v___x_2899_ = 0usize;
                    v___x_2900_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2880_,
                        v___f_2897_,
                        v_buckets_2881_,
                        v___x_2898_,
                        v___x_2899_,
                        v___x_2893_,
                    );
                    v___y_2887_ = v___x_2900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2888_ = l_List_repr___redArg(v_inst_2876_, v___y_2887_);
                if v_isShared_2884_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2883_, 5);
                    leanh::lean_ctor_set(v___x_2883_, 1, v___x_2888_);
                    leanh::lean_ctor_set(v___x_2883_, 0, v___x_2885_);
                    v___x_2890_ = v___x_2883_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2888_);
                    v___x_2890_ = v_reuseFailAlloc_2892_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2891_ = l_Repr_addAppParen(v___x_2890_, v_prec_2879_);
                return v___x_2891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_instRepr___redArg___lam__2___boxed(
    mut v_inst_2903_: *mut leanh::LeanObject,
    mut v___f_2904_: *mut leanh::LeanObject,
    mut v_m_2905_: *mut leanh::LeanObject,
    mut v_prec_2906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2907_ = l_Std_HashSet_instRepr___redArg___lam__2(
        v_inst_2903_,
        v___f_2904_,
        v_m_2905_,
        v_prec_2906_,
    );
    leanh::lean_dec(v_prec_2906_);
    return v_res_2907_;
}
pub unsafe fn l_Std_HashSet_instRepr___redArg(
    mut v_inst_2908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2909_ = l_Std_HashSet_toList___redArg___closed__10;
    v___f_2910_ = leanh::lean_alloc_closure(
        l_Std_HashSet_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2910_, 0, v_inst_2908_);
    leanh::lean_closure_set(v___f_2910_, 1, v___f_2909_);
    return v___f_2910_;
}
pub unsafe fn l_Std_HashSet_instRepr(
    mut v_00_u03b1_2911_: *mut leanh::LeanObject,
    mut v_inst_2912_: *mut leanh::LeanObject,
    mut v_inst_2913_: *mut leanh::LeanObject,
    mut v_inst_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Std_HashSet_instRepr___redArg(v_inst_2914_);
    return v___x_2915_;
}
pub unsafe fn l_Std_HashSet_instRepr___boxed(
    mut v_00_u03b1_2916_: *mut leanh::LeanObject,
    mut v_inst_2917_: *mut leanh::LeanObject,
    mut v_inst_2918_: *mut leanh::LeanObject,
    mut v_inst_2919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2920_ =
        l_Std_HashSet_instRepr(v_00_u03b1_2916_, v_inst_2917_, v_inst_2918_, v_inst_2919_);
    leanh::lean_dec_ref(v_inst_2918_);
    leanh::lean_dec_ref(v_inst_2917_);
    return v_res_2920_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashSet_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashSet_Basic(builtin);
}