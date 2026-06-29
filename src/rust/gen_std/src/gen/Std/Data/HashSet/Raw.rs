// Lean compiler output
// Module: Std.Data.HashSet.Raw
// Imports: Std.Data.HashMap.Raw
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
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_inter___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Raw::{
    l_Std_DHashMap_Raw_Const_beq___redArg, l_Std_DHashMap_Raw_Internal_numBuckets___redArg,
    l_Std_DHashMap_Raw_instDecidableMem___redArg,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2;
use crate::r#gen::Std::Data::HashMap::Raw::{
    initialize_Std_Data_HashMap_Raw, runtime_initialize_Std_Data_HashMap_Raw,
};
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
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashSet_Raw_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [72, 97, 115, 104, 83, 101, 116, 0],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__3_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            4197276704451117917 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            18086102783661291962 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_HashSet_Raw_term___x7em___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            17417104850251625812 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__9_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__13_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_HashSet_Raw_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,4197276704451117917 as *mut crate::leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value) as *mut crate::leanh::LeanObject,18086102783661291962 as *mut crate::leanh::LeanObject] };
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,8576336600160769941 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1: u8 = 0;
pub static l_Std_HashSet_Raw_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__10_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashSet_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashSet_Raw_toList___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__11_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashSet_Raw_toList___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_toList___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofList___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofList___redArg___closed__1_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashSet_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashSet_Raw_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_toArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashSet_Raw_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_union___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_union___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_union___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_HashSet_Raw_beq___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_Raw_beq___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashSet_Raw_all___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_HashSet_Raw_all___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_all___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_ofArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
        core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_ofArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value:
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
        83, 116, 100, 46, 72, 97, 115, 104, 83, 101, 116, 46, 82, 97, 119, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___redArg(
    mut v_capacity_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1389_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1390_ = lean_nat_mul(v_capacity_1387_, v___x_1389_);
    v___x_1391_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1392_ = lean_nat_div(v___x_1390_, v___x_1391_);
    crate::leanh::lean_dec(v___x_1390_);
    v___x_1393_ = l_Nat_nextPowerOfTwo(v___x_1392_);
    crate::leanh::lean_dec(v___x_1392_);
    v___x_1394_ = crate::leanh::lean_box(0);
    v___x_1395_ = lean_mk_array(v___x_1393_, v___x_1394_);
    v___x_1396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1396_, 0, v___x_1388_);
    crate::leanh::lean_ctor_set(v___x_1396_, 1, v___x_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Std_HashSet_Raw_emptyWithCapacity___redArg(v_capacity_1397_);
    crate::leanh::lean_dec(v_capacity_1397_);
    return v_res_1398_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity(
    mut v_00_u03b1_1399_: *mut crate::leanh::LeanObject,
    mut v_capacity_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1402_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1403_ = lean_nat_mul(v_capacity_1400_, v___x_1402_);
    v___x_1404_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1405_ = lean_nat_div(v___x_1403_, v___x_1404_);
    crate::leanh::lean_dec(v___x_1403_);
    v___x_1406_ = l_Nat_nextPowerOfTwo(v___x_1405_);
    crate::leanh::lean_dec(v___x_1405_);
    v___x_1407_ = crate::leanh::lean_box(0);
    v___x_1408_ = lean_mk_array(v___x_1406_, v___x_1407_);
    v___x_1409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1409_, 0, v___x_1401_);
    crate::leanh::lean_ctor_set(v___x_1409_, 1, v___x_1408_);
    return v___x_1409_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___boxed(
    mut v_00_u03b1_1410_: *mut crate::leanh::LeanObject,
    mut v_capacity_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Std_HashSet_Raw_emptyWithCapacity(v_00_u03b1_1410_, v_capacity_1411_);
    crate::leanh::lean_dec(v_capacity_1411_);
    return v_res_1412_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = crate::leanh::lean_box(0);
    v___x_1414_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1415_ = lean_mk_array(v___x_1414_, v___x_1413_);
    return v___x_1415_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0,
    );
    v___x_1417_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    crate::leanh::lean_ctor_set(v___x_1418_, 1, v___x_1416_);
    return v___x_1418_;
}
pub unsafe fn l_Std_HashSet_Raw_instEmptyCollection(
    mut v_00_u03b1_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    return v___x_1420_;
}
pub unsafe fn l_Std_HashSet_Raw_instInhabited(
    mut v_00_u03b1_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    return v___x_1422_;
}
pub unsafe fn _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5;
    v___x_1464_ = l_String_toRawSubstring_x27(v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(
    mut v_x_1486_: *mut crate::leanh::LeanObject,
    mut v_a_1487_: *mut crate::leanh::LeanObject,
    mut v_a_1488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    v___x_1489_ = l_Std_HashSet_Raw_term___x7em___00__closed__4;
    crate::leanh::lean_inc(v_x_1486_);
    v___x_1490_ = l_Lean_Syntax_isOfKind(v_x_1486_, v___x_1489_);
    if v___x_1490_ == 0 {
        let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1486_);
        v___x_1491_ = crate::leanh::lean_box(1);
        v___x_1492_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1492_, 0, v___x_1491_);
        crate::leanh::lean_ctor_set(v___x_1492_, 1, v_a_1488_);
        return v___x_1492_;
    } else {
        let mut v_quotContext_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: u8 = 0;
        let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1493_ = crate::leanh::lean_ctor_get(v_a_1487_, 1);
        v_currMacroScope_1494_ = crate::leanh::lean_ctor_get(v_a_1487_, 2);
        v_ref_1495_ = crate::leanh::lean_ctor_get(v_a_1487_, 5);
        v___x_1496_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1497_ = l_Lean_Syntax_getArg(v_x_1486_, v___x_1496_);
        v___x_1498_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1499_ = l_Lean_Syntax_getArg(v_x_1486_, v___x_1498_);
        crate::leanh::lean_dec(v_x_1486_);
        v___x_1500_ = 0;
        v___x_1501_ = l_Lean_SourceInfo_fromRef(v_ref_1495_, v___x_1500_);
        v___x_1502_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4;
        v___x_1503_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once), _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
        v___x_1504_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_1494_);
        crate::leanh::lean_inc(v_quotContext_1493_);
        v___x_1505_ =
            l_Lean_addMacroScope(v_quotContext_1493_, v___x_1504_, v_currMacroScope_1494_);
        v___x_1506_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12;
        crate::leanh::lean_inc_n(v___x_1501_, 2);
        v___x_1507_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1501_);
        crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1503_);
        crate::leanh::lean_ctor_set(v___x_1507_, 2, v___x_1505_);
        crate::leanh::lean_ctor_set(v___x_1507_, 3, v___x_1506_);
        v___x_1508_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14;
        v___x_1509_ = l_Lean_Syntax_node2(v___x_1501_, v___x_1508_, v___x_1497_, v___x_1499_);
        v___x_1510_ = l_Lean_Syntax_node2(v___x_1501_, v___x_1502_, v___x_1507_, v___x_1509_);
        v___x_1511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
        crate::leanh::lean_ctor_set(v___x_1511_, 1, v_a_1488_);
        return v___x_1511_;
    }
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(
    mut v_x_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
    mut v_a_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(v_x_1512_, v_a_1513_, v_a_1514_);
    crate::leanh::lean_dec_ref(v_a_1513_);
    return v_res_1515_;
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(
    mut v_x_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
    mut v_a_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: u8 = 0;
    v___x_1522_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4;
    crate::leanh::lean_inc(v_x_1519_);
    v___x_1523_ = l_Lean_Syntax_isOfKind(v_x_1519_, v___x_1522_);
    if v___x_1523_ == 0 {
        let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1519_);
        v___x_1524_ = crate::leanh::lean_box(0);
        v___x_1525_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1524_);
        crate::leanh::lean_ctor_set(v___x_1525_, 1, v_a_1521_);
        return v___x_1525_;
    } else {
        let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: u8 = 0;
        v___x_1526_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1527_ = l_Lean_Syntax_getArg(v_x_1519_, v___x_1526_);
        v___x_1528_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_1527_);
        v___x_1529_ = l_Lean_Syntax_isOfKind(v___x_1527_, v___x_1528_);
        if v___x_1529_ == 0 {
            let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1527_);
            crate::leanh::lean_dec(v_x_1519_);
            v___x_1530_ = crate::leanh::lean_box(0);
            v___x_1531_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
            crate::leanh::lean_ctor_set(v___x_1531_, 1, v_a_1521_);
            return v___x_1531_;
        } else {
            let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1535_: u8 = 0;
            v___x_1532_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1533_ = l_Lean_Syntax_getArg(v_x_1519_, v___x_1532_);
            crate::leanh::lean_dec(v_x_1519_);
            v___x_1534_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1533_);
            v___x_1535_ = l_Lean_Syntax_matchesNull(v___x_1533_, v___x_1534_);
            if v___x_1535_ == 0 {
                let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1533_);
                crate::leanh::lean_dec(v___x_1527_);
                v___x_1536_ = crate::leanh::lean_box(0);
                v___x_1537_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                crate::leanh::lean_ctor_set(v___x_1537_, 1, v_a_1521_);
                return v___x_1537_;
            } else {
                let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1541_: u8 = 0;
                let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1538_ = l_Lean_Syntax_getArg(v___x_1533_, v___x_1526_);
                v___x_1539_ = l_Lean_Syntax_getArg(v___x_1533_, v___x_1532_);
                crate::leanh::lean_dec(v___x_1533_);
                v_ref_1540_ = l_Lean_replaceRef(v___x_1527_, v_a_1520_);
                crate::leanh::lean_dec(v___x_1527_);
                v___x_1541_ = 0;
                v___x_1542_ = l_Lean_SourceInfo_fromRef(v_ref_1540_, v___x_1541_);
                crate::leanh::lean_dec(v_ref_1540_);
                v___x_1543_ = l_Std_HashSet_Raw_term___x7em___00__closed__4;
                v___x_1544_ = l_Std_HashSet_Raw_term___x7em___00__closed__7;
                crate::leanh::lean_inc(v___x_1542_);
                v___x_1545_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1545_, 0, v___x_1542_);
                crate::leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
                v___x_1546_ = l_Lean_Syntax_node3(
                    v___x_1542_,
                    v___x_1543_,
                    v___x_1538_,
                    v___x_1545_,
                    v___x_1539_,
                );
                v___x_1547_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1547_, 0, v___x_1546_);
                crate::leanh::lean_ctor_set(v___x_1547_, 1, v_a_1521_);
                return v___x_1547_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(
    mut v_x_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ =
        l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(
            v_x_1548_, v_a_1549_, v_a_1550_,
        );
    crate::leanh::lean_dec(v_a_1549_);
    return v_res_1551_;
}
pub unsafe fn l_Std_HashSet_Raw_insert___redArg(
    mut v_inst_1552_: *mut crate::leanh::LeanObject,
    mut v_inst_1553_: *mut crate::leanh::LeanObject,
    mut v_m_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    v_buckets_1556_ = crate::leanh::lean_ctor_get(v_m_1554_, 1);
    v___x_1557_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1558_ = lean_array_get_size(v_buckets_1556_);
    v___x_1559_ = lean_nat_dec_lt(v___x_1557_, v___x_1558_);
    if v___x_1559_ == 0 {
        crate::leanh::lean_dec(v_a_1555_);
        crate::leanh::lean_dec_ref(v_inst_1553_);
        crate::leanh::lean_dec_ref(v_inst_1552_);
        return v_m_1554_;
    } else {
        let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1560_ = crate::leanh::lean_box(0);
        v___x_1561_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_1552_,
            v_inst_1553_,
            v_m_1554_,
            v_a_1555_,
            v___x_1560_,
        );
        return v___x_1561_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_insert(
    mut v_00_u03b1_1562_: *mut crate::leanh::LeanObject,
    mut v_inst_1563_: *mut crate::leanh::LeanObject,
    mut v_inst_1564_: *mut crate::leanh::LeanObject,
    mut v_m_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    v_buckets_1567_ = crate::leanh::lean_ctor_get(v_m_1565_, 1);
    v___x_1568_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1569_ = lean_array_get_size(v_buckets_1567_);
    v___x_1570_ = lean_nat_dec_lt(v___x_1568_, v___x_1569_);
    if v___x_1570_ == 0 {
        crate::leanh::lean_dec(v_a_1566_);
        crate::leanh::lean_dec_ref(v_inst_1564_);
        crate::leanh::lean_dec_ref(v_inst_1563_);
        return v_m_1565_;
    } else {
        let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1571_ = crate::leanh::lean_box(0);
        v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_1563_,
            v_inst_1564_,
            v_m_1565_,
            v_a_1566_,
            v___x_1571_,
        );
        return v___x_1572_;
    }
}
pub unsafe fn _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0,
    );
    v___x_1574_ = lean_array_get_size(v___x_1573_);
    return v___x_1574_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1()
-> u8 {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    v___x_1575_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0,
    );
    v___x_1576_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1577_ = lean_nat_dec_lt(v___x_1576_, v___x_1575_);
    return v___x_1577_;
}
pub unsafe fn l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(
    mut v_inst_1578_: *mut crate::leanh::LeanObject,
    mut v_inst_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    v___x_1581_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_1582_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_1582_ == 0 {
        crate::leanh::lean_dec(v_a_1580_);
        crate::leanh::lean_dec_ref(v_inst_1579_);
        crate::leanh::lean_dec_ref(v_inst_1578_);
        return v___x_1581_;
    } else {
        let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1583_ = crate::leanh::lean_box(0);
        v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_1578_,
            v_inst_1579_,
            v___x_1581_,
            v_a_1580_,
            v___x_1583_,
        );
        return v___x_1584_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(
    mut v_inst_1585_: *mut crate::leanh::LeanObject,
    mut v_inst_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1587_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1587_, 0, v_inst_1585_);
    crate::leanh::lean_closure_set(v___f_1587_, 1, v_inst_1586_);
    return v___f_1587_;
}
pub unsafe fn l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(
    mut v_00_u03b1_1588_: *mut crate::leanh::LeanObject,
    mut v_inst_1589_: *mut crate::leanh::LeanObject,
    mut v_inst_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1591_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1591_, 0, v_inst_1589_);
    crate::leanh::lean_closure_set(v___f_1591_, 1, v_inst_1590_);
    return v___f_1591_;
}
pub unsafe fn l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(
    mut v_inst_1592_: *mut crate::leanh::LeanObject,
    mut v_inst_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
    mut v_s_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    v_buckets_1596_ = crate::leanh::lean_ctor_get(v_s_1595_, 1);
    v___x_1597_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1598_ = lean_array_get_size(v_buckets_1596_);
    v___x_1599_ = lean_nat_dec_lt(v___x_1597_, v___x_1598_);
    if v___x_1599_ == 0 {
        crate::leanh::lean_dec(v_a_1594_);
        crate::leanh::lean_dec_ref(v_inst_1593_);
        crate::leanh::lean_dec_ref(v_inst_1592_);
        return v_s_1595_;
    } else {
        let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1600_ = crate::leanh::lean_box(0);
        v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_1592_,
            v_inst_1593_,
            v_s_1595_,
            v_a_1594_,
            v___x_1600_,
        );
        return v___x_1601_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(
    mut v_inst_1602_: *mut crate::leanh::LeanObject,
    mut v_inst_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1604_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1604_, 0, v_inst_1602_);
    crate::leanh::lean_closure_set(v___f_1604_, 1, v_inst_1603_);
    return v___f_1604_;
}
pub unsafe fn l_Std_HashSet_Raw_instInsertOfBEqOfHashable(
    mut v_00_u03b1_1605_: *mut crate::leanh::LeanObject,
    mut v_inst_1606_: *mut crate::leanh::LeanObject,
    mut v_inst_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1608_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1608_, 0, v_inst_1606_);
    crate::leanh::lean_closure_set(v___f_1608_, 1, v_inst_1607_);
    return v___f_1608_;
}
pub unsafe fn l_Std_HashSet_Raw_containsThenInsert___redArg(
    mut v_inst_1609_: *mut crate::leanh::LeanObject,
    mut v_inst_1610_: *mut crate::leanh::LeanObject,
    mut v_m_1611_: *mut crate::leanh::LeanObject,
    mut v_a_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: u64 = 0;
    let mut v___x_1622_: u64 = 0;
    let mut v___x_1623_: u64 = 0;
    let mut v___x_1624_: u64 = 0;
    let mut v_fold_1625_: u64 = 0;
    let mut v___x_1626_: u64 = 0;
    let mut v___x_1627_: u64 = 0;
    let mut v___x_1628_: u64 = 0;
    let mut v___x_1629_: usize = 0;
    let mut v___x_1630_: usize = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: usize = 0;
    let mut v___x_1633_: usize = 0;
    let mut v_bkt_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v_val_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v_unused_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1613_ = crate::leanh::lean_ctor_get(v_m_1611_, 0);
                v_buckets_1614_ = crate::leanh::lean_ctor_get(v_m_1611_, 1);
                v___x_1615_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1616_ = lean_array_get_size(v_buckets_1614_);
                v___x_1617_ = lean_nat_dec_lt(v___x_1615_, v___x_1616_);
                if v___x_1617_ == 0 {
                    crate::leanh::lean_dec(v_a_1612_);
                    crate::leanh::lean_dec_ref(v_inst_1610_);
                    crate::leanh::lean_dec_ref(v_inst_1609_);
                    v___x_1618_ = crate::leanh::lean_box((v___x_1617_) as usize);
                    v___x_1619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1619_, 0, v___x_1618_);
                    crate::leanh::lean_ctor_set(v___x_1619_, 1, v_m_1611_);
                    return v___x_1619_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_1610_);
                    crate::leanh::lean_inc_n(v_a_1612_, 2);
                    v___x_1620_ = crate::leanh::lean_apply_1(v_inst_1610_, v_a_1612_);
                    v___x_1621_ = 32u64;
                    v___x_1622_ = crate::leanh::lean_unbox_uint64(v___x_1620_);
                    v___x_1623_ = lean_uint64_shift_right(v___x_1622_, v___x_1621_);
                    v___x_1624_ = crate::leanh::lean_unbox_uint64(v___x_1620_);
                    crate::leanh::lean_dec_ref(v___x_1620_);
                    v_fold_1625_ = lean_uint64_xor(v___x_1624_, v___x_1623_);
                    v___x_1626_ = 16u64;
                    v___x_1627_ = lean_uint64_shift_right(v_fold_1625_, v___x_1626_);
                    v___x_1628_ = lean_uint64_xor(v_fold_1625_, v___x_1627_);
                    v___x_1629_ = lean_uint64_to_usize(v___x_1628_);
                    v___x_1630_ = lean_usize_of_nat(v___x_1616_);
                    v___x_1631_ = 1usize;
                    v___x_1632_ = lean_usize_sub(v___x_1630_, v___x_1631_);
                    v___x_1633_ = lean_usize_land(v___x_1629_, v___x_1632_);
                    v_bkt_1634_ = lean_array_uget_borrowed(v_buckets_1614_, v___x_1633_);
                    crate::leanh::lean_inc(v_bkt_1634_);
                    v___x_1635_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_1609_,
                        v_a_1612_,
                        v_bkt_1634_,
                    );
                    if v___x_1635_ == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_1614_);
                        crate::leanh::lean_inc(v_size_1613_);
                        v_isSharedCheck_1661_ = (!crate::leanh::lean_is_exclusive(v_m_1611_)) as u8;
                        if v_isSharedCheck_1661_ == 0 {
                            v_unused_1662_ = crate::leanh::lean_ctor_get(v_m_1611_, 1);
                            crate::leanh::lean_dec(v_unused_1662_);
                            v_unused_1663_ = crate::leanh::lean_ctor_get(v_m_1611_, 0);
                            crate::leanh::lean_dec(v_unused_1663_);
                            v___x_1637_ = v_m_1611_;
                            v_isShared_1638_ = v_isSharedCheck_1661_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_1611_);
                            v___x_1637_ = crate::leanh::lean_box(0);
                            v_isShared_1638_ = v_isSharedCheck_1661_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1612_);
                        crate::leanh::lean_dec_ref(v_inst_1610_);
                        v___x_1664_ = crate::leanh::lean_box((v___x_1635_) as usize);
                        v___x_1665_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1664_);
                        crate::leanh::lean_ctor_set(v___x_1665_, 1, v_m_1611_);
                        return v___x_1665_;
                    }
                }
            }
            1 => {
                v___x_1639_ = crate::leanh::lean_box(0);
                v___x_1640_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1641_ = lean_nat_add(v_size_1613_, v___x_1640_);
                crate::leanh::lean_dec(v_size_1613_);
                crate::leanh::lean_inc(v_bkt_1634_);
                v___x_1642_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1642_, 0, v_a_1612_);
                crate::leanh::lean_ctor_set(v___x_1642_, 1, v___x_1639_);
                crate::leanh::lean_ctor_set(v___x_1642_, 2, v_bkt_1634_);
                v_buckets_x27_1643_ = lean_array_uset(v_buckets_1614_, v___x_1633_, v___x_1642_);
                v___x_1644_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1645_ = lean_nat_mul(v_size_x27_1641_, v___x_1644_);
                v___x_1646_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1647_ = lean_nat_div(v___x_1645_, v___x_1646_);
                crate::leanh::lean_dec(v___x_1645_);
                v___x_1648_ = lean_array_get_size(v_buckets_x27_1643_);
                v___x_1649_ = lean_nat_dec_le(v___x_1647_, v___x_1648_);
                crate::leanh::lean_dec(v___x_1647_);
                if v___x_1649_ == 0 {
                    v_val_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_1610_,
                        v_buckets_x27_1643_,
                    );
                    if v_isShared_1638_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1637_, 1, v_val_1650_);
                        crate::leanh::lean_ctor_set(v___x_1637_, 0, v_size_x27_1641_);
                        v___x_1652_ = v___x_1637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_size_x27_1641_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_val_1650_);
                        v___x_1652_ = v_reuseFailAlloc_1655_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1610_);
                    if v_isShared_1638_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1637_, 1, v_buckets_x27_1643_);
                        crate::leanh::lean_ctor_set(v___x_1637_, 0, v_size_x27_1641_);
                        v___x_1657_ = v___x_1637_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1660_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_size_x27_1641_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_buckets_x27_1643_);
                        v___x_1657_ = v_reuseFailAlloc_1660_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1653_ = crate::leanh::lean_box((v___x_1635_) as usize);
                v___x_1654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1654_, 0, v___x_1653_);
                crate::leanh::lean_ctor_set(v___x_1654_, 1, v___x_1652_);
                return v___x_1654_;
            }
            3 => {
                v___x_1658_ = crate::leanh::lean_box((v___x_1635_) as usize);
                v___x_1659_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1659_, 0, v___x_1658_);
                crate::leanh::lean_ctor_set(v___x_1659_, 1, v___x_1657_);
                return v___x_1659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_containsThenInsert(
    mut v_00_u03b1_1666_: *mut crate::leanh::LeanObject,
    mut v_inst_1667_: *mut crate::leanh::LeanObject,
    mut v_inst_1668_: *mut crate::leanh::LeanObject,
    mut v_m_1669_: *mut crate::leanh::LeanObject,
    mut v_a_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u64 = 0;
    let mut v___x_1680_: u64 = 0;
    let mut v___x_1681_: u64 = 0;
    let mut v___x_1682_: u64 = 0;
    let mut v_fold_1683_: u64 = 0;
    let mut v___x_1684_: u64 = 0;
    let mut v___x_1685_: u64 = 0;
    let mut v___x_1686_: u64 = 0;
    let mut v___x_1687_: usize = 0;
    let mut v___x_1688_: usize = 0;
    let mut v___x_1689_: usize = 0;
    let mut v___x_1690_: usize = 0;
    let mut v___x_1691_: usize = 0;
    let mut v_bkt_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v_val_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut v_unused_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1671_ = crate::leanh::lean_ctor_get(v_m_1669_, 0);
                v_buckets_1672_ = crate::leanh::lean_ctor_get(v_m_1669_, 1);
                v___x_1673_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1674_ = lean_array_get_size(v_buckets_1672_);
                v___x_1675_ = lean_nat_dec_lt(v___x_1673_, v___x_1674_);
                if v___x_1675_ == 0 {
                    crate::leanh::lean_dec(v_a_1670_);
                    crate::leanh::lean_dec_ref(v_inst_1668_);
                    crate::leanh::lean_dec_ref(v_inst_1667_);
                    v___x_1676_ = crate::leanh::lean_box((v___x_1675_) as usize);
                    v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
                    crate::leanh::lean_ctor_set(v___x_1677_, 1, v_m_1669_);
                    return v___x_1677_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_1668_);
                    crate::leanh::lean_inc_n(v_a_1670_, 2);
                    v___x_1678_ = crate::leanh::lean_apply_1(v_inst_1668_, v_a_1670_);
                    v___x_1679_ = 32u64;
                    v___x_1680_ = crate::leanh::lean_unbox_uint64(v___x_1678_);
                    v___x_1681_ = lean_uint64_shift_right(v___x_1680_, v___x_1679_);
                    v___x_1682_ = crate::leanh::lean_unbox_uint64(v___x_1678_);
                    crate::leanh::lean_dec_ref(v___x_1678_);
                    v_fold_1683_ = lean_uint64_xor(v___x_1682_, v___x_1681_);
                    v___x_1684_ = 16u64;
                    v___x_1685_ = lean_uint64_shift_right(v_fold_1683_, v___x_1684_);
                    v___x_1686_ = lean_uint64_xor(v_fold_1683_, v___x_1685_);
                    v___x_1687_ = lean_uint64_to_usize(v___x_1686_);
                    v___x_1688_ = lean_usize_of_nat(v___x_1674_);
                    v___x_1689_ = 1usize;
                    v___x_1690_ = lean_usize_sub(v___x_1688_, v___x_1689_);
                    v___x_1691_ = lean_usize_land(v___x_1687_, v___x_1690_);
                    v_bkt_1692_ = lean_array_uget_borrowed(v_buckets_1672_, v___x_1691_);
                    crate::leanh::lean_inc(v_bkt_1692_);
                    v___x_1693_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_1667_,
                        v_a_1670_,
                        v_bkt_1692_,
                    );
                    if v___x_1693_ == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_1672_);
                        crate::leanh::lean_inc(v_size_1671_);
                        v_isSharedCheck_1719_ = (!crate::leanh::lean_is_exclusive(v_m_1669_)) as u8;
                        if v_isSharedCheck_1719_ == 0 {
                            v_unused_1720_ = crate::leanh::lean_ctor_get(v_m_1669_, 1);
                            crate::leanh::lean_dec(v_unused_1720_);
                            v_unused_1721_ = crate::leanh::lean_ctor_get(v_m_1669_, 0);
                            crate::leanh::lean_dec(v_unused_1721_);
                            v___x_1695_ = v_m_1669_;
                            v_isShared_1696_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_1669_);
                            v___x_1695_ = crate::leanh::lean_box(0);
                            v_isShared_1696_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1670_);
                        crate::leanh::lean_dec_ref(v_inst_1668_);
                        v___x_1722_ = crate::leanh::lean_box((v___x_1693_) as usize);
                        v___x_1723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1723_, 0, v___x_1722_);
                        crate::leanh::lean_ctor_set(v___x_1723_, 1, v_m_1669_);
                        return v___x_1723_;
                    }
                }
            }
            1 => {
                v___x_1697_ = crate::leanh::lean_box(0);
                v___x_1698_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1699_ = lean_nat_add(v_size_1671_, v___x_1698_);
                crate::leanh::lean_dec(v_size_1671_);
                crate::leanh::lean_inc(v_bkt_1692_);
                v___x_1700_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1700_, 0, v_a_1670_);
                crate::leanh::lean_ctor_set(v___x_1700_, 1, v___x_1697_);
                crate::leanh::lean_ctor_set(v___x_1700_, 2, v_bkt_1692_);
                v_buckets_x27_1701_ = lean_array_uset(v_buckets_1672_, v___x_1691_, v___x_1700_);
                v___x_1702_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1703_ = lean_nat_mul(v_size_x27_1699_, v___x_1702_);
                v___x_1704_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1705_ = lean_nat_div(v___x_1703_, v___x_1704_);
                crate::leanh::lean_dec(v___x_1703_);
                v___x_1706_ = lean_array_get_size(v_buckets_x27_1701_);
                v___x_1707_ = lean_nat_dec_le(v___x_1705_, v___x_1706_);
                crate::leanh::lean_dec(v___x_1705_);
                if v___x_1707_ == 0 {
                    v_val_1708_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_1668_,
                        v_buckets_x27_1701_,
                    );
                    if v_isShared_1696_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1695_, 1, v_val_1708_);
                        crate::leanh::lean_ctor_set(v___x_1695_, 0, v_size_x27_1699_);
                        v___x_1710_ = v___x_1695_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_size_x27_1699_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_val_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1713_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1668_);
                    if v_isShared_1696_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1695_, 1, v_buckets_x27_1701_);
                        crate::leanh::lean_ctor_set(v___x_1695_, 0, v_size_x27_1699_);
                        v___x_1715_ = v___x_1695_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_size_x27_1699_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_buckets_x27_1701_);
                        v___x_1715_ = v_reuseFailAlloc_1718_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1711_ = crate::leanh::lean_box((v___x_1693_) as usize);
                v___x_1712_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1712_, 0, v___x_1711_);
                crate::leanh::lean_ctor_set(v___x_1712_, 1, v___x_1710_);
                return v___x_1712_;
            }
            3 => {
                v___x_1716_ = crate::leanh::lean_box((v___x_1693_) as usize);
                v___x_1717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1716_);
                crate::leanh::lean_ctor_set(v___x_1717_, 1, v___x_1715_);
                return v___x_1717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_contains___redArg(
    mut v_inst_1724_: *mut crate::leanh::LeanObject,
    mut v_inst_1725_: *mut crate::leanh::LeanObject,
    mut v_m_1726_: *mut crate::leanh::LeanObject,
    mut v_a_1727_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    v_buckets_1728_ = crate::leanh::lean_ctor_get(v_m_1726_, 1);
    v___x_1729_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1730_ = lean_array_get_size(v_buckets_1728_);
    v___x_1731_ = lean_nat_dec_lt(v___x_1729_, v___x_1730_);
    if v___x_1731_ == 0 {
        crate::leanh::lean_dec(v_a_1727_);
        crate::leanh::lean_dec_ref(v_inst_1725_);
        crate::leanh::lean_dec_ref(v_inst_1724_);
        return v___x_1731_;
    } else {
        let mut v___x_1732_: u8 = 0;
        v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_1724_,
            v_inst_1725_,
            v_m_1726_,
            v_a_1727_,
        );
        return v___x_1732_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_contains___redArg___boxed(
    mut v_inst_1733_: *mut crate::leanh::LeanObject,
    mut v_inst_1734_: *mut crate::leanh::LeanObject,
    mut v_m_1735_: *mut crate::leanh::LeanObject,
    mut v_a_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1737_: u8 = 0;
    let mut v_r_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1737_ =
        l_Std_HashSet_Raw_contains___redArg(v_inst_1733_, v_inst_1734_, v_m_1735_, v_a_1736_);
    crate::leanh::lean_dec_ref(v_m_1735_);
    v_r_1738_ = crate::leanh::lean_box((v_res_1737_) as usize);
    return v_r_1738_;
}
pub unsafe fn l_Std_HashSet_Raw_contains(
    mut v_00_u03b1_1739_: *mut crate::leanh::LeanObject,
    mut v_inst_1740_: *mut crate::leanh::LeanObject,
    mut v_inst_1741_: *mut crate::leanh::LeanObject,
    mut v_m_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    v_buckets_1744_ = crate::leanh::lean_ctor_get(v_m_1742_, 1);
    v___x_1745_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1746_ = lean_array_get_size(v_buckets_1744_);
    v___x_1747_ = lean_nat_dec_lt(v___x_1745_, v___x_1746_);
    if v___x_1747_ == 0 {
        crate::leanh::lean_dec(v_a_1743_);
        crate::leanh::lean_dec_ref(v_inst_1741_);
        crate::leanh::lean_dec_ref(v_inst_1740_);
        return v___x_1747_;
    } else {
        let mut v___x_1748_: u8 = 0;
        v___x_1748_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_1740_,
            v_inst_1741_,
            v_m_1742_,
            v_a_1743_,
        );
        return v___x_1748_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_contains___boxed(
    mut v_00_u03b1_1749_: *mut crate::leanh::LeanObject,
    mut v_inst_1750_: *mut crate::leanh::LeanObject,
    mut v_inst_1751_: *mut crate::leanh::LeanObject,
    mut v_m_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1754_: u8 = 0;
    let mut v_r_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Std_HashSet_Raw_contains(
        v_00_u03b1_1749_,
        v_inst_1750_,
        v_inst_1751_,
        v_m_1752_,
        v_a_1753_,
    );
    crate::leanh::lean_dec_ref(v_m_1752_);
    v_r_1755_ = crate::leanh::lean_box((v_res_1754_) as usize);
    return v_r_1755_;
}
pub unsafe fn l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(
    mut v_00_u03b1_1756_: *mut crate::leanh::LeanObject,
    mut v_inst_1757_: *mut crate::leanh::LeanObject,
    mut v_inst_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ = crate::leanh::lean_box(0);
    return v___x_1759_;
}
pub unsafe fn l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(
    mut v_00_u03b1_1760_: *mut crate::leanh::LeanObject,
    mut v_inst_1761_: *mut crate::leanh::LeanObject,
    mut v_inst_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(
        v_00_u03b1_1760_,
        v_inst_1761_,
        v_inst_1762_,
    );
    crate::leanh::lean_dec_ref(v_inst_1762_);
    crate::leanh::lean_dec_ref(v_inst_1761_);
    return v_res_1763_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem___redArg(
    mut v_inst_1764_: *mut crate::leanh::LeanObject,
    mut v_inst_1765_: *mut crate::leanh::LeanObject,
    mut v_m_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1768_: u8 = 0;
    v___x_1768_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(
        v_inst_1764_,
        v_inst_1765_,
        v_m_1766_,
        v_a_1767_,
    );
    return v___x_1768_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(
    mut v_inst_1769_: *mut crate::leanh::LeanObject,
    mut v_inst_1770_: *mut crate::leanh::LeanObject,
    mut v_m_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1773_: u8 = 0;
    let mut v_r_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1773_ = l_Std_HashSet_Raw_instDecidableMem___redArg(
        v_inst_1769_,
        v_inst_1770_,
        v_m_1771_,
        v_a_1772_,
    );
    crate::leanh::lean_dec_ref(v_m_1771_);
    v_r_1774_ = crate::leanh::lean_box((v_res_1773_) as usize);
    return v_r_1774_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem(
    mut v_00_u03b1_1775_: *mut crate::leanh::LeanObject,
    mut v_inst_1776_: *mut crate::leanh::LeanObject,
    mut v_inst_1777_: *mut crate::leanh::LeanObject,
    mut v_m_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1780_: u8 = 0;
    v___x_1780_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(
        v_inst_1776_,
        v_inst_1777_,
        v_m_1778_,
        v_a_1779_,
    );
    return v___x_1780_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem___boxed(
    mut v_00_u03b1_1781_: *mut crate::leanh::LeanObject,
    mut v_inst_1782_: *mut crate::leanh::LeanObject,
    mut v_inst_1783_: *mut crate::leanh::LeanObject,
    mut v_m_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1786_: u8 = 0;
    let mut v_r_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Std_HashSet_Raw_instDecidableMem(
        v_00_u03b1_1781_,
        v_inst_1782_,
        v_inst_1783_,
        v_m_1784_,
        v_a_1785_,
    );
    crate::leanh::lean_dec_ref(v_m_1784_);
    v_r_1787_ = crate::leanh::lean_box((v_res_1786_) as usize);
    return v_r_1787_;
}
pub unsafe fn l_Std_HashSet_Raw_erase___redArg(
    mut v_inst_1788_: *mut crate::leanh::LeanObject,
    mut v_inst_1789_: *mut crate::leanh::LeanObject,
    mut v_m_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: u8 = 0;
    v_buckets_1792_ = crate::leanh::lean_ctor_get(v_m_1790_, 1);
    v___x_1793_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1794_ = lean_array_get_size(v_buckets_1792_);
    v___x_1795_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
    if v___x_1795_ == 0 {
        crate::leanh::lean_dec(v_a_1791_);
        crate::leanh::lean_dec_ref(v_inst_1789_);
        crate::leanh::lean_dec_ref(v_inst_1788_);
        return v_m_1790_;
    } else {
        let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1796_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
            v_inst_1788_,
            v_inst_1789_,
            v_m_1790_,
            v_a_1791_,
        );
        return v___x_1796_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_erase(
    mut v_00_u03b1_1797_: *mut crate::leanh::LeanObject,
    mut v_inst_1798_: *mut crate::leanh::LeanObject,
    mut v_inst_1799_: *mut crate::leanh::LeanObject,
    mut v_m_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    v_buckets_1802_ = crate::leanh::lean_ctor_get(v_m_1800_, 1);
    v___x_1803_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1804_ = lean_array_get_size(v_buckets_1802_);
    v___x_1805_ = lean_nat_dec_lt(v___x_1803_, v___x_1804_);
    if v___x_1805_ == 0 {
        crate::leanh::lean_dec(v_a_1801_);
        crate::leanh::lean_dec_ref(v_inst_1799_);
        crate::leanh::lean_dec_ref(v_inst_1798_);
        return v_m_1800_;
    } else {
        let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
            v_inst_1798_,
            v_inst_1799_,
            v_m_1800_,
            v_a_1801_,
        );
        return v___x_1806_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_size___redArg(
    mut v_m_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_1808_ = crate::leanh::lean_ctor_get(v_m_1807_, 0);
    crate::leanh::lean_inc(v_size_1808_);
    return v_size_1808_;
}
pub unsafe fn l_Std_HashSet_Raw_size___redArg___boxed(
    mut v_m_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Std_HashSet_Raw_size___redArg(v_m_1809_);
    crate::leanh::lean_dec_ref(v_m_1809_);
    return v_res_1810_;
}
pub unsafe fn l_Std_HashSet_Raw_size(
    mut v_00_u03b1_1811_: *mut crate::leanh::LeanObject,
    mut v_m_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_1813_ = crate::leanh::lean_ctor_get(v_m_1812_, 0);
    crate::leanh::lean_inc(v_size_1813_);
    return v_size_1813_;
}
pub unsafe fn l_Std_HashSet_Raw_size___boxed(
    mut v_00_u03b1_1814_: *mut crate::leanh::LeanObject,
    mut v_m_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Std_HashSet_Raw_size(v_00_u03b1_1814_, v_m_1815_);
    crate::leanh::lean_dec_ref(v_m_1815_);
    return v_res_1816_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f___redArg(
    mut v_inst_1817_: *mut crate::leanh::LeanObject,
    mut v_inst_1818_: *mut crate::leanh::LeanObject,
    mut v_m_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    v_buckets_1821_ = crate::leanh::lean_ctor_get(v_m_1819_, 1);
    v___x_1822_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1823_ = lean_array_get_size(v_buckets_1821_);
    v___x_1824_ = lean_nat_dec_lt(v___x_1822_, v___x_1823_);
    if v___x_1824_ == 0 {
        let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1820_);
        crate::leanh::lean_dec_ref(v_inst_1818_);
        crate::leanh::lean_dec_ref(v_inst_1817_);
        v___x_1825_ = crate::leanh::lean_box(0);
        return v___x_1825_;
    } else {
        let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1826_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
            v_inst_1817_,
            v_inst_1818_,
            v_m_1819_,
            v_a_1820_,
        );
        return v___x_1826_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f___redArg___boxed(
    mut v_inst_1827_: *mut crate::leanh::LeanObject,
    mut v_inst_1828_: *mut crate::leanh::LeanObject,
    mut v_m_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1831_ =
        l_Std_HashSet_Raw_get_x3f___redArg(v_inst_1827_, v_inst_1828_, v_m_1829_, v_a_1830_);
    crate::leanh::lean_dec_ref(v_m_1829_);
    return v_res_1831_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f(
    mut v_00_u03b1_1832_: *mut crate::leanh::LeanObject,
    mut v_inst_1833_: *mut crate::leanh::LeanObject,
    mut v_inst_1834_: *mut crate::leanh::LeanObject,
    mut v_m_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    v_buckets_1837_ = crate::leanh::lean_ctor_get(v_m_1835_, 1);
    v___x_1838_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1839_ = lean_array_get_size(v_buckets_1837_);
    v___x_1840_ = lean_nat_dec_lt(v___x_1838_, v___x_1839_);
    if v___x_1840_ == 0 {
        let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1836_);
        crate::leanh::lean_dec_ref(v_inst_1834_);
        crate::leanh::lean_dec_ref(v_inst_1833_);
        v___x_1841_ = crate::leanh::lean_box(0);
        return v___x_1841_;
    } else {
        let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
            v_inst_1833_,
            v_inst_1834_,
            v_m_1835_,
            v_a_1836_,
        );
        return v___x_1842_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f___boxed(
    mut v_00_u03b1_1843_: *mut crate::leanh::LeanObject,
    mut v_inst_1844_: *mut crate::leanh::LeanObject,
    mut v_inst_1845_: *mut crate::leanh::LeanObject,
    mut v_m_1846_: *mut crate::leanh::LeanObject,
    mut v_a_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_HashSet_Raw_get_x3f(
        v_00_u03b1_1843_,
        v_inst_1844_,
        v_inst_1845_,
        v_m_1846_,
        v_a_1847_,
    );
    crate::leanh::lean_dec_ref(v_m_1846_);
    return v_res_1848_;
}
pub unsafe fn l_Std_HashSet_Raw_get___redArg(
    mut v_inst_1849_: *mut crate::leanh::LeanObject,
    mut v_inst_1850_: *mut crate::leanh::LeanObject,
    mut v_m_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1849_,
        v_inst_1850_,
        v_m_1851_,
        v_a_1852_,
    );
    return v___x_1853_;
}
pub unsafe fn l_Std_HashSet_Raw_get___redArg___boxed(
    mut v_inst_1854_: *mut crate::leanh::LeanObject,
    mut v_inst_1855_: *mut crate::leanh::LeanObject,
    mut v_m_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_Std_HashSet_Raw_get___redArg(v_inst_1854_, v_inst_1855_, v_m_1856_, v_a_1857_);
    crate::leanh::lean_dec_ref(v_m_1856_);
    return v_res_1858_;
}
pub unsafe fn l_Std_HashSet_Raw_get(
    mut v_00_u03b1_1859_: *mut crate::leanh::LeanObject,
    mut v_inst_1860_: *mut crate::leanh::LeanObject,
    mut v_inst_1861_: *mut crate::leanh::LeanObject,
    mut v_m_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
    mut v_h_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1860_,
        v_inst_1861_,
        v_m_1862_,
        v_a_1863_,
    );
    return v___x_1865_;
}
pub unsafe fn l_Std_HashSet_Raw_get___boxed(
    mut v_00_u03b1_1866_: *mut crate::leanh::LeanObject,
    mut v_inst_1867_: *mut crate::leanh::LeanObject,
    mut v_inst_1868_: *mut crate::leanh::LeanObject,
    mut v_m_1869_: *mut crate::leanh::LeanObject,
    mut v_a_1870_: *mut crate::leanh::LeanObject,
    mut v_h_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Std_HashSet_Raw_get(
        v_00_u03b1_1866_,
        v_inst_1867_,
        v_inst_1868_,
        v_m_1869_,
        v_a_1870_,
        v_h_1871_,
    );
    crate::leanh::lean_dec_ref(v_m_1869_);
    return v_res_1872_;
}
pub unsafe fn l_Std_HashSet_Raw_getD___redArg(
    mut v_inst_1873_: *mut crate::leanh::LeanObject,
    mut v_inst_1874_: *mut crate::leanh::LeanObject,
    mut v_m_1875_: *mut crate::leanh::LeanObject,
    mut v_a_1876_: *mut crate::leanh::LeanObject,
    mut v_fallback_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    v_buckets_1878_ = crate::leanh::lean_ctor_get(v_m_1875_, 1);
    v___x_1879_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1880_ = lean_array_get_size(v_buckets_1878_);
    v___x_1881_ = lean_nat_dec_lt(v___x_1879_, v___x_1880_);
    if v___x_1881_ == 0 {
        crate::leanh::lean_dec(v_a_1876_);
        crate::leanh::lean_dec_ref(v_inst_1874_);
        crate::leanh::lean_dec_ref(v_inst_1873_);
        crate::leanh::lean_inc(v_fallback_1877_);
        return v_fallback_1877_;
    } else {
        let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1882_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
            v_inst_1873_,
            v_inst_1874_,
            v_m_1875_,
            v_a_1876_,
            v_fallback_1877_,
        );
        return v___x_1882_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_getD___redArg___boxed(
    mut v_inst_1883_: *mut crate::leanh::LeanObject,
    mut v_inst_1884_: *mut crate::leanh::LeanObject,
    mut v_m_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_fallback_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Std_HashSet_Raw_getD___redArg(
        v_inst_1883_,
        v_inst_1884_,
        v_m_1885_,
        v_a_1886_,
        v_fallback_1887_,
    );
    crate::leanh::lean_dec(v_fallback_1887_);
    crate::leanh::lean_dec_ref(v_m_1885_);
    return v_res_1888_;
}
pub unsafe fn l_Std_HashSet_Raw_getD(
    mut v_00_u03b1_1889_: *mut crate::leanh::LeanObject,
    mut v_inst_1890_: *mut crate::leanh::LeanObject,
    mut v_inst_1891_: *mut crate::leanh::LeanObject,
    mut v_m_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_fallback_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u8 = 0;
    v_buckets_1895_ = crate::leanh::lean_ctor_get(v_m_1892_, 1);
    v___x_1896_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1897_ = lean_array_get_size(v_buckets_1895_);
    v___x_1898_ = lean_nat_dec_lt(v___x_1896_, v___x_1897_);
    if v___x_1898_ == 0 {
        crate::leanh::lean_dec(v_a_1893_);
        crate::leanh::lean_dec_ref(v_inst_1891_);
        crate::leanh::lean_dec_ref(v_inst_1890_);
        crate::leanh::lean_inc(v_fallback_1894_);
        return v_fallback_1894_;
    } else {
        let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1899_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
            v_inst_1890_,
            v_inst_1891_,
            v_m_1892_,
            v_a_1893_,
            v_fallback_1894_,
        );
        return v___x_1899_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_getD___boxed(
    mut v_00_u03b1_1900_: *mut crate::leanh::LeanObject,
    mut v_inst_1901_: *mut crate::leanh::LeanObject,
    mut v_inst_1902_: *mut crate::leanh::LeanObject,
    mut v_m_1903_: *mut crate::leanh::LeanObject,
    mut v_a_1904_: *mut crate::leanh::LeanObject,
    mut v_fallback_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Std_HashSet_Raw_getD(
        v_00_u03b1_1900_,
        v_inst_1901_,
        v_inst_1902_,
        v_m_1903_,
        v_a_1904_,
        v_fallback_1905_,
    );
    crate::leanh::lean_dec(v_fallback_1905_);
    crate::leanh::lean_dec_ref(v_m_1903_);
    return v_res_1906_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x21___redArg(
    mut v_inst_1907_: *mut crate::leanh::LeanObject,
    mut v_inst_1908_: *mut crate::leanh::LeanObject,
    mut v_inst_1909_: *mut crate::leanh::LeanObject,
    mut v_m_1910_: *mut crate::leanh::LeanObject,
    mut v_a_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    v_buckets_1912_ = crate::leanh::lean_ctor_get(v_m_1910_, 1);
    v___x_1913_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1914_ = lean_array_get_size(v_buckets_1912_);
    v___x_1915_ = lean_nat_dec_lt(v___x_1913_, v___x_1914_);
    if v___x_1915_ == 0 {
        crate::leanh::lean_dec(v_a_1911_);
        crate::leanh::lean_dec_ref(v_inst_1908_);
        crate::leanh::lean_dec_ref(v_inst_1907_);
        crate::leanh::lean_inc(v_inst_1909_);
        return v_inst_1909_;
    } else {
        let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1916_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
            v_inst_1907_,
            v_inst_1908_,
            v_inst_1909_,
            v_m_1910_,
            v_a_1911_,
        );
        return v___x_1916_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_get_x21___redArg___boxed(
    mut v_inst_1917_: *mut crate::leanh::LeanObject,
    mut v_inst_1918_: *mut crate::leanh::LeanObject,
    mut v_inst_1919_: *mut crate::leanh::LeanObject,
    mut v_m_1920_: *mut crate::leanh::LeanObject,
    mut v_a_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_HashSet_Raw_get_x21___redArg(
        v_inst_1917_,
        v_inst_1918_,
        v_inst_1919_,
        v_m_1920_,
        v_a_1921_,
    );
    crate::leanh::lean_dec_ref(v_m_1920_);
    crate::leanh::lean_dec(v_inst_1919_);
    return v_res_1922_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x21(
    mut v_00_u03b1_1923_: *mut crate::leanh::LeanObject,
    mut v_inst_1924_: *mut crate::leanh::LeanObject,
    mut v_inst_1925_: *mut crate::leanh::LeanObject,
    mut v_inst_1926_: *mut crate::leanh::LeanObject,
    mut v_m_1927_: *mut crate::leanh::LeanObject,
    mut v_a_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    v_buckets_1929_ = crate::leanh::lean_ctor_get(v_m_1927_, 1);
    v___x_1930_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1931_ = lean_array_get_size(v_buckets_1929_);
    v___x_1932_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
    if v___x_1932_ == 0 {
        crate::leanh::lean_dec(v_a_1928_);
        crate::leanh::lean_dec_ref(v_inst_1925_);
        crate::leanh::lean_dec_ref(v_inst_1924_);
        crate::leanh::lean_inc(v_inst_1926_);
        return v_inst_1926_;
    } else {
        let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1933_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
            v_inst_1924_,
            v_inst_1925_,
            v_inst_1926_,
            v_m_1927_,
            v_a_1928_,
        );
        return v___x_1933_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_get_x21___boxed(
    mut v_00_u03b1_1934_: *mut crate::leanh::LeanObject,
    mut v_inst_1935_: *mut crate::leanh::LeanObject,
    mut v_inst_1936_: *mut crate::leanh::LeanObject,
    mut v_inst_1937_: *mut crate::leanh::LeanObject,
    mut v_m_1938_: *mut crate::leanh::LeanObject,
    mut v_a_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Std_HashSet_Raw_get_x21(
        v_00_u03b1_1934_,
        v_inst_1935_,
        v_inst_1936_,
        v_inst_1937_,
        v_m_1938_,
        v_a_1939_,
    );
    crate::leanh::lean_dec_ref(v_m_1938_);
    crate::leanh::lean_dec(v_inst_1937_);
    return v_res_1940_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___redArg(
    mut v_m_1941_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    v_size_1942_ = crate::leanh::lean_ctor_get(v_m_1941_, 0);
    v___x_1943_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1944_ = lean_nat_dec_eq(v_size_1942_, v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___redArg___boxed(
    mut v_m_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1946_: u8 = 0;
    let mut v_r_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1946_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_1945_);
    crate::leanh::lean_dec_ref(v_m_1945_);
    v_r_1947_ = crate::leanh::lean_box((v_res_1946_) as usize);
    return v_r_1947_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty(
    mut v_00_u03b1_1948_: *mut crate::leanh::LeanObject,
    mut v_m_1949_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    v_size_1950_ = crate::leanh::lean_ctor_get(v_m_1949_, 0);
    v___x_1951_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1952_ = lean_nat_dec_eq(v_size_1950_, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___boxed(
    mut v_00_u03b1_1953_: *mut crate::leanh::LeanObject,
    mut v_m_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1955_: u8 = 0;
    let mut v_r_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_1953_, v_m_1954_);
    crate::leanh::lean_dec_ref(v_m_1954_);
    v_r_1956_ = crate::leanh::lean_box((v_res_1955_) as usize);
    return v_r_1956_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg___lam__0(
    mut v_a_1957_: *mut crate::leanh::LeanObject,
    mut v_b_1958_: *mut crate::leanh::LeanObject,
    mut v_d_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1960_, 0, v_a_1957_);
    crate::leanh::lean_ctor_set(v___x_1960_, 1, v_d_1959_);
    return v___x_1960_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg___lam__1(
    mut v___x_1961_: *mut crate::leanh::LeanObject,
    mut v___f_1962_: *mut crate::leanh::LeanObject,
    mut v_l_1963_: *mut crate::leanh::LeanObject,
    mut v_acc_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1961_,
        v___f_1962_,
        v_acc_1964_,
        v_l_1963_,
    );
    return v___x_1965_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg(
    mut v_m_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    v___x_1990_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_1991_ = crate::leanh::lean_ctor_get(v_m_1989_, 1);
    crate::leanh::lean_inc_ref(v_buckets_1991_);
    crate::leanh::lean_dec_ref(v_m_1989_);
    v___x_1992_ = crate::leanh::lean_box(0);
    v___x_1993_ = lean_array_get_size(v_buckets_1991_);
    v___x_1994_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1995_ = lean_nat_dec_lt(v___x_1994_, v___x_1993_);
    if v___x_1995_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_1991_);
        return v___x_1992_;
    } else {
        let mut v___f_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: usize = 0;
        let mut v___x_1998_: usize = 0;
        let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1996_ = l_Std_HashSet_Raw_toList___redArg___closed__11;
        v___x_1997_ = lean_usize_of_nat(v___x_1993_);
        v___x_1998_ = 0usize;
        v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1990_,
            v___f_1996_,
            v_buckets_1991_,
            v___x_1997_,
            v___x_1998_,
            v___x_1992_,
        );
        return v___x_1999_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_toList(
    mut v_00_u03b1_2000_: *mut crate::leanh::LeanObject,
    mut v_m_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    v___x_2002_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2003_ = crate::leanh::lean_ctor_get(v_m_2001_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2003_);
    crate::leanh::lean_dec_ref(v_m_2001_);
    v___x_2004_ = crate::leanh::lean_box(0);
    v___x_2005_ = lean_array_get_size(v_buckets_2003_);
    v___x_2006_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2007_ = lean_nat_dec_lt(v___x_2006_, v___x_2005_);
    if v___x_2007_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_2003_);
        return v___x_2004_;
    } else {
        let mut v___f_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: usize = 0;
        let mut v___x_2010_: usize = 0;
        let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2008_ = l_Std_HashSet_Raw_toList___redArg___closed__11;
        v___x_2009_ = lean_usize_of_nat(v___x_2005_);
        v___x_2010_ = 0usize;
        v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2002_,
            v___f_2008_,
            v_buckets_2003_,
            v___x_2009_,
            v___x_2010_,
            v___x_2004_,
        );
        return v___x_2011_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_ofList___redArg(
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_inst_2017_: *mut crate::leanh::LeanObject,
    mut v_l_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: u8 = 0;
    v___x_2019_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2020_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2020_ == 0 {
        crate::leanh::lean_dec(v_l_2018_);
        crate::leanh::lean_dec_ref(v_inst_2017_);
        crate::leanh::lean_dec_ref(v_inst_2016_);
        return v___x_2019_;
    } else {
        let mut v___f_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2021_ = l_Std_HashSet_Raw_ofList___redArg___closed__1;
        v___x_2022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_2021_,
            v_inst_2016_,
            v_inst_2017_,
            v___x_2019_,
            v_l_2018_,
        );
        return v___x_2022_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_ofList(
    mut v_00_u03b1_2023_: *mut crate::leanh::LeanObject,
    mut v_inst_2024_: *mut crate::leanh::LeanObject,
    mut v_inst_2025_: *mut crate::leanh::LeanObject,
    mut v_l_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    v___x_2027_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2028_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2028_ == 0 {
        crate::leanh::lean_dec(v_l_2026_);
        crate::leanh::lean_dec_ref(v_inst_2025_);
        crate::leanh::lean_dec_ref(v_inst_2024_);
        return v___x_2027_;
    } else {
        let mut v___f_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2029_ = l_Std_HashSet_Raw_ofList___redArg___closed__1;
        v___x_2030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_2029_,
            v_inst_2024_,
            v_inst_2025_,
            v___x_2027_,
            v_l_2026_,
        );
        return v___x_2030_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_foldM___redArg___lam__0(
    mut v_f_2031_: *mut crate::leanh::LeanObject,
    mut v_b_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
    mut v_x_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = crate::leanh::lean_apply_2(v_f_2031_, v_b_2032_, v_a_2033_);
    return v___x_2035_;
}
pub unsafe fn l_Std_HashSet_Raw_foldM___redArg___lam__1(
    mut v_inst_2036_: *mut crate::leanh::LeanObject,
    mut v___f_2037_: *mut crate::leanh::LeanObject,
    mut v_acc_2038_: *mut crate::leanh::LeanObject,
    mut v_l_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2040_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2036_,
        v___f_2037_,
        v_acc_2038_,
        v_l_2039_,
    );
    return v___x_2040_;
}
pub unsafe fn l_Std_HashSet_Raw_foldM___redArg(
    mut v_inst_2041_: *mut crate::leanh::LeanObject,
    mut v_f_2042_: *mut crate::leanh::LeanObject,
    mut v_init_2043_: *mut crate::leanh::LeanObject,
    mut v_b_2044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: u8 = 0;
    v_buckets_2045_ = crate::leanh::lean_ctor_get(v_b_2044_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2045_);
    crate::leanh::lean_dec_ref(v_b_2044_);
    v___x_2046_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2047_ = lean_array_get_size(v_buckets_2045_);
    v___x_2048_ = lean_nat_dec_lt(v___x_2046_, v___x_2047_);
    if v___x_2048_ == 0 {
        let mut v_toApplicative_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_2045_);
        crate::leanh::lean_dec(v_f_2042_);
        v_toApplicative_2049_ = crate::leanh::lean_ctor_get(v_inst_2041_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_2049_);
        crate::leanh::lean_dec_ref(v_inst_2041_);
        v_toPure_2050_ = crate::leanh::lean_ctor_get(v_toApplicative_2049_, 1);
        crate::leanh::lean_inc(v_toPure_2050_);
        crate::leanh::lean_dec_ref(v_toApplicative_2049_);
        v___x_2051_ =
            crate::leanh::lean_apply_2(v_toPure_2050_, crate::leanh::lean_box(0), v_init_2043_);
        return v___x_2051_;
    } else {
        let mut v___f_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: u8 = 0;
        v___f_2052_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2052_, 0, v_f_2042_);
        crate::leanh::lean_inc_ref(v_inst_2041_);
        v___f_2053_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2053_, 0, v_inst_2041_);
        crate::leanh::lean_closure_set(v___f_2053_, 1, v___f_2052_);
        v___x_2054_ = lean_nat_dec_le(v___x_2047_, v___x_2047_);
        if v___x_2054_ == 0 {
            if v___x_2048_ == 0 {
                let mut v_toApplicative_2055_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_2053_);
                crate::leanh::lean_dec_ref(v_buckets_2045_);
                v_toApplicative_2055_ = crate::leanh::lean_ctor_get(v_inst_2041_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_2055_);
                crate::leanh::lean_dec_ref(v_inst_2041_);
                v_toPure_2056_ = crate::leanh::lean_ctor_get(v_toApplicative_2055_, 1);
                crate::leanh::lean_inc(v_toPure_2056_);
                crate::leanh::lean_dec_ref(v_toApplicative_2055_);
                v___x_2057_ = crate::leanh::lean_apply_2(
                    v_toPure_2056_,
                    crate::leanh::lean_box(0),
                    v_init_2043_,
                );
                return v___x_2057_;
            } else {
                let mut v___x_2058_: usize = 0;
                let mut v___x_2059_: usize = 0;
                let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2058_ = 0usize;
                v___x_2059_ = lean_usize_of_nat(v___x_2047_);
                v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_2041_,
                    v___f_2053_,
                    v_buckets_2045_,
                    v___x_2058_,
                    v___x_2059_,
                    v_init_2043_,
                );
                return v___x_2060_;
            }
        } else {
            let mut v___x_2061_: usize = 0;
            let mut v___x_2062_: usize = 0;
            let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2061_ = 0usize;
            v___x_2062_ = lean_usize_of_nat(v___x_2047_);
            v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_2041_,
                v___f_2053_,
                v_buckets_2045_,
                v___x_2061_,
                v___x_2062_,
                v_init_2043_,
            );
            return v___x_2063_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_foldM(
    mut v_00_u03b1_2064_: *mut crate::leanh::LeanObject,
    mut v_m_2065_: *mut crate::leanh::LeanObject,
    mut v_inst_2066_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2067_: *mut crate::leanh::LeanObject,
    mut v_f_2068_: *mut crate::leanh::LeanObject,
    mut v_init_2069_: *mut crate::leanh::LeanObject,
    mut v_b_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    v_buckets_2071_ = crate::leanh::lean_ctor_get(v_b_2070_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2071_);
    crate::leanh::lean_dec_ref(v_b_2070_);
    v___x_2072_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2073_ = lean_array_get_size(v_buckets_2071_);
    v___x_2074_ = lean_nat_dec_lt(v___x_2072_, v___x_2073_);
    if v___x_2074_ == 0 {
        let mut v_toApplicative_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_2071_);
        crate::leanh::lean_dec(v_f_2068_);
        v_toApplicative_2075_ = crate::leanh::lean_ctor_get(v_inst_2066_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_2075_);
        crate::leanh::lean_dec_ref(v_inst_2066_);
        v_toPure_2076_ = crate::leanh::lean_ctor_get(v_toApplicative_2075_, 1);
        crate::leanh::lean_inc(v_toPure_2076_);
        crate::leanh::lean_dec_ref(v_toApplicative_2075_);
        v___x_2077_ =
            crate::leanh::lean_apply_2(v_toPure_2076_, crate::leanh::lean_box(0), v_init_2069_);
        return v___x_2077_;
    } else {
        let mut v___f_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: u8 = 0;
        v___f_2078_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2078_, 0, v_f_2068_);
        crate::leanh::lean_inc_ref(v_inst_2066_);
        v___f_2079_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2079_, 0, v_inst_2066_);
        crate::leanh::lean_closure_set(v___f_2079_, 1, v___f_2078_);
        v___x_2080_ = lean_nat_dec_le(v___x_2073_, v___x_2073_);
        if v___x_2080_ == 0 {
            if v___x_2074_ == 0 {
                let mut v_toApplicative_2081_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_2079_);
                crate::leanh::lean_dec_ref(v_buckets_2071_);
                v_toApplicative_2081_ = crate::leanh::lean_ctor_get(v_inst_2066_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_2081_);
                crate::leanh::lean_dec_ref(v_inst_2066_);
                v_toPure_2082_ = crate::leanh::lean_ctor_get(v_toApplicative_2081_, 1);
                crate::leanh::lean_inc(v_toPure_2082_);
                crate::leanh::lean_dec_ref(v_toApplicative_2081_);
                v___x_2083_ = crate::leanh::lean_apply_2(
                    v_toPure_2082_,
                    crate::leanh::lean_box(0),
                    v_init_2069_,
                );
                return v___x_2083_;
            } else {
                let mut v___x_2084_: usize = 0;
                let mut v___x_2085_: usize = 0;
                let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2084_ = 0usize;
                v___x_2085_ = lean_usize_of_nat(v___x_2073_);
                v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_2066_,
                    v___f_2079_,
                    v_buckets_2071_,
                    v___x_2084_,
                    v___x_2085_,
                    v_init_2069_,
                );
                return v___x_2086_;
            }
        } else {
            let mut v___x_2087_: usize = 0;
            let mut v___x_2088_: usize = 0;
            let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2087_ = 0usize;
            v___x_2088_ = lean_usize_of_nat(v___x_2073_);
            v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_2066_,
                v___f_2079_,
                v_buckets_2071_,
                v___x_2087_,
                v___x_2088_,
                v_init_2069_,
            );
            return v___x_2089_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_fold___redArg___lam__0(
    mut v_f_2090_: *mut crate::leanh::LeanObject,
    mut v_x1_2091_: *mut crate::leanh::LeanObject,
    mut v_x2_2092_: *mut crate::leanh::LeanObject,
    mut v_x3_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = crate::leanh::lean_apply_2(v_f_2090_, v_x1_2091_, v_x2_2092_);
    return v___x_2094_;
}
pub unsafe fn l_Std_HashSet_Raw_fold___redArg___lam__1(
    mut v___x_2095_: *mut crate::leanh::LeanObject,
    mut v___f_2096_: *mut crate::leanh::LeanObject,
    mut v_acc_2097_: *mut crate::leanh::LeanObject,
    mut v_l_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2099_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2095_,
        v___f_2096_,
        v_acc_2097_,
        v_l_2098_,
    );
    return v___x_2099_;
}
pub unsafe fn l_Std_HashSet_Raw_fold___redArg(
    mut v_f_2100_: *mut crate::leanh::LeanObject,
    mut v_init_2101_: *mut crate::leanh::LeanObject,
    mut v_m_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: u8 = 0;
    v___x_2103_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2104_ = crate::leanh::lean_ctor_get(v_m_2102_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2104_);
    crate::leanh::lean_dec_ref(v_m_2102_);
    v___x_2105_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2106_ = lean_array_get_size(v_buckets_2104_);
    v___x_2107_ = lean_nat_dec_lt(v___x_2105_, v___x_2106_);
    if v___x_2107_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_2104_);
        crate::leanh::lean_dec(v_f_2100_);
        return v_init_2101_;
    } else {
        let mut v___f_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: u8 = 0;
        v___f_2108_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2108_, 0, v_f_2100_);
        v___f_2109_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2109_, 0, v___x_2103_);
        crate::leanh::lean_closure_set(v___f_2109_, 1, v___f_2108_);
        v___x_2110_ = lean_nat_dec_le(v___x_2106_, v___x_2106_);
        if v___x_2110_ == 0 {
            if v___x_2107_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2109_);
                crate::leanh::lean_dec_ref(v_buckets_2104_);
                return v_init_2101_;
            } else {
                let mut v___x_2111_: usize = 0;
                let mut v___x_2112_: usize = 0;
                let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2111_ = 0usize;
                v___x_2112_ = lean_usize_of_nat(v___x_2106_);
                v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2103_,
                    v___f_2109_,
                    v_buckets_2104_,
                    v___x_2111_,
                    v___x_2112_,
                    v_init_2101_,
                );
                return v___x_2113_;
            }
        } else {
            let mut v___x_2114_: usize = 0;
            let mut v___x_2115_: usize = 0;
            let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2114_ = 0usize;
            v___x_2115_ = lean_usize_of_nat(v___x_2106_);
            v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2103_,
                v___f_2109_,
                v_buckets_2104_,
                v___x_2114_,
                v___x_2115_,
                v_init_2101_,
            );
            return v___x_2116_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_fold(
    mut v_00_u03b1_2117_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2118_: *mut crate::leanh::LeanObject,
    mut v_f_2119_: *mut crate::leanh::LeanObject,
    mut v_init_2120_: *mut crate::leanh::LeanObject,
    mut v_m_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    v___x_2122_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2123_ = crate::leanh::lean_ctor_get(v_m_2121_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2123_);
    crate::leanh::lean_dec_ref(v_m_2121_);
    v___x_2124_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2125_ = lean_array_get_size(v_buckets_2123_);
    v___x_2126_ = lean_nat_dec_lt(v___x_2124_, v___x_2125_);
    if v___x_2126_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_2123_);
        crate::leanh::lean_dec(v_f_2119_);
        return v_init_2120_;
    } else {
        let mut v___f_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2129_: u8 = 0;
        v___f_2127_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2127_, 0, v_f_2119_);
        v___f_2128_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2128_, 0, v___x_2122_);
        crate::leanh::lean_closure_set(v___f_2128_, 1, v___f_2127_);
        v___x_2129_ = lean_nat_dec_le(v___x_2125_, v___x_2125_);
        if v___x_2129_ == 0 {
            if v___x_2126_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2128_);
                crate::leanh::lean_dec_ref(v_buckets_2123_);
                return v_init_2120_;
            } else {
                let mut v___x_2130_: usize = 0;
                let mut v___x_2131_: usize = 0;
                let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2130_ = 0usize;
                v___x_2131_ = lean_usize_of_nat(v___x_2125_);
                v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2122_,
                    v___f_2128_,
                    v_buckets_2123_,
                    v___x_2130_,
                    v___x_2131_,
                    v_init_2120_,
                );
                return v___x_2132_;
            }
        } else {
            let mut v___x_2133_: usize = 0;
            let mut v___x_2134_: usize = 0;
            let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2133_ = 0usize;
            v___x_2134_ = lean_usize_of_nat(v___x_2125_);
            v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2122_,
                v___f_2128_,
                v_buckets_2123_,
                v___x_2133_,
                v___x_2134_,
                v_init_2120_,
            );
            return v___x_2135_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_forM___redArg___lam__0(
    mut v_f_2136_: *mut crate::leanh::LeanObject,
    mut v_x_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = crate::leanh::lean_apply_1(v_f_2136_, v___y_2138_);
    return v___x_2140_;
}
pub unsafe fn l_Std_HashSet_Raw_forM___redArg___lam__1(
    mut v_inst_2141_: *mut crate::leanh::LeanObject,
    mut v___f_2142_: *mut crate::leanh::LeanObject,
    mut v_x_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2145_ = crate::leanh::lean_box(0);
    v___x_2146_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2141_,
        v___f_2142_,
        v___x_2145_,
        v___y_2144_,
    );
    return v___x_2146_;
}
pub unsafe fn l_Std_HashSet_Raw_forM___redArg(
    mut v_inst_2147_: *mut crate::leanh::LeanObject,
    mut v_f_2148_: *mut crate::leanh::LeanObject,
    mut v_b_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    v_buckets_2150_ = crate::leanh::lean_ctor_get(v_b_2149_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2150_);
    crate::leanh::lean_dec_ref(v_b_2149_);
    v___x_2151_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2152_ = lean_array_get_size(v_buckets_2150_);
    v___x_2153_ = crate::leanh::lean_box(0);
    v___x_2154_ = lean_nat_dec_lt(v___x_2151_, v___x_2152_);
    if v___x_2154_ == 0 {
        let mut v_toApplicative_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_2150_);
        crate::leanh::lean_dec(v_f_2148_);
        v_toApplicative_2155_ = crate::leanh::lean_ctor_get(v_inst_2147_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_2155_);
        crate::leanh::lean_dec_ref(v_inst_2147_);
        v_toPure_2156_ = crate::leanh::lean_ctor_get(v_toApplicative_2155_, 1);
        crate::leanh::lean_inc(v_toPure_2156_);
        crate::leanh::lean_dec_ref(v_toApplicative_2155_);
        v___x_2157_ =
            crate::leanh::lean_apply_2(v_toPure_2156_, crate::leanh::lean_box(0), v___x_2153_);
        return v___x_2157_;
    } else {
        let mut v___f_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: u8 = 0;
        v___f_2158_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2158_, 0, v_f_2148_);
        crate::leanh::lean_inc_ref(v_inst_2147_);
        v___f_2159_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2159_, 0, v_inst_2147_);
        crate::leanh::lean_closure_set(v___f_2159_, 1, v___f_2158_);
        v___x_2160_ = lean_nat_dec_le(v___x_2152_, v___x_2152_);
        if v___x_2160_ == 0 {
            if v___x_2154_ == 0 {
                let mut v_toApplicative_2161_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_2159_);
                crate::leanh::lean_dec_ref(v_buckets_2150_);
                v_toApplicative_2161_ = crate::leanh::lean_ctor_get(v_inst_2147_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_2161_);
                crate::leanh::lean_dec_ref(v_inst_2147_);
                v_toPure_2162_ = crate::leanh::lean_ctor_get(v_toApplicative_2161_, 1);
                crate::leanh::lean_inc(v_toPure_2162_);
                crate::leanh::lean_dec_ref(v_toApplicative_2161_);
                v___x_2163_ = crate::leanh::lean_apply_2(
                    v_toPure_2162_,
                    crate::leanh::lean_box(0),
                    v___x_2153_,
                );
                return v___x_2163_;
            } else {
                let mut v___x_2164_: usize = 0;
                let mut v___x_2165_: usize = 0;
                let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2164_ = 0usize;
                v___x_2165_ = lean_usize_of_nat(v___x_2152_);
                v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_2147_,
                    v___f_2159_,
                    v_buckets_2150_,
                    v___x_2164_,
                    v___x_2165_,
                    v___x_2153_,
                );
                return v___x_2166_;
            }
        } else {
            let mut v___x_2167_: usize = 0;
            let mut v___x_2168_: usize = 0;
            let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2167_ = 0usize;
            v___x_2168_ = lean_usize_of_nat(v___x_2152_);
            v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_2147_,
                v___f_2159_,
                v_buckets_2150_,
                v___x_2167_,
                v___x_2168_,
                v___x_2153_,
            );
            return v___x_2169_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_forM(
    mut v_00_u03b1_2170_: *mut crate::leanh::LeanObject,
    mut v_m_2171_: *mut crate::leanh::LeanObject,
    mut v_inst_2172_: *mut crate::leanh::LeanObject,
    mut v_f_2173_: *mut crate::leanh::LeanObject,
    mut v_b_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    v_buckets_2175_ = crate::leanh::lean_ctor_get(v_b_2174_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2175_);
    crate::leanh::lean_dec_ref(v_b_2174_);
    v___x_2176_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2177_ = lean_array_get_size(v_buckets_2175_);
    v___x_2178_ = crate::leanh::lean_box(0);
    v___x_2179_ = lean_nat_dec_lt(v___x_2176_, v___x_2177_);
    if v___x_2179_ == 0 {
        let mut v_toApplicative_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_2175_);
        crate::leanh::lean_dec(v_f_2173_);
        v_toApplicative_2180_ = crate::leanh::lean_ctor_get(v_inst_2172_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_2180_);
        crate::leanh::lean_dec_ref(v_inst_2172_);
        v_toPure_2181_ = crate::leanh::lean_ctor_get(v_toApplicative_2180_, 1);
        crate::leanh::lean_inc(v_toPure_2181_);
        crate::leanh::lean_dec_ref(v_toApplicative_2180_);
        v___x_2182_ =
            crate::leanh::lean_apply_2(v_toPure_2181_, crate::leanh::lean_box(0), v___x_2178_);
        return v___x_2182_;
    } else {
        let mut v___f_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: u8 = 0;
        v___f_2183_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2183_, 0, v_f_2173_);
        crate::leanh::lean_inc_ref(v_inst_2172_);
        v___f_2184_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2184_, 0, v_inst_2172_);
        crate::leanh::lean_closure_set(v___f_2184_, 1, v___f_2183_);
        v___x_2185_ = lean_nat_dec_le(v___x_2177_, v___x_2177_);
        if v___x_2185_ == 0 {
            if v___x_2179_ == 0 {
                let mut v_toApplicative_2186_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_2184_);
                crate::leanh::lean_dec_ref(v_buckets_2175_);
                v_toApplicative_2186_ = crate::leanh::lean_ctor_get(v_inst_2172_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_2186_);
                crate::leanh::lean_dec_ref(v_inst_2172_);
                v_toPure_2187_ = crate::leanh::lean_ctor_get(v_toApplicative_2186_, 1);
                crate::leanh::lean_inc(v_toPure_2187_);
                crate::leanh::lean_dec_ref(v_toApplicative_2186_);
                v___x_2188_ = crate::leanh::lean_apply_2(
                    v_toPure_2187_,
                    crate::leanh::lean_box(0),
                    v___x_2178_,
                );
                return v___x_2188_;
            } else {
                let mut v___x_2189_: usize = 0;
                let mut v___x_2190_: usize = 0;
                let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2189_ = 0usize;
                v___x_2190_ = lean_usize_of_nat(v___x_2177_);
                v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_2172_,
                    v___f_2184_,
                    v_buckets_2175_,
                    v___x_2189_,
                    v___x_2190_,
                    v___x_2178_,
                );
                return v___x_2191_;
            }
        } else {
            let mut v___x_2192_: usize = 0;
            let mut v___x_2193_: usize = 0;
            let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2192_ = 0usize;
            v___x_2193_ = lean_usize_of_nat(v___x_2177_);
            v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_2172_,
                v___f_2184_,
                v_buckets_2175_,
                v___x_2192_,
                v___x_2193_,
                v___x_2178_,
            );
            return v___x_2194_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_forIn___redArg___lam__0(
    mut v_f_2195_: *mut crate::leanh::LeanObject,
    mut v_a_2196_: *mut crate::leanh::LeanObject,
    mut v_x_2197_: *mut crate::leanh::LeanObject,
    mut v_acc_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = crate::leanh::lean_apply_2(v_f_2195_, v_a_2196_, v_acc_2198_);
    return v___x_2199_;
}
pub unsafe fn l_Std_HashSet_Raw_forIn___redArg___lam__1(
    mut v_inst_2200_: *mut crate::leanh::LeanObject,
    mut v___f_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_x_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_2200_, v___f_2201_, v_a_2202_, v___y_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Std_HashSet_Raw_forIn___redArg(
    mut v_inst_2206_: *mut crate::leanh::LeanObject,
    mut v_f_2207_: *mut crate::leanh::LeanObject,
    mut v_init_2208_: *mut crate::leanh::LeanObject,
    mut v_b_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2210_ = crate::leanh::lean_ctor_get(v_b_2209_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2210_);
    crate::leanh::lean_dec_ref(v_b_2209_);
    v___f_2211_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2211_, 0, v_f_2207_);
    crate::leanh::lean_inc_ref(v_inst_2206_);
    v___f_2212_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2212_, 0, v_inst_2206_);
    crate::leanh::lean_closure_set(v___f_2212_, 1, v___f_2211_);
    v_sz_2213_ = lean_array_size(v_buckets_2210_);
    v___x_2214_ = 0usize;
    v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2206_,
        v_buckets_2210_,
        v___f_2212_,
        v_sz_2213_,
        v___x_2214_,
        v_init_2208_,
    );
    return v___x_2215_;
}
pub unsafe fn l_Std_HashSet_Raw_forIn(
    mut v_00_u03b1_2216_: *mut crate::leanh::LeanObject,
    mut v_m_2217_: *mut crate::leanh::LeanObject,
    mut v_inst_2218_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2219_: *mut crate::leanh::LeanObject,
    mut v_f_2220_: *mut crate::leanh::LeanObject,
    mut v_init_2221_: *mut crate::leanh::LeanObject,
    mut v_b_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2226_: usize = 0;
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2223_ = crate::leanh::lean_ctor_get(v_b_2222_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2223_);
    crate::leanh::lean_dec_ref(v_b_2222_);
    v___f_2224_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2224_, 0, v_f_2220_);
    crate::leanh::lean_inc_ref(v_inst_2218_);
    v___f_2225_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2225_, 0, v_inst_2218_);
    crate::leanh::lean_closure_set(v___f_2225_, 1, v___f_2224_);
    v_sz_2226_ = lean_array_size(v_buckets_2223_);
    v___x_2227_ = 0usize;
    v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2218_,
        v_buckets_2223_,
        v___f_2225_,
        v_sz_2226_,
        v___x_2227_,
        v_init_2221_,
    );
    return v___x_2228_;
}
pub unsafe fn l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(
    mut v_inst_2229_: *mut crate::leanh::LeanObject,
    mut v_m_2230_: *mut crate::leanh::LeanObject,
    mut v_f_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    v_buckets_2232_ = crate::leanh::lean_ctor_get(v_m_2230_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2232_);
    crate::leanh::lean_dec_ref(v_m_2230_);
    v___x_2233_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2234_ = lean_array_get_size(v_buckets_2232_);
    v___x_2235_ = crate::leanh::lean_box(0);
    v___x_2236_ = lean_nat_dec_lt(v___x_2233_, v___x_2234_);
    if v___x_2236_ == 0 {
        let mut v_toApplicative_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_2232_);
        crate::leanh::lean_dec(v_f_2231_);
        v_toApplicative_2237_ = crate::leanh::lean_ctor_get(v_inst_2229_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_2237_);
        crate::leanh::lean_dec_ref(v_inst_2229_);
        v_toPure_2238_ = crate::leanh::lean_ctor_get(v_toApplicative_2237_, 1);
        crate::leanh::lean_inc(v_toPure_2238_);
        crate::leanh::lean_dec_ref(v_toApplicative_2237_);
        v___x_2239_ =
            crate::leanh::lean_apply_2(v_toPure_2238_, crate::leanh::lean_box(0), v___x_2235_);
        return v___x_2239_;
    } else {
        let mut v___f_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: u8 = 0;
        v___f_2240_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2240_, 0, v_f_2231_);
        crate::leanh::lean_inc_ref(v_inst_2229_);
        v___f_2241_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2241_, 0, v_inst_2229_);
        crate::leanh::lean_closure_set(v___f_2241_, 1, v___f_2240_);
        v___x_2242_ = lean_nat_dec_le(v___x_2234_, v___x_2234_);
        if v___x_2242_ == 0 {
            if v___x_2236_ == 0 {
                let mut v_toApplicative_2243_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_2241_);
                crate::leanh::lean_dec_ref(v_buckets_2232_);
                v_toApplicative_2243_ = crate::leanh::lean_ctor_get(v_inst_2229_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_2243_);
                crate::leanh::lean_dec_ref(v_inst_2229_);
                v_toPure_2244_ = crate::leanh::lean_ctor_get(v_toApplicative_2243_, 1);
                crate::leanh::lean_inc(v_toPure_2244_);
                crate::leanh::lean_dec_ref(v_toApplicative_2243_);
                v___x_2245_ = crate::leanh::lean_apply_2(
                    v_toPure_2244_,
                    crate::leanh::lean_box(0),
                    v___x_2235_,
                );
                return v___x_2245_;
            } else {
                let mut v___x_2246_: usize = 0;
                let mut v___x_2247_: usize = 0;
                let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2246_ = 0usize;
                v___x_2247_ = lean_usize_of_nat(v___x_2234_);
                v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_2229_,
                    v___f_2241_,
                    v_buckets_2232_,
                    v___x_2246_,
                    v___x_2247_,
                    v___x_2235_,
                );
                return v___x_2248_;
            }
        } else {
            let mut v___x_2249_: usize = 0;
            let mut v___x_2250_: usize = 0;
            let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2249_ = 0usize;
            v___x_2250_ = lean_usize_of_nat(v___x_2234_);
            v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_2229_,
                v___f_2241_,
                v_buckets_2232_,
                v___x_2249_,
                v___x_2250_,
                v___x_2235_,
            );
            return v___x_2251_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_instForMOfMonad___redArg(
    mut v_inst_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2253_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2253_, 0, v_inst_2252_);
    return v___f_2253_;
}
pub unsafe fn l_Std_HashSet_Raw_instForMOfMonad(
    mut v_00_u03b1_2254_: *mut crate::leanh::LeanObject,
    mut v_m_2255_: *mut crate::leanh::LeanObject,
    mut v_inst_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2257_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2257_, 0, v_inst_2256_);
    return v___f_2257_;
}
pub unsafe fn l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(
    mut v_inst_2258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2259_: *mut crate::leanh::LeanObject,
    mut v_m_2260_: *mut crate::leanh::LeanObject,
    mut v_init_2261_: *mut crate::leanh::LeanObject,
    mut v_f_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2266_: usize = 0;
    let mut v___x_2267_: usize = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2263_ = crate::leanh::lean_ctor_get(v_m_2260_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2263_);
    crate::leanh::lean_dec_ref(v_m_2260_);
    v___f_2264_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2264_, 0, v_f_2262_);
    crate::leanh::lean_inc_ref(v_inst_2258_);
    v___f_2265_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2265_, 0, v_inst_2258_);
    crate::leanh::lean_closure_set(v___f_2265_, 1, v___f_2264_);
    v_sz_2266_ = lean_array_size(v_buckets_2263_);
    v___x_2267_ = 0usize;
    v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2258_,
        v_buckets_2263_,
        v___f_2265_,
        v_sz_2266_,
        v___x_2267_,
        v_init_2261_,
    );
    return v___x_2268_;
}
pub unsafe fn l_Std_HashSet_Raw_instForInOfMonad___redArg(
    mut v_inst_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2270_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2270_, 0, v_inst_2269_);
    return v___f_2270_;
}
pub unsafe fn l_Std_HashSet_Raw_instForInOfMonad(
    mut v_00_u03b1_2271_: *mut crate::leanh::LeanObject,
    mut v_m_2272_: *mut crate::leanh::LeanObject,
    mut v_inst_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2274_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2274_, 0, v_inst_2273_);
    return v___f_2274_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg___lam__0(
    mut v_f_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
    mut v_x_2277_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: u8 = 0;
    v___x_2278_ = crate::leanh::lean_apply_1(v_f_2275_, v_a_2276_);
    v___x_2279_ = (crate::leanh::lean_unbox(v___x_2278_) as u8);
    return v___x_2279_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(
    mut v_f_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_x_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2283_: u8 = 0;
    let mut v_r_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_2280_, v_a_2281_, v_x_2282_);
    v_r_2284_ = crate::leanh::lean_box((v_res_2283_) as usize);
    return v_r_2284_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg(
    mut v_f_2285_: *mut crate::leanh::LeanObject,
    mut v_m_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    v_buckets_2287_ = crate::leanh::lean_ctor_get(v_m_2286_, 1);
    v___x_2288_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2289_ = lean_array_get_size(v_buckets_2287_);
    v___x_2290_ = lean_nat_dec_lt(v___x_2288_, v___x_2289_);
    if v___x_2290_ == 0 {
        let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_2286_);
        crate::leanh::lean_dec_ref(v_f_2285_);
        v___x_2291_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
        );
        return v___x_2291_;
    } else {
        let mut v___f_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2292_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2292_, 0, v_f_2285_);
        v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2292_, v_m_2286_);
        return v___x_2293_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_filter(
    mut v_00_u03b1_2294_: *mut crate::leanh::LeanObject,
    mut v_inst_2295_: *mut crate::leanh::LeanObject,
    mut v_inst_2296_: *mut crate::leanh::LeanObject,
    mut v_f_2297_: *mut crate::leanh::LeanObject,
    mut v_m_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    v_buckets_2299_ = crate::leanh::lean_ctor_get(v_m_2298_, 1);
    v___x_2300_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2301_ = lean_array_get_size(v_buckets_2299_);
    v___x_2302_ = lean_nat_dec_lt(v___x_2300_, v___x_2301_);
    if v___x_2302_ == 0 {
        let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_2298_);
        crate::leanh::lean_dec_ref(v_f_2297_);
        v___x_2303_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
        );
        return v___x_2303_;
    } else {
        let mut v___f_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2304_ = crate::leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2304_, 0, v_f_2297_);
        v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2304_, v_m_2298_);
        return v___x_2305_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_filter___boxed(
    mut v_00_u03b1_2306_: *mut crate::leanh::LeanObject,
    mut v_inst_2307_: *mut crate::leanh::LeanObject,
    mut v_inst_2308_: *mut crate::leanh::LeanObject,
    mut v_f_2309_: *mut crate::leanh::LeanObject,
    mut v_m_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2311_ = l_Std_HashSet_Raw_filter(
        v_00_u03b1_2306_,
        v_inst_2307_,
        v_inst_2308_,
        v_f_2309_,
        v_m_2310_,
    );
    crate::leanh::lean_dec_ref(v_inst_2308_);
    crate::leanh::lean_dec_ref(v_inst_2307_);
    return v_res_2311_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg___lam__0(
    mut v_x1_2312_: *mut crate::leanh::LeanObject,
    mut v_x2_2313_: *mut crate::leanh::LeanObject,
    mut v_x3_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = lean_array_push(v_x1_2312_, v_x2_2313_);
    return v___x_2315_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg___lam__1(
    mut v___x_2316_: *mut crate::leanh::LeanObject,
    mut v___f_2317_: *mut crate::leanh::LeanObject,
    mut v_acc_2318_: *mut crate::leanh::LeanObject,
    mut v_l_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2316_,
        v___f_2317_,
        v_acc_2318_,
        v_l_2319_,
    );
    return v___x_2320_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg(
    mut v_m_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    v_size_2326_ = crate::leanh::lean_ctor_get(v_m_2325_, 0);
    crate::leanh::lean_inc(v_size_2326_);
    v_buckets_2327_ = crate::leanh::lean_ctor_get(v_m_2325_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2327_);
    crate::leanh::lean_dec_ref(v_m_2325_);
    v___x_2328_ = lean_mk_empty_array_with_capacity(v_size_2326_);
    crate::leanh::lean_dec(v_size_2326_);
    v___x_2329_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v___x_2330_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2331_ = lean_array_get_size(v_buckets_2327_);
    v___x_2332_ = lean_nat_dec_lt(v___x_2330_, v___x_2331_);
    if v___x_2332_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_2327_);
        return v___x_2328_;
    } else {
        let mut v___f_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        v___f_2333_ = l_Std_HashSet_Raw_toArray___redArg___closed__1;
        v___x_2334_ = lean_nat_dec_le(v___x_2331_, v___x_2331_);
        if v___x_2334_ == 0 {
            if v___x_2332_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_2327_);
                return v___x_2328_;
            } else {
                let mut v___x_2335_: usize = 0;
                let mut v___x_2336_: usize = 0;
                let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2335_ = 0usize;
                v___x_2336_ = lean_usize_of_nat(v___x_2331_);
                v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2329_,
                    v___f_2333_,
                    v_buckets_2327_,
                    v___x_2335_,
                    v___x_2336_,
                    v___x_2328_,
                );
                return v___x_2337_;
            }
        } else {
            let mut v___x_2338_: usize = 0;
            let mut v___x_2339_: usize = 0;
            let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2338_ = 0usize;
            v___x_2339_ = lean_usize_of_nat(v___x_2331_);
            v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2329_,
                v___f_2333_,
                v_buckets_2327_,
                v___x_2338_,
                v___x_2339_,
                v___x_2328_,
            );
            return v___x_2340_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_toArray(
    mut v_00_u03b1_2341_: *mut crate::leanh::LeanObject,
    mut v_m_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: u8 = 0;
    v_size_2343_ = crate::leanh::lean_ctor_get(v_m_2342_, 0);
    crate::leanh::lean_inc(v_size_2343_);
    v_buckets_2344_ = crate::leanh::lean_ctor_get(v_m_2342_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2344_);
    crate::leanh::lean_dec_ref(v_m_2342_);
    v___x_2345_ = lean_mk_empty_array_with_capacity(v_size_2343_);
    crate::leanh::lean_dec(v_size_2343_);
    v___x_2346_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v___x_2347_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2348_ = lean_array_get_size(v_buckets_2344_);
    v___x_2349_ = lean_nat_dec_lt(v___x_2347_, v___x_2348_);
    if v___x_2349_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_2344_);
        return v___x_2345_;
    } else {
        let mut v___f_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: u8 = 0;
        v___f_2350_ = l_Std_HashSet_Raw_toArray___redArg___closed__1;
        v___x_2351_ = lean_nat_dec_le(v___x_2348_, v___x_2348_);
        if v___x_2351_ == 0 {
            if v___x_2349_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_2344_);
                return v___x_2345_;
            } else {
                let mut v___x_2352_: usize = 0;
                let mut v___x_2353_: usize = 0;
                let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2352_ = 0usize;
                v___x_2353_ = lean_usize_of_nat(v___x_2348_);
                v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2346_,
                    v___f_2350_,
                    v_buckets_2344_,
                    v___x_2352_,
                    v___x_2353_,
                    v___x_2345_,
                );
                return v___x_2354_;
            }
        } else {
            let mut v___x_2355_: usize = 0;
            let mut v___x_2356_: usize = 0;
            let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2355_ = 0usize;
            v___x_2356_ = lean_usize_of_nat(v___x_2348_);
            v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2346_,
                v___f_2350_,
                v_buckets_2344_,
                v___x_2355_,
                v___x_2356_,
                v___x_2345_,
            );
            return v___x_2357_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_union___redArg___lam__0(
    mut v_inst_2358_: *mut crate::leanh::LeanObject,
    mut v_inst_2359_: *mut crate::leanh::LeanObject,
    mut v_a_2360_: *mut crate::leanh::LeanObject,
    mut v_b_2361_: *mut crate::leanh::LeanObject,
    mut v_acc_2362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_2363_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_2358_,
        v_inst_2359_,
        v_acc_2362_,
        v_a_2360_,
        v_b_2361_,
    );
    v___x_2364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2364_, 0, v_r_2363_);
    return v___x_2364_;
}
pub unsafe fn l_Std_HashSet_Raw_union___redArg___lam__1(
    mut v___x_2365_: *mut crate::leanh::LeanObject,
    mut v___f_2366_: *mut crate::leanh::LeanObject,
    mut v_a_2367_: *mut crate::leanh::LeanObject,
    mut v_x_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_2365_, v___f_2366_, v_a_2367_, v___y_2369_);
    return v___x_2370_;
}
pub unsafe fn l_Std_HashSet_Raw_union___redArg(
    mut v_inst_2373_: *mut crate::leanh::LeanObject,
    mut v_inst_2374_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2375_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    v_size_2377_ = crate::leanh::lean_ctor_get(v_m_u2081_2375_, 0);
    v_buckets_2378_ = crate::leanh::lean_ctor_get(v_m_u2081_2375_, 1);
    v___x_2379_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2380_ = lean_array_get_size(v_buckets_2378_);
    v___x_2381_ = lean_nat_dec_lt(v___x_2379_, v___x_2380_);
    if v___x_2381_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_2375_);
        crate::leanh::lean_dec_ref(v_inst_2374_);
        crate::leanh::lean_dec_ref(v_inst_2373_);
        return v_m_u2082_2376_;
    } else {
        let mut v_size_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: u8 = 0;
        v_size_2382_ = crate::leanh::lean_ctor_get(v_m_u2082_2376_, 0);
        v_buckets_2383_ = crate::leanh::lean_ctor_get(v_m_u2082_2376_, 1);
        v___x_2384_ = lean_array_get_size(v_buckets_2383_);
        v___x_2385_ = lean_nat_dec_lt(v___x_2379_, v___x_2384_);
        if v___x_2385_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_2376_);
            crate::leanh::lean_dec_ref(v_inst_2374_);
            crate::leanh::lean_dec_ref(v_inst_2373_);
            return v_m_u2081_2375_;
        } else {
            let mut v___x_2386_: u8 = 0;
            v___x_2386_ = lean_nat_dec_le(v_size_2377_, v_size_2382_);
            if v___x_2386_ == 0 {
                let mut v___f_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_2387_ = l_Std_HashSet_Raw_union___redArg___closed__0;
                v___x_2388_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
                    v___f_2387_,
                    v_inst_2373_,
                    v_inst_2374_,
                    v_m_u2081_2375_,
                    v_m_u2082_2376_,
                );
                return v___x_2388_;
            } else {
                let mut v___f_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_2392_: usize = 0;
                let mut v___x_2393_: usize = 0;
                let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_buckets_2378_);
                crate::leanh::lean_dec_ref(v_m_u2081_2375_);
                v___f_2389_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2389_, 0, v_inst_2373_);
                crate::leanh::lean_closure_set(v___f_2389_, 1, v_inst_2374_);
                v___x_2390_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v___f_2391_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2391_, 0, v___x_2390_);
                crate::leanh::lean_closure_set(v___f_2391_, 1, v___f_2389_);
                v_sz_2392_ = lean_array_size(v_buckets_2378_);
                v___x_2393_ = 0usize;
                v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2390_,
                    v_buckets_2378_,
                    v___f_2391_,
                    v_sz_2392_,
                    v___x_2393_,
                    v_m_u2082_2376_,
                );
                return v___x_2394_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_union(
    mut v_00_u03b1_2395_: *mut crate::leanh::LeanObject,
    mut v_inst_2396_: *mut crate::leanh::LeanObject,
    mut v_inst_2397_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2398_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: u8 = 0;
    v_size_2400_ = crate::leanh::lean_ctor_get(v_m_u2081_2398_, 0);
    v_buckets_2401_ = crate::leanh::lean_ctor_get(v_m_u2081_2398_, 1);
    v___x_2402_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2403_ = lean_array_get_size(v_buckets_2401_);
    v___x_2404_ = lean_nat_dec_lt(v___x_2402_, v___x_2403_);
    if v___x_2404_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_2398_);
        crate::leanh::lean_dec_ref(v_inst_2397_);
        crate::leanh::lean_dec_ref(v_inst_2396_);
        return v_m_u2082_2399_;
    } else {
        let mut v_size_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: u8 = 0;
        v_size_2405_ = crate::leanh::lean_ctor_get(v_m_u2082_2399_, 0);
        v_buckets_2406_ = crate::leanh::lean_ctor_get(v_m_u2082_2399_, 1);
        v___x_2407_ = lean_array_get_size(v_buckets_2406_);
        v___x_2408_ = lean_nat_dec_lt(v___x_2402_, v___x_2407_);
        if v___x_2408_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_2399_);
            crate::leanh::lean_dec_ref(v_inst_2397_);
            crate::leanh::lean_dec_ref(v_inst_2396_);
            return v_m_u2081_2398_;
        } else {
            let mut v___x_2409_: u8 = 0;
            v___x_2409_ = lean_nat_dec_le(v_size_2400_, v_size_2405_);
            if v___x_2409_ == 0 {
                let mut v___f_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_2410_ = l_Std_HashSet_Raw_union___redArg___closed__0;
                v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
                    v___f_2410_,
                    v_inst_2396_,
                    v_inst_2397_,
                    v_m_u2081_2398_,
                    v_m_u2082_2399_,
                );
                return v___x_2411_;
            } else {
                let mut v___f_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_2415_: usize = 0;
                let mut v___x_2416_: usize = 0;
                let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_buckets_2401_);
                crate::leanh::lean_dec_ref(v_m_u2081_2398_);
                v___f_2412_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2412_, 0, v_inst_2396_);
                crate::leanh::lean_closure_set(v___f_2412_, 1, v_inst_2397_);
                v___x_2413_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v___f_2414_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2414_, 0, v___x_2413_);
                crate::leanh::lean_closure_set(v___f_2414_, 1, v___f_2412_);
                v_sz_2415_ = lean_array_size(v_buckets_2401_);
                v___x_2416_ = 0usize;
                v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2413_,
                    v_buckets_2401_,
                    v___f_2414_,
                    v_sz_2415_,
                    v___x_2416_,
                    v_m_u2082_2399_,
                );
                return v___x_2417_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(
    mut v_inst_2418_: *mut crate::leanh::LeanObject,
    mut v_inst_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ =
        crate::leanh::lean_alloc_closure(l_Std_HashSet_Raw_union as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2420_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2420_, 1, v_inst_2418_);
    crate::leanh::lean_closure_set(v___x_2420_, 2, v_inst_2419_);
    return v___x_2420_;
}
pub unsafe fn l_Std_HashSet_Raw_instUnionOfBEqOfHashable(
    mut v_00_u03b1_2421_: *mut crate::leanh::LeanObject,
    mut v_inst_2422_: *mut crate::leanh::LeanObject,
    mut v_inst_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ =
        crate::leanh::lean_alloc_closure(l_Std_HashSet_Raw_union as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2424_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2424_, 1, v_inst_2422_);
    crate::leanh::lean_closure_set(v___x_2424_, 2, v_inst_2423_);
    return v___x_2424_;
}
pub unsafe fn l_Std_HashSet_Raw_inter___redArg(
    mut v_inst_2425_: *mut crate::leanh::LeanObject,
    mut v_inst_2426_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2427_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    v_buckets_2429_ = crate::leanh::lean_ctor_get(v_m_u2081_2427_, 1);
    v___x_2430_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2431_ = lean_array_get_size(v_buckets_2429_);
    v___x_2432_ = lean_nat_dec_lt(v___x_2430_, v___x_2431_);
    if v___x_2432_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_2427_);
        crate::leanh::lean_dec_ref(v_inst_2426_);
        crate::leanh::lean_dec_ref(v_inst_2425_);
        return v_m_u2082_2428_;
    } else {
        let mut v_buckets_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2435_: u8 = 0;
        v_buckets_2433_ = crate::leanh::lean_ctor_get(v_m_u2082_2428_, 1);
        v___x_2434_ = lean_array_get_size(v_buckets_2433_);
        v___x_2435_ = lean_nat_dec_lt(v___x_2430_, v___x_2434_);
        if v___x_2435_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_2428_);
            crate::leanh::lean_dec_ref(v_inst_2426_);
            crate::leanh::lean_dec_ref(v_inst_2425_);
            return v_m_u2081_2427_;
        } else {
            let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2436_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
                v_inst_2425_,
                v_inst_2426_,
                v_m_u2081_2427_,
                v_m_u2082_2428_,
            );
            return v___x_2436_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_inter(
    mut v_00_u03b1_2437_: *mut crate::leanh::LeanObject,
    mut v_inst_2438_: *mut crate::leanh::LeanObject,
    mut v_inst_2439_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2440_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    v_buckets_2442_ = crate::leanh::lean_ctor_get(v_m_u2081_2440_, 1);
    v___x_2443_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2444_ = lean_array_get_size(v_buckets_2442_);
    v___x_2445_ = lean_nat_dec_lt(v___x_2443_, v___x_2444_);
    if v___x_2445_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_2440_);
        crate::leanh::lean_dec_ref(v_inst_2439_);
        crate::leanh::lean_dec_ref(v_inst_2438_);
        return v_m_u2082_2441_;
    } else {
        let mut v_buckets_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2448_: u8 = 0;
        v_buckets_2446_ = crate::leanh::lean_ctor_get(v_m_u2082_2441_, 1);
        v___x_2447_ = lean_array_get_size(v_buckets_2446_);
        v___x_2448_ = lean_nat_dec_lt(v___x_2443_, v___x_2447_);
        if v___x_2448_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_2441_);
            crate::leanh::lean_dec_ref(v_inst_2439_);
            crate::leanh::lean_dec_ref(v_inst_2438_);
            return v_m_u2081_2440_;
        } else {
            let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2449_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
                v_inst_2438_,
                v_inst_2439_,
                v_m_u2081_2440_,
                v_m_u2082_2441_,
            );
            return v___x_2449_;
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(
    mut v_inst_2450_: *mut crate::leanh::LeanObject,
    mut v_inst_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ =
        crate::leanh::lean_alloc_closure(l_Std_HashSet_Raw_inter as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2452_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2452_, 1, v_inst_2450_);
    crate::leanh::lean_closure_set(v___x_2452_, 2, v_inst_2451_);
    return v___x_2452_;
}
pub unsafe fn l_Std_HashSet_Raw_instInterOfBEqOfHashable(
    mut v_00_u03b1_2453_: *mut crate::leanh::LeanObject,
    mut v_inst_2454_: *mut crate::leanh::LeanObject,
    mut v_inst_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ =
        crate::leanh::lean_alloc_closure(l_Std_HashSet_Raw_inter as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2456_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2456_, 1, v_inst_2454_);
    crate::leanh::lean_closure_set(v___x_2456_, 2, v_inst_2455_);
    return v___x_2456_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_beq___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_2458_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2458_, 0, v___x_2457_);
    return v___f_2458_;
}
pub unsafe fn l_Std_HashSet_Raw_beq___redArg(
    mut v_inst_2459_: *mut crate::leanh::LeanObject,
    mut v_inst_2460_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2461_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2462_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u8 = 0;
    v___f_2463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_beq___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_beq___redArg___closed__0_once),
        _init_l_Std_HashSet_Raw_beq___redArg___closed__0,
    );
    v___x_2464_ = l_Std_DHashMap_Raw_Const_beq___redArg(
        v_inst_2459_,
        v_inst_2460_,
        v___f_2463_,
        v_m_u2081_2461_,
        v_m_u2082_2462_,
    );
    return v___x_2464_;
}
pub unsafe fn l_Std_HashSet_Raw_beq___redArg___boxed(
    mut v_inst_2465_: *mut crate::leanh::LeanObject,
    mut v_inst_2466_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2467_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2469_: u8 = 0;
    let mut v_r_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2469_ = l_Std_HashSet_Raw_beq___redArg(
        v_inst_2465_,
        v_inst_2466_,
        v_m_u2081_2467_,
        v_m_u2082_2468_,
    );
    v_r_2470_ = crate::leanh::lean_box((v_res_2469_) as usize);
    return v_r_2470_;
}
pub unsafe fn l_Std_HashSet_Raw_beq(
    mut v_00_u03b1_2471_: *mut crate::leanh::LeanObject,
    mut v_inst_2472_: *mut crate::leanh::LeanObject,
    mut v_inst_2473_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2474_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2475_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2476_: u8 = 0;
    v___x_2476_ = l_Std_HashSet_Raw_beq___redArg(
        v_inst_2472_,
        v_inst_2473_,
        v_m_u2081_2474_,
        v_m_u2082_2475_,
    );
    return v___x_2476_;
}
pub unsafe fn l_Std_HashSet_Raw_beq___boxed(
    mut v_00_u03b1_2477_: *mut crate::leanh::LeanObject,
    mut v_inst_2478_: *mut crate::leanh::LeanObject,
    mut v_inst_2479_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2480_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2482_: u8 = 0;
    let mut v_r_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2482_ = l_Std_HashSet_Raw_beq(
        v_00_u03b1_2477_,
        v_inst_2478_,
        v_inst_2479_,
        v_m_u2081_2480_,
        v_m_u2082_2481_,
    );
    v_r_2483_ = crate::leanh::lean_box((v_res_2482_) as usize);
    return v_r_2483_;
}
pub unsafe fn l_Std_HashSet_Raw_instBEqOfHashable___redArg(
    mut v_inst_2484_: *mut crate::leanh::LeanObject,
    mut v_inst_2485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_beq___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2486_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2486_, 1, v_inst_2484_);
    crate::leanh::lean_closure_set(v___x_2486_, 2, v_inst_2485_);
    return v___x_2486_;
}
pub unsafe fn l_Std_HashSet_Raw_instBEqOfHashable(
    mut v_00_u03b1_2487_: *mut crate::leanh::LeanObject,
    mut v_inst_2488_: *mut crate::leanh::LeanObject,
    mut v_inst_2489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_beq___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2490_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2490_, 1, v_inst_2488_);
    crate::leanh::lean_closure_set(v___x_2490_, 2, v_inst_2489_);
    return v___x_2490_;
}
pub unsafe fn l_Std_HashSet_Raw_diff___redArg___lam__0(
    mut v_inst_2491_: *mut crate::leanh::LeanObject,
    mut v_inst_2492_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2493_: *mut crate::leanh::LeanObject,
    mut v___x_2494_: u8,
    mut v_k_2495_: *mut crate::leanh::LeanObject,
    mut v_x_2496_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2497_: u8 = 0;
    v___x_2497_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_2491_,
        v_inst_2492_,
        v_m_u2082_2493_,
        v_k_2495_,
    );
    if v___x_2497_ == 0 {
        return v___x_2494_;
    } else {
        let mut v___x_2498_: u8 = 0;
        v___x_2498_ = 0;
        return v___x_2498_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(
    mut v_inst_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2501_: *mut crate::leanh::LeanObject,
    mut v___x_2502_: *mut crate::leanh::LeanObject,
    mut v_k_2503_: *mut crate::leanh::LeanObject,
    mut v_x_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_97__boxed_2505_: u8 = 0;
    let mut v_res_2506_: u8 = 0;
    let mut v_r_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_97__boxed_2505_ = (crate::leanh::lean_unbox(v___x_2502_) as u8);
    v_res_2506_ = l_Std_HashSet_Raw_diff___redArg___lam__0(
        v_inst_2499_,
        v_inst_2500_,
        v_m_u2082_2501_,
        v___x_97__boxed_2505_,
        v_k_2503_,
        v_x_2504_,
    );
    crate::leanh::lean_dec_ref(v_m_u2082_2501_);
    v_r_2507_ = crate::leanh::lean_box((v_res_2506_) as usize);
    return v_r_2507_;
}
pub unsafe fn l_Std_HashSet_Raw_diff___redArg(
    mut v_inst_2508_: *mut crate::leanh::LeanObject,
    mut v_inst_2509_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2510_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    v_size_2512_ = crate::leanh::lean_ctor_get(v_m_u2081_2510_, 0);
    v_buckets_2513_ = crate::leanh::lean_ctor_get(v_m_u2081_2510_, 1);
    v___x_2514_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2515_ = lean_array_get_size(v_buckets_2513_);
    v___x_2516_ = lean_nat_dec_lt(v___x_2514_, v___x_2515_);
    if v___x_2516_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_2510_);
        crate::leanh::lean_dec_ref(v_inst_2509_);
        crate::leanh::lean_dec_ref(v_inst_2508_);
        return v_m_u2082_2511_;
    } else {
        let mut v_size_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: u8 = 0;
        v_size_2517_ = crate::leanh::lean_ctor_get(v_m_u2082_2511_, 0);
        v_buckets_2518_ = crate::leanh::lean_ctor_get(v_m_u2082_2511_, 1);
        v___x_2519_ = lean_array_get_size(v_buckets_2518_);
        v___x_2520_ = lean_nat_dec_lt(v___x_2514_, v___x_2519_);
        if v___x_2520_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_2511_);
            crate::leanh::lean_dec_ref(v_inst_2509_);
            crate::leanh::lean_dec_ref(v_inst_2508_);
            return v_m_u2081_2510_;
        } else {
            let mut v___x_2521_: u8 = 0;
            v___x_2521_ = lean_nat_dec_le(v_size_2512_, v_size_2517_);
            if v___x_2521_ == 0 {
                let mut v___f_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_2522_ = l_Std_HashSet_Raw_union___redArg___closed__0;
                v___x_2523_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
                    v___f_2522_,
                    v_inst_2508_,
                    v_inst_2509_,
                    v_m_u2081_2510_,
                    v_m_u2082_2511_,
                );
                return v___x_2523_;
            } else {
                let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2524_ = crate::leanh::lean_box((v___x_2521_) as usize);
                v___f_2525_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2525_, 0, v_inst_2508_);
                crate::leanh::lean_closure_set(v___f_2525_, 1, v_inst_2509_);
                crate::leanh::lean_closure_set(v___f_2525_, 2, v_m_u2082_2511_);
                crate::leanh::lean_closure_set(v___f_2525_, 3, v___x_2524_);
                v___x_2526_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2525_, v_m_u2081_2510_);
                return v___x_2526_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_diff(
    mut v_00_u03b1_2527_: *mut crate::leanh::LeanObject,
    mut v_inst_2528_: *mut crate::leanh::LeanObject,
    mut v_inst_2529_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2530_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    v_size_2532_ = crate::leanh::lean_ctor_get(v_m_u2081_2530_, 0);
    v_buckets_2533_ = crate::leanh::lean_ctor_get(v_m_u2081_2530_, 1);
    v___x_2534_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2535_ = lean_array_get_size(v_buckets_2533_);
    v___x_2536_ = lean_nat_dec_lt(v___x_2534_, v___x_2535_);
    if v___x_2536_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_2530_);
        crate::leanh::lean_dec_ref(v_inst_2529_);
        crate::leanh::lean_dec_ref(v_inst_2528_);
        return v_m_u2082_2531_;
    } else {
        let mut v_size_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2540_: u8 = 0;
        v_size_2537_ = crate::leanh::lean_ctor_get(v_m_u2082_2531_, 0);
        v_buckets_2538_ = crate::leanh::lean_ctor_get(v_m_u2082_2531_, 1);
        v___x_2539_ = lean_array_get_size(v_buckets_2538_);
        v___x_2540_ = lean_nat_dec_lt(v___x_2534_, v___x_2539_);
        if v___x_2540_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_2531_);
            crate::leanh::lean_dec_ref(v_inst_2529_);
            crate::leanh::lean_dec_ref(v_inst_2528_);
            return v_m_u2081_2530_;
        } else {
            let mut v___x_2541_: u8 = 0;
            v___x_2541_ = lean_nat_dec_le(v_size_2532_, v_size_2537_);
            if v___x_2541_ == 0 {
                let mut v___f_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_2542_ = l_Std_HashSet_Raw_union___redArg___closed__0;
                v___x_2543_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
                    v___f_2542_,
                    v_inst_2528_,
                    v_inst_2529_,
                    v_m_u2081_2530_,
                    v_m_u2082_2531_,
                );
                return v___x_2543_;
            } else {
                let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2544_ = crate::leanh::lean_box((v___x_2541_) as usize);
                v___f_2545_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2545_, 0, v_inst_2528_);
                crate::leanh::lean_closure_set(v___f_2545_, 1, v_inst_2529_);
                crate::leanh::lean_closure_set(v___f_2545_, 2, v_m_u2082_2531_);
                crate::leanh::lean_closure_set(v___f_2545_, 3, v___x_2544_);
                v___x_2546_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2545_, v_m_u2081_2530_);
                return v___x_2546_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(
    mut v_inst_2547_: *mut crate::leanh::LeanObject,
    mut v_inst_2548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2549_ =
        crate::leanh::lean_alloc_closure(l_Std_HashSet_Raw_diff as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2549_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2549_, 1, v_inst_2547_);
    crate::leanh::lean_closure_set(v___x_2549_, 2, v_inst_2548_);
    return v___x_2549_;
}
pub unsafe fn l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(
    mut v_00_u03b1_2550_: *mut crate::leanh::LeanObject,
    mut v_inst_2551_: *mut crate::leanh::LeanObject,
    mut v_inst_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ =
        crate::leanh::lean_alloc_closure(l_Std_HashSet_Raw_diff as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2553_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2553_, 1, v_inst_2551_);
    crate::leanh::lean_closure_set(v___x_2553_, 2, v_inst_2552_);
    return v___x_2553_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__0(
    mut v_p_2554_: *mut crate::leanh::LeanObject,
    mut v___x_2555_: *mut crate::leanh::LeanObject,
    mut v___x_2556_: *mut crate::leanh::LeanObject,
    mut v_a_2557_: *mut crate::leanh::LeanObject,
    mut v_b_2558_: *mut crate::leanh::LeanObject,
    mut v_acc_2559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    v___x_2560_ = crate::leanh::lean_apply_1(v_p_2554_, v_a_2557_);
    v___x_2561_ = (crate::leanh::lean_unbox(v___x_2560_) as u8);
    if v___x_2561_ == 0 {
        let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2556_);
        v___x_2562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2562_, 0, v___x_2560_);
        v___x_2563_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2563_, 0, v___x_2562_);
        crate::leanh::lean_ctor_set(v___x_2563_, 1, v___x_2555_);
        v___x_2564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
        return v___x_2564_;
    } else {
        let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2565_, 0, v___x_2556_);
        return v___x_2565_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__0___boxed(
    mut v_p_2566_: *mut crate::leanh::LeanObject,
    mut v___x_2567_: *mut crate::leanh::LeanObject,
    mut v___x_2568_: *mut crate::leanh::LeanObject,
    mut v_a_2569_: *mut crate::leanh::LeanObject,
    mut v_b_2570_: *mut crate::leanh::LeanObject,
    mut v_acc_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Std_HashSet_Raw_all___redArg___lam__0(
        v_p_2566_,
        v___x_2567_,
        v___x_2568_,
        v_a_2569_,
        v_b_2570_,
        v_acc_2571_,
    );
    crate::leanh::lean_dec_ref(v_acc_2571_);
    return v_res_2572_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__1(
    mut v___x_2573_: *mut crate::leanh::LeanObject,
    mut v___f_2574_: *mut crate::leanh::LeanObject,
    mut v_a_2575_: *mut crate::leanh::LeanObject,
    mut v_x_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_2573_, v___f_2574_, v_a_2575_, v___y_2577_);
    return v___x_2578_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg(
    mut v_m_2582_: *mut crate::leanh::LeanObject,
    mut v_p_2583_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2590_: usize = 0;
    let mut v___x_2591_: usize = 0;
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2585_ = crate::leanh::lean_ctor_get(v_m_2582_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2585_);
    crate::leanh::lean_dec_ref(v_m_2582_);
    v___x_2586_ = crate::leanh::lean_box(0);
    v___x_2587_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2588_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2588_, 0, v_p_2583_);
    crate::leanh::lean_closure_set(v___f_2588_, 1, v___x_2586_);
    crate::leanh::lean_closure_set(v___f_2588_, 2, v___x_2587_);
    v___f_2589_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2589_, 0, v___x_2584_);
    crate::leanh::lean_closure_set(v___f_2589_, 1, v___f_2588_);
    v_sz_2590_ = lean_array_size(v_buckets_2585_);
    v___x_2591_ = 0usize;
    v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2584_,
        v_buckets_2585_,
        v___f_2589_,
        v_sz_2590_,
        v___x_2591_,
        v___x_2587_,
    );
    v_fst_2593_ = crate::leanh::lean_ctor_get(v___x_2592_, 0);
    crate::leanh::lean_inc(v_fst_2593_);
    crate::leanh::lean_dec(v___x_2592_);
    if crate::leanh::lean_obj_tag(v_fst_2593_) == 0 {
        let mut v___x_2594_: u8 = 0;
        v___x_2594_ = 1;
        return v___x_2594_;
    } else {
        let mut v_val_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2596_: u8 = 0;
        v_val_2595_ = crate::leanh::lean_ctor_get(v_fst_2593_, 0);
        crate::leanh::lean_inc(v_val_2595_);
        crate::leanh::lean_dec_ref_known(v_fst_2593_, 1);
        v___x_2596_ = (crate::leanh::lean_unbox(v_val_2595_) as u8);
        crate::leanh::lean_dec(v_val_2595_);
        return v___x_2596_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___boxed(
    mut v_m_2597_: *mut crate::leanh::LeanObject,
    mut v_p_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2599_: u8 = 0;
    let mut v_r_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2599_ = l_Std_HashSet_Raw_all___redArg(v_m_2597_, v_p_2598_);
    v_r_2600_ = crate::leanh::lean_box((v_res_2599_) as usize);
    return v_r_2600_;
}
pub unsafe fn l_Std_HashSet_Raw_all(
    mut v_00_u03b1_2601_: *mut crate::leanh::LeanObject,
    mut v_m_2602_: *mut crate::leanh::LeanObject,
    mut v_p_2603_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2605_ = crate::leanh::lean_ctor_get(v_m_2602_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2605_);
    crate::leanh::lean_dec_ref(v_m_2602_);
    v___x_2606_ = crate::leanh::lean_box(0);
    v___x_2607_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2608_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2608_, 0, v_p_2603_);
    crate::leanh::lean_closure_set(v___f_2608_, 1, v___x_2606_);
    crate::leanh::lean_closure_set(v___f_2608_, 2, v___x_2607_);
    v___f_2609_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2609_, 0, v___x_2604_);
    crate::leanh::lean_closure_set(v___f_2609_, 1, v___f_2608_);
    v_sz_2610_ = lean_array_size(v_buckets_2605_);
    v___x_2611_ = 0usize;
    v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2604_,
        v_buckets_2605_,
        v___f_2609_,
        v_sz_2610_,
        v___x_2611_,
        v___x_2607_,
    );
    v_fst_2613_ = crate::leanh::lean_ctor_get(v___x_2612_, 0);
    crate::leanh::lean_inc(v_fst_2613_);
    crate::leanh::lean_dec(v___x_2612_);
    if crate::leanh::lean_obj_tag(v_fst_2613_) == 0 {
        let mut v___x_2614_: u8 = 0;
        v___x_2614_ = 1;
        return v___x_2614_;
    } else {
        let mut v_val_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2616_: u8 = 0;
        v_val_2615_ = crate::leanh::lean_ctor_get(v_fst_2613_, 0);
        crate::leanh::lean_inc(v_val_2615_);
        crate::leanh::lean_dec_ref_known(v_fst_2613_, 1);
        v___x_2616_ = (crate::leanh::lean_unbox(v_val_2615_) as u8);
        crate::leanh::lean_dec(v_val_2615_);
        return v___x_2616_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___boxed(
    mut v_00_u03b1_2617_: *mut crate::leanh::LeanObject,
    mut v_m_2618_: *mut crate::leanh::LeanObject,
    mut v_p_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2620_: u8 = 0;
    let mut v_r_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2620_ = l_Std_HashSet_Raw_all(v_00_u03b1_2617_, v_m_2618_, v_p_2619_);
    v_r_2621_ = crate::leanh::lean_box((v_res_2620_) as usize);
    return v_r_2621_;
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___lam__0(
    mut v_p_2622_: *mut crate::leanh::LeanObject,
    mut v___x_2623_: *mut crate::leanh::LeanObject,
    mut v___x_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_b_2626_: *mut crate::leanh::LeanObject,
    mut v_acc_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    v___x_2628_ = crate::leanh::lean_apply_1(v_p_2622_, v_a_2625_);
    v___x_2629_ = (crate::leanh::lean_unbox(v___x_2628_) as u8);
    if v___x_2629_ == 0 {
        let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2630_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2630_, 0, v___x_2623_);
        return v___x_2630_;
    } else {
        let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2623_);
        v___x_2631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2631_, 0, v___x_2628_);
        v___x_2632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2631_);
        crate::leanh::lean_ctor_set(v___x_2632_, 1, v___x_2624_);
        v___x_2633_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2633_, 0, v___x_2632_);
        return v___x_2633_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___lam__0___boxed(
    mut v_p_2634_: *mut crate::leanh::LeanObject,
    mut v___x_2635_: *mut crate::leanh::LeanObject,
    mut v___x_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
    mut v_b_2638_: *mut crate::leanh::LeanObject,
    mut v_acc_2639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2640_ = l_Std_HashSet_Raw_any___redArg___lam__0(
        v_p_2634_,
        v___x_2635_,
        v___x_2636_,
        v_a_2637_,
        v_b_2638_,
        v_acc_2639_,
    );
    crate::leanh::lean_dec_ref(v_acc_2639_);
    return v_res_2640_;
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg(
    mut v_m_2641_: *mut crate::leanh::LeanObject,
    mut v_p_2642_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2649_: usize = 0;
    let mut v___x_2650_: usize = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2643_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2644_ = crate::leanh::lean_ctor_get(v_m_2641_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2644_);
    crate::leanh::lean_dec_ref(v_m_2641_);
    v___x_2645_ = crate::leanh::lean_box(0);
    v___x_2646_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2647_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2647_, 0, v_p_2642_);
    crate::leanh::lean_closure_set(v___f_2647_, 1, v___x_2646_);
    crate::leanh::lean_closure_set(v___f_2647_, 2, v___x_2645_);
    v___f_2648_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2648_, 0, v___x_2643_);
    crate::leanh::lean_closure_set(v___f_2648_, 1, v___f_2647_);
    v_sz_2649_ = lean_array_size(v_buckets_2644_);
    v___x_2650_ = 0usize;
    v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2643_,
        v_buckets_2644_,
        v___f_2648_,
        v_sz_2649_,
        v___x_2650_,
        v___x_2646_,
    );
    v_fst_2652_ = crate::leanh::lean_ctor_get(v___x_2651_, 0);
    crate::leanh::lean_inc(v_fst_2652_);
    crate::leanh::lean_dec(v___x_2651_);
    if crate::leanh::lean_obj_tag(v_fst_2652_) == 0 {
        let mut v___x_2653_: u8 = 0;
        v___x_2653_ = 0;
        return v___x_2653_;
    } else {
        let mut v_val_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: u8 = 0;
        v_val_2654_ = crate::leanh::lean_ctor_get(v_fst_2652_, 0);
        crate::leanh::lean_inc(v_val_2654_);
        crate::leanh::lean_dec_ref_known(v_fst_2652_, 1);
        v___x_2655_ = (crate::leanh::lean_unbox(v_val_2654_) as u8);
        crate::leanh::lean_dec(v_val_2654_);
        return v___x_2655_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___boxed(
    mut v_m_2656_: *mut crate::leanh::LeanObject,
    mut v_p_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2658_: u8 = 0;
    let mut v_r_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2658_ = l_Std_HashSet_Raw_any___redArg(v_m_2656_, v_p_2657_);
    v_r_2659_ = crate::leanh::lean_box((v_res_2658_) as usize);
    return v_r_2659_;
}
pub unsafe fn l_Std_HashSet_Raw_any(
    mut v_00_u03b1_2660_: *mut crate::leanh::LeanObject,
    mut v_m_2661_: *mut crate::leanh::LeanObject,
    mut v_p_2662_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2669_: usize = 0;
    let mut v___x_2670_: usize = 0;
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2663_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2664_ = crate::leanh::lean_ctor_get(v_m_2661_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2664_);
    crate::leanh::lean_dec_ref(v_m_2661_);
    v___x_2665_ = crate::leanh::lean_box(0);
    v___x_2666_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2667_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2667_, 0, v_p_2662_);
    crate::leanh::lean_closure_set(v___f_2667_, 1, v___x_2666_);
    crate::leanh::lean_closure_set(v___f_2667_, 2, v___x_2665_);
    v___f_2668_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2668_, 0, v___x_2663_);
    crate::leanh::lean_closure_set(v___f_2668_, 1, v___f_2667_);
    v_sz_2669_ = lean_array_size(v_buckets_2664_);
    v___x_2670_ = 0usize;
    v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2663_,
        v_buckets_2664_,
        v___f_2668_,
        v_sz_2669_,
        v___x_2670_,
        v___x_2666_,
    );
    v_fst_2672_ = crate::leanh::lean_ctor_get(v___x_2671_, 0);
    crate::leanh::lean_inc(v_fst_2672_);
    crate::leanh::lean_dec(v___x_2671_);
    if crate::leanh::lean_obj_tag(v_fst_2672_) == 0 {
        let mut v___x_2673_: u8 = 0;
        v___x_2673_ = 0;
        return v___x_2673_;
    } else {
        let mut v_val_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: u8 = 0;
        v_val_2674_ = crate::leanh::lean_ctor_get(v_fst_2672_, 0);
        crate::leanh::lean_inc(v_val_2674_);
        crate::leanh::lean_dec_ref_known(v_fst_2672_, 1);
        v___x_2675_ = (crate::leanh::lean_unbox(v_val_2674_) as u8);
        crate::leanh::lean_dec(v_val_2674_);
        return v___x_2675_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___boxed(
    mut v_00_u03b1_2676_: *mut crate::leanh::LeanObject,
    mut v_m_2677_: *mut crate::leanh::LeanObject,
    mut v_p_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2679_: u8 = 0;
    let mut v_r_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Std_HashSet_Raw_any(v_00_u03b1_2676_, v_m_2677_, v_p_2678_);
    v_r_2680_ = crate::leanh::lean_box((v_res_2679_) as usize);
    return v_r_2680_;
}
pub unsafe fn l_Std_HashSet_Raw_insertMany___redArg(
    mut v_inst_2681_: *mut crate::leanh::LeanObject,
    mut v_inst_2682_: *mut crate::leanh::LeanObject,
    mut v_inst_2683_: *mut crate::leanh::LeanObject,
    mut v_m_2684_: *mut crate::leanh::LeanObject,
    mut v_l_2685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: u8 = 0;
    v_buckets_2686_ = crate::leanh::lean_ctor_get(v_m_2684_, 1);
    v___x_2687_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2688_ = lean_array_get_size(v_buckets_2686_);
    v___x_2689_ = lean_nat_dec_lt(v___x_2687_, v___x_2688_);
    if v___x_2689_ == 0 {
        crate::leanh::lean_dec(v_l_2685_);
        crate::leanh::lean_dec(v_inst_2683_);
        crate::leanh::lean_dec_ref(v_inst_2682_);
        crate::leanh::lean_dec_ref(v_inst_2681_);
        return v_m_2684_;
    } else {
        let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v_inst_2683_,
            v_inst_2681_,
            v_inst_2682_,
            v_m_2684_,
            v_l_2685_,
        );
        return v___x_2690_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_insertMany(
    mut v_00_u03b1_2691_: *mut crate::leanh::LeanObject,
    mut v_inst_2692_: *mut crate::leanh::LeanObject,
    mut v_inst_2693_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_2694_: *mut crate::leanh::LeanObject,
    mut v_inst_2695_: *mut crate::leanh::LeanObject,
    mut v_m_2696_: *mut crate::leanh::LeanObject,
    mut v_l_2697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    v_buckets_2698_ = crate::leanh::lean_ctor_get(v_m_2696_, 1);
    v___x_2699_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2700_ = lean_array_get_size(v_buckets_2698_);
    v___x_2701_ = lean_nat_dec_lt(v___x_2699_, v___x_2700_);
    if v___x_2701_ == 0 {
        crate::leanh::lean_dec(v_l_2697_);
        crate::leanh::lean_dec(v_inst_2695_);
        crate::leanh::lean_dec_ref(v_inst_2693_);
        crate::leanh::lean_dec_ref(v_inst_2692_);
        return v_m_2696_;
    } else {
        let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v_inst_2695_,
            v_inst_2692_,
            v_inst_2693_,
            v_m_2696_,
            v_l_2697_,
        );
        return v___x_2702_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_ofArray___redArg(
    mut v_inst_2707_: *mut crate::leanh::LeanObject,
    mut v_inst_2708_: *mut crate::leanh::LeanObject,
    mut v_l_2709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    v___x_2710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2711_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2711_ == 0 {
        crate::leanh::lean_dec_ref(v_l_2709_);
        crate::leanh::lean_dec_ref(v_inst_2708_);
        crate::leanh::lean_dec_ref(v_inst_2707_);
        return v___x_2710_;
    } else {
        let mut v___f_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2712_ = l_Std_HashSet_Raw_ofArray___redArg___closed__1;
        v___x_2713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_2712_,
            v_inst_2707_,
            v_inst_2708_,
            v___x_2710_,
            v_l_2709_,
        );
        return v___x_2713_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_ofArray(
    mut v_00_u03b1_2714_: *mut crate::leanh::LeanObject,
    mut v_inst_2715_: *mut crate::leanh::LeanObject,
    mut v_inst_2716_: *mut crate::leanh::LeanObject,
    mut v_l_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: u8 = 0;
    v___x_2718_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2719_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2719_ == 0 {
        crate::leanh::lean_dec_ref(v_l_2717_);
        crate::leanh::lean_dec_ref(v_inst_2716_);
        crate::leanh::lean_dec_ref(v_inst_2715_);
        return v___x_2718_;
    } else {
        let mut v___f_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2720_ = l_Std_HashSet_Raw_ofArray___redArg___closed__1;
        v___x_2721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_2720_,
            v_inst_2715_,
            v_inst_2716_,
            v___x_2718_,
            v_l_2717_,
        );
        return v___x_2721_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets___redArg(
    mut v_m_2722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2722_);
    return v___x_2723_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(
    mut v_m_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_2724_);
    crate::leanh::lean_dec_ref(v_m_2724_);
    return v_res_2725_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets(
    mut v_00_u03b1_2726_: *mut crate::leanh::LeanObject,
    mut v_m_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2727_);
    return v___x_2728_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets___boxed(
    mut v_00_u03b1_2729_: *mut crate::leanh::LeanObject,
    mut v_m_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_2729_, v_m_2730_);
    crate::leanh::lean_dec_ref(v_m_2730_);
    return v_res_2731_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr___redArg___lam__2(
    mut v_inst_2735_: *mut crate::leanh::LeanObject,
    mut v___f_2736_: *mut crate::leanh::LeanObject,
    mut v_m_2737_: *mut crate::leanh::LeanObject,
    mut v_prec_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2743_: u8 = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___f_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut v_unused_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2739_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v_buckets_2740_ = crate::leanh::lean_ctor_get(v_m_2737_, 1);
                v_isSharedCheck_2760_ = (!crate::leanh::lean_is_exclusive(v_m_2737_)) as u8;
                if v_isSharedCheck_2760_ == 0 {
                    v_unused_2761_ = crate::leanh::lean_ctor_get(v_m_2737_, 0);
                    crate::leanh::lean_dec(v_unused_2761_);
                    v___x_2742_ = v_m_2737_;
                    v_isShared_2743_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2740_);
                    crate::leanh::lean_dec(v_m_2737_);
                    v___x_2742_ = crate::leanh::lean_box(0);
                    v_isShared_2743_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2744_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1;
                v___x_2752_ = crate::leanh::lean_box(0);
                v___x_2753_ = lean_array_get_size(v_buckets_2740_);
                v___x_2754_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2755_ = lean_nat_dec_lt(v___x_2754_, v___x_2753_);
                if v___x_2755_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_2740_);
                    crate::leanh::lean_dec_ref(v___f_2736_);
                    v___y_2746_ = v___x_2752_;
                    state = 2;
                    continue;
                } else {
                    v___f_2756_ = crate::leanh::lean_alloc_closure(
                        l_Std_HashSet_Raw_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_2756_, 0, v___x_2739_);
                    crate::leanh::lean_closure_set(v___f_2756_, 1, v___f_2736_);
                    v___x_2757_ = lean_usize_of_nat(v___x_2753_);
                    v___x_2758_ = 0usize;
                    v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2739_,
                        v___f_2756_,
                        v_buckets_2740_,
                        v___x_2757_,
                        v___x_2758_,
                        v___x_2752_,
                    );
                    v___y_2746_ = v___x_2759_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2747_ = l_List_repr___redArg(v_inst_2735_, v___y_2746_);
                if v_isShared_2743_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2742_, 5);
                    crate::leanh::lean_ctor_set(v___x_2742_, 1, v___x_2747_);
                    crate::leanh::lean_ctor_set(v___x_2742_, 0, v___x_2744_);
                    v___x_2749_ = v___x_2742_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2747_);
                    v___x_2749_ = v_reuseFailAlloc_2751_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2750_ = l_Repr_addAppParen(v___x_2749_, v_prec_2738_);
                return v___x_2750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(
    mut v_inst_2762_: *mut crate::leanh::LeanObject,
    mut v___f_2763_: *mut crate::leanh::LeanObject,
    mut v_m_2764_: *mut crate::leanh::LeanObject,
    mut v_prec_2765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2766_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(
        v_inst_2762_,
        v___f_2763_,
        v_m_2764_,
        v_prec_2765_,
    );
    crate::leanh::lean_dec(v_prec_2765_);
    return v_res_2766_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr___redArg(
    mut v_inst_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2768_ = l_Std_HashSet_Raw_toList___redArg___closed__10;
    v___f_2769_ = crate::leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2769_, 0, v_inst_2767_);
    crate::leanh::lean_closure_set(v___f_2769_, 1, v___f_2768_);
    return v___f_2769_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr(
    mut v_00_u03b1_2770_: *mut crate::leanh::LeanObject,
    mut v_inst_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_2771_);
    return v___x_2772_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_Raw(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_Raw(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashSet_Raw(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashSet_Raw(builtin);
}
