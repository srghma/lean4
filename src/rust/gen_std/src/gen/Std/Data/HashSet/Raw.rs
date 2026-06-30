// Lean compiler output
// Module: Std.Data.HashSet.Raw
// Imports: Std.Data.HashMap.Raw
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
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashSet_Raw_term___x7em___00__closed__0_value: leanh::LeanStringObject<4> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__1_value: leanh::LeanStringObject<8> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__2_value: leanh::LeanStringObject<4> =
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
        m_data: [82, 97, 119, 0],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__3_value: leanh::LeanStringObject<9> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value)
                as *mut leanh::LeanObject,
            4197276704451117917 as *mut leanh::LeanObject,
        ],
    };
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value)
                as *mut leanh::LeanObject,
            18086102783661291962 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_HashSet_Raw_term___x7em___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__3_value)
                as *mut leanh::LeanObject,
            17417104850251625812 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__5_value: leanh::LeanStringObject<8> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__5_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__7_value: leanh::LeanStringObject<5> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__8_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__9_value: leanh::LeanStringObject<5> =
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__9_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__11_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__10_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__13_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_HashSet_Raw_term___x7em__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,6049842283740396800 as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value) as *mut leanh::LeanObject;
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value) as *mut leanh::LeanObject,4197276704451117917 as *mut leanh::LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value) as *mut leanh::LeanObject,18086102783661291962 as *mut leanh::LeanObject] };
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,8576336600160769941 as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1: u8 = 0;
pub static l_Std_HashSet_Raw_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashSet_Raw_toList___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__10_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashSet_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashSet_Raw_toList___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__11_value: leanh::LeanClosureObject<
    2,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_HashSet_Raw_toList___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_toList___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofList___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofList___redArg___closed__1_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashSet_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashSet_Raw_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_toArray___redArg___closed__1_value: leanh::LeanClosureObject<
    2,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_HashSet_Raw_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_union___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_union___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_union___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_HashSet_Raw_beq___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashSet_Raw_beq___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashSet_Raw_all___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_HashSet_Raw_all___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_all___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofArray___redArg___closed__0_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_ofArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_ofArray___redArg___closed__1_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_ofArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value:
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
        83, 116, 100, 46, 72, 97, 115, 104, 83, 101, 116, 46, 82, 97, 119, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___redArg(
    mut v_capacity_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = leanh::lean_unsigned_to_nat(0);
    v___x_1389_ = leanh::lean_unsigned_to_nat(4);
    v___x_1390_ = lean_nat_mul(v_capacity_1387_, v___x_1389_);
    v___x_1391_ = leanh::lean_unsigned_to_nat(3);
    v___x_1392_ = lean_nat_div(v___x_1390_, v___x_1391_);
    leanh::lean_dec(v___x_1390_);
    v___x_1393_ = l_Nat_nextPowerOfTwo(v___x_1392_);
    leanh::lean_dec(v___x_1392_);
    v___x_1394_ = leanh::lean_box(0);
    v___x_1395_ = lean_mk_array(v___x_1393_, v___x_1394_);
    v___x_1396_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1396_, 0, v___x_1388_);
    leanh::lean_ctor_set(v___x_1396_, 1, v___x_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Std_HashSet_Raw_emptyWithCapacity___redArg(v_capacity_1397_);
    leanh::lean_dec(v_capacity_1397_);
    return v_res_1398_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity(
    mut v_00_u03b1_1399_: *mut leanh::LeanObject,
    mut v_capacity_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = leanh::lean_unsigned_to_nat(0);
    v___x_1402_ = leanh::lean_unsigned_to_nat(4);
    v___x_1403_ = lean_nat_mul(v_capacity_1400_, v___x_1402_);
    v___x_1404_ = leanh::lean_unsigned_to_nat(3);
    v___x_1405_ = lean_nat_div(v___x_1403_, v___x_1404_);
    leanh::lean_dec(v___x_1403_);
    v___x_1406_ = l_Nat_nextPowerOfTwo(v___x_1405_);
    leanh::lean_dec(v___x_1405_);
    v___x_1407_ = leanh::lean_box(0);
    v___x_1408_ = lean_mk_array(v___x_1406_, v___x_1407_);
    v___x_1409_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1409_, 0, v___x_1401_);
    leanh::lean_ctor_set(v___x_1409_, 1, v___x_1408_);
    return v___x_1409_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___boxed(
    mut v_00_u03b1_1410_: *mut leanh::LeanObject,
    mut v_capacity_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Std_HashSet_Raw_emptyWithCapacity(v_00_u03b1_1410_, v_capacity_1411_);
    leanh::lean_dec(v_capacity_1411_);
    return v_res_1412_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = leanh::lean_box(0);
    v___x_1414_ = leanh::lean_unsigned_to_nat(16);
    v___x_1415_ = lean_mk_array(v___x_1414_, v___x_1413_);
    return v___x_1415_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0,
    );
    v___x_1417_ = leanh::lean_unsigned_to_nat(0);
    v___x_1418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    leanh::lean_ctor_set(v___x_1418_, 1, v___x_1416_);
    return v___x_1418_;
}
pub unsafe fn l_Std_HashSet_Raw_instEmptyCollection(
    mut v_00_u03b1_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    return v___x_1420_;
}
pub unsafe fn l_Std_HashSet_Raw_instInhabited(
    mut v_00_u03b1_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    return v___x_1422_;
}
pub unsafe fn _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5;
    v___x_1464_ = l_String_toRawSubstring_x27(v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(
    mut v_x_1486_: *mut leanh::LeanObject,
    mut v_a_1487_: *mut leanh::LeanObject,
    mut v_a_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    v___x_1489_ = l_Std_HashSet_Raw_term___x7em___00__closed__4;
    leanh::lean_inc(v_x_1486_);
    v___x_1490_ = l_Lean_Syntax_isOfKind(v_x_1486_, v___x_1489_);
    if v___x_1490_ == 0 {
        let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1486_);
        v___x_1491_ = leanh::lean_box(1);
        v___x_1492_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1492_, 0, v___x_1491_);
        leanh::lean_ctor_set(v___x_1492_, 1, v_a_1488_);
        return v___x_1492_;
    } else {
        let mut v_quotContext_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: u8 = 0;
        let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1493_ = leanh::lean_ctor_get(v_a_1487_, 1);
        v_currMacroScope_1494_ = leanh::lean_ctor_get(v_a_1487_, 2);
        v_ref_1495_ = leanh::lean_ctor_get(v_a_1487_, 5);
        v___x_1496_ = leanh::lean_unsigned_to_nat(0);
        v___x_1497_ = l_Lean_Syntax_getArg(v_x_1486_, v___x_1496_);
        v___x_1498_ = leanh::lean_unsigned_to_nat(2);
        v___x_1499_ = l_Lean_Syntax_getArg(v_x_1486_, v___x_1498_);
        leanh::lean_dec(v_x_1486_);
        v___x_1500_ = 0;
        v___x_1501_ = l_Lean_SourceInfo_fromRef(v_ref_1495_, v___x_1500_);
        v___x_1502_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4;
        v___x_1503_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once), _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
        v___x_1504_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7;
        leanh::lean_inc(v_currMacroScope_1494_);
        leanh::lean_inc(v_quotContext_1493_);
        v___x_1505_ =
            l_Lean_addMacroScope(v_quotContext_1493_, v___x_1504_, v_currMacroScope_1494_);
        v___x_1506_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12;
        leanh::lean_inc_n(v___x_1501_, 2);
        v___x_1507_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1507_, 0, v___x_1501_);
        leanh::lean_ctor_set(v___x_1507_, 1, v___x_1503_);
        leanh::lean_ctor_set(v___x_1507_, 2, v___x_1505_);
        leanh::lean_ctor_set(v___x_1507_, 3, v___x_1506_);
        v___x_1508_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14;
        v___x_1509_ = l_Lean_Syntax_node2(v___x_1501_, v___x_1508_, v___x_1497_, v___x_1499_);
        v___x_1510_ = l_Lean_Syntax_node2(v___x_1501_, v___x_1502_, v___x_1507_, v___x_1509_);
        v___x_1511_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
        leanh::lean_ctor_set(v___x_1511_, 1, v_a_1488_);
        return v___x_1511_;
    }
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(
    mut v_x_1512_: *mut leanh::LeanObject,
    mut v_a_1513_: *mut leanh::LeanObject,
    mut v_a_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(v_x_1512_, v_a_1513_, v_a_1514_);
    leanh::lean_dec_ref(v_a_1513_);
    return v_res_1515_;
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(
    mut v_x_1519_: *mut leanh::LeanObject,
    mut v_a_1520_: *mut leanh::LeanObject,
    mut v_a_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: u8 = 0;
    v___x_1522_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4;
    leanh::lean_inc(v_x_1519_);
    v___x_1523_ = l_Lean_Syntax_isOfKind(v_x_1519_, v___x_1522_);
    if v___x_1523_ == 0 {
        let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1519_);
        v___x_1524_ = leanh::lean_box(0);
        v___x_1525_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1525_, 0, v___x_1524_);
        leanh::lean_ctor_set(v___x_1525_, 1, v_a_1521_);
        return v___x_1525_;
    } else {
        let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: u8 = 0;
        v___x_1526_ = leanh::lean_unsigned_to_nat(0);
        v___x_1527_ = l_Lean_Syntax_getArg(v_x_1519_, v___x_1526_);
        v___x_1528_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1;
        leanh::lean_inc(v___x_1527_);
        v___x_1529_ = l_Lean_Syntax_isOfKind(v___x_1527_, v___x_1528_);
        if v___x_1529_ == 0 {
            let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1527_);
            leanh::lean_dec(v_x_1519_);
            v___x_1530_ = leanh::lean_box(0);
            v___x_1531_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
            leanh::lean_ctor_set(v___x_1531_, 1, v_a_1521_);
            return v___x_1531_;
        } else {
            let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1535_: u8 = 0;
            v___x_1532_ = leanh::lean_unsigned_to_nat(1);
            v___x_1533_ = l_Lean_Syntax_getArg(v_x_1519_, v___x_1532_);
            leanh::lean_dec(v_x_1519_);
            v___x_1534_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1533_);
            v___x_1535_ = l_Lean_Syntax_matchesNull(v___x_1533_, v___x_1534_);
            if v___x_1535_ == 0 {
                let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1533_);
                leanh::lean_dec(v___x_1527_);
                v___x_1536_ = leanh::lean_box(0);
                v___x_1537_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                leanh::lean_ctor_set(v___x_1537_, 1, v_a_1521_);
                return v___x_1537_;
            } else {
                let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1541_: u8 = 0;
                let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1538_ = l_Lean_Syntax_getArg(v___x_1533_, v___x_1526_);
                v___x_1539_ = l_Lean_Syntax_getArg(v___x_1533_, v___x_1532_);
                leanh::lean_dec(v___x_1533_);
                v_ref_1540_ = l_Lean_replaceRef(v___x_1527_, v_a_1520_);
                leanh::lean_dec(v___x_1527_);
                v___x_1541_ = 0;
                v___x_1542_ = l_Lean_SourceInfo_fromRef(v_ref_1540_, v___x_1541_);
                leanh::lean_dec(v_ref_1540_);
                v___x_1543_ = l_Std_HashSet_Raw_term___x7em___00__closed__4;
                v___x_1544_ = l_Std_HashSet_Raw_term___x7em___00__closed__7;
                leanh::lean_inc(v___x_1542_);
                v___x_1545_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1545_, 0, v___x_1542_);
                leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
                v___x_1546_ = l_Lean_Syntax_node3(
                    v___x_1542_,
                    v___x_1543_,
                    v___x_1538_,
                    v___x_1545_,
                    v___x_1539_,
                );
                v___x_1547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1547_, 0, v___x_1546_);
                leanh::lean_ctor_set(v___x_1547_, 1, v_a_1521_);
                return v___x_1547_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(
    mut v_x_1548_: *mut leanh::LeanObject,
    mut v_a_1549_: *mut leanh::LeanObject,
    mut v_a_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ =
        l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(
            v_x_1548_, v_a_1549_, v_a_1550_,
        );
    leanh::lean_dec(v_a_1549_);
    return v_res_1551_;
}
pub unsafe fn l_Std_HashSet_Raw_insert___redArg(
    mut v_inst_1552_: *mut leanh::LeanObject,
    mut v_inst_1553_: *mut leanh::LeanObject,
    mut v_m_1554_: *mut leanh::LeanObject,
    mut v_a_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    v_buckets_1556_ = leanh::lean_ctor_get(v_m_1554_, 1);
    v___x_1557_ = leanh::lean_unsigned_to_nat(0);
    v___x_1558_ = lean_array_get_size(v_buckets_1556_);
    v___x_1559_ = lean_nat_dec_lt(v___x_1557_, v___x_1558_);
    if v___x_1559_ == 0 {
        leanh::lean_dec(v_a_1555_);
        leanh::lean_dec_ref(v_inst_1553_);
        leanh::lean_dec_ref(v_inst_1552_);
        return v_m_1554_;
    } else {
        let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1560_ = leanh::lean_box(0);
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
    mut v_00_u03b1_1562_: *mut leanh::LeanObject,
    mut v_inst_1563_: *mut leanh::LeanObject,
    mut v_inst_1564_: *mut leanh::LeanObject,
    mut v_m_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    v_buckets_1567_ = leanh::lean_ctor_get(v_m_1565_, 1);
    v___x_1568_ = leanh::lean_unsigned_to_nat(0);
    v___x_1569_ = lean_array_get_size(v_buckets_1567_);
    v___x_1570_ = lean_nat_dec_lt(v___x_1568_, v___x_1569_);
    if v___x_1570_ == 0 {
        leanh::lean_dec(v_a_1566_);
        leanh::lean_dec_ref(v_inst_1564_);
        leanh::lean_dec_ref(v_inst_1563_);
        return v_m_1565_;
    } else {
        let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1571_ = leanh::lean_box(0);
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
-> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0,
    );
    v___x_1574_ = lean_array_get_size(v___x_1573_);
    return v___x_1574_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1()
-> u8 {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    v___x_1575_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0,
    );
    v___x_1576_ = leanh::lean_unsigned_to_nat(0);
    v___x_1577_ = lean_nat_dec_lt(v___x_1576_, v___x_1575_);
    return v___x_1577_;
}
pub unsafe fn l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(
    mut v_inst_1578_: *mut leanh::LeanObject,
    mut v_inst_1579_: *mut leanh::LeanObject,
    mut v_a_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    v___x_1581_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_1582_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_1582_ == 0 {
        leanh::lean_dec(v_a_1580_);
        leanh::lean_dec_ref(v_inst_1579_);
        leanh::lean_dec_ref(v_inst_1578_);
        return v___x_1581_;
    } else {
        let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1583_ = leanh::lean_box(0);
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
    mut v_inst_1585_: *mut leanh::LeanObject,
    mut v_inst_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1587_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1587_, 0, v_inst_1585_);
    leanh::lean_closure_set(v___f_1587_, 1, v_inst_1586_);
    return v___f_1587_;
}
pub unsafe fn l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(
    mut v_00_u03b1_1588_: *mut leanh::LeanObject,
    mut v_inst_1589_: *mut leanh::LeanObject,
    mut v_inst_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1591_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1591_, 0, v_inst_1589_);
    leanh::lean_closure_set(v___f_1591_, 1, v_inst_1590_);
    return v___f_1591_;
}
pub unsafe fn l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(
    mut v_inst_1592_: *mut leanh::LeanObject,
    mut v_inst_1593_: *mut leanh::LeanObject,
    mut v_a_1594_: *mut leanh::LeanObject,
    mut v_s_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    v_buckets_1596_ = leanh::lean_ctor_get(v_s_1595_, 1);
    v___x_1597_ = leanh::lean_unsigned_to_nat(0);
    v___x_1598_ = lean_array_get_size(v_buckets_1596_);
    v___x_1599_ = lean_nat_dec_lt(v___x_1597_, v___x_1598_);
    if v___x_1599_ == 0 {
        leanh::lean_dec(v_a_1594_);
        leanh::lean_dec_ref(v_inst_1593_);
        leanh::lean_dec_ref(v_inst_1592_);
        return v_s_1595_;
    } else {
        let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1600_ = leanh::lean_box(0);
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
    mut v_inst_1602_: *mut leanh::LeanObject,
    mut v_inst_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1604_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1604_, 0, v_inst_1602_);
    leanh::lean_closure_set(v___f_1604_, 1, v_inst_1603_);
    return v___f_1604_;
}
pub unsafe fn l_Std_HashSet_Raw_instInsertOfBEqOfHashable(
    mut v_00_u03b1_1605_: *mut leanh::LeanObject,
    mut v_inst_1606_: *mut leanh::LeanObject,
    mut v_inst_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1608_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1608_, 0, v_inst_1606_);
    leanh::lean_closure_set(v___f_1608_, 1, v_inst_1607_);
    return v___f_1608_;
}
pub unsafe fn l_Std_HashSet_Raw_containsThenInsert___redArg(
    mut v_inst_1609_: *mut leanh::LeanObject,
    mut v_inst_1610_: *mut leanh::LeanObject,
    mut v_m_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v_val_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v_unused_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1613_ = leanh::lean_ctor_get(v_m_1611_, 0);
                v_buckets_1614_ = leanh::lean_ctor_get(v_m_1611_, 1);
                v___x_1615_ = leanh::lean_unsigned_to_nat(0);
                v___x_1616_ = lean_array_get_size(v_buckets_1614_);
                v___x_1617_ = lean_nat_dec_lt(v___x_1615_, v___x_1616_);
                if v___x_1617_ == 0 {
                    leanh::lean_dec(v_a_1612_);
                    leanh::lean_dec_ref(v_inst_1610_);
                    leanh::lean_dec_ref(v_inst_1609_);
                    v___x_1618_ = leanh::lean_box((v___x_1617_) as usize);
                    v___x_1619_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1619_, 0, v___x_1618_);
                    leanh::lean_ctor_set(v___x_1619_, 1, v_m_1611_);
                    return v___x_1619_;
                } else {
                    leanh::lean_inc_ref(v_inst_1610_);
                    leanh::lean_inc_n(v_a_1612_, 2);
                    v___x_1620_ = leanh::lean_apply_1(v_inst_1610_, v_a_1612_);
                    v___x_1621_ = 32u64;
                    v___x_1622_ = leanh::lean_unbox_uint64(v___x_1620_);
                    v___x_1623_ = lean_uint64_shift_right(v___x_1622_, v___x_1621_);
                    v___x_1624_ = leanh::lean_unbox_uint64(v___x_1620_);
                    leanh::lean_dec_ref(v___x_1620_);
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
                    leanh::lean_inc(v_bkt_1634_);
                    v___x_1635_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_1609_,
                        v_a_1612_,
                        v_bkt_1634_,
                    );
                    if v___x_1635_ == 0 {
                        leanh::lean_inc_ref(v_buckets_1614_);
                        leanh::lean_inc(v_size_1613_);
                        v_isSharedCheck_1661_ = (!leanh::lean_is_exclusive(v_m_1611_)) as u8;
                        if v_isSharedCheck_1661_ == 0 {
                            v_unused_1662_ = leanh::lean_ctor_get(v_m_1611_, 1);
                            leanh::lean_dec(v_unused_1662_);
                            v_unused_1663_ = leanh::lean_ctor_get(v_m_1611_, 0);
                            leanh::lean_dec(v_unused_1663_);
                            v___x_1637_ = v_m_1611_;
                            v_isShared_1638_ = v_isSharedCheck_1661_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_1611_);
                            v___x_1637_ = leanh::lean_box(0);
                            v_isShared_1638_ = v_isSharedCheck_1661_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1612_);
                        leanh::lean_dec_ref(v_inst_1610_);
                        v___x_1664_ = leanh::lean_box((v___x_1635_) as usize);
                        v___x_1665_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1665_, 0, v___x_1664_);
                        leanh::lean_ctor_set(v___x_1665_, 1, v_m_1611_);
                        return v___x_1665_;
                    }
                }
            }
            1 => {
                v___x_1639_ = leanh::lean_box(0);
                v___x_1640_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1641_ = lean_nat_add(v_size_1613_, v___x_1640_);
                leanh::lean_dec(v_size_1613_);
                leanh::lean_inc(v_bkt_1634_);
                v___x_1642_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1642_, 0, v_a_1612_);
                leanh::lean_ctor_set(v___x_1642_, 1, v___x_1639_);
                leanh::lean_ctor_set(v___x_1642_, 2, v_bkt_1634_);
                v_buckets_x27_1643_ = lean_array_uset(v_buckets_1614_, v___x_1633_, v___x_1642_);
                v___x_1644_ = leanh::lean_unsigned_to_nat(4);
                v___x_1645_ = lean_nat_mul(v_size_x27_1641_, v___x_1644_);
                v___x_1646_ = leanh::lean_unsigned_to_nat(3);
                v___x_1647_ = lean_nat_div(v___x_1645_, v___x_1646_);
                leanh::lean_dec(v___x_1645_);
                v___x_1648_ = lean_array_get_size(v_buckets_x27_1643_);
                v___x_1649_ = lean_nat_dec_le(v___x_1647_, v___x_1648_);
                leanh::lean_dec(v___x_1647_);
                if v___x_1649_ == 0 {
                    v_val_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_1610_,
                        v_buckets_x27_1643_,
                    );
                    if v_isShared_1638_ == 0 {
                        leanh::lean_ctor_set(v___x_1637_, 1, v_val_1650_);
                        leanh::lean_ctor_set(v___x_1637_, 0, v_size_x27_1641_);
                        v___x_1652_ = v___x_1637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1655_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_size_x27_1641_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_val_1650_);
                        v___x_1652_ = v_reuseFailAlloc_1655_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1610_);
                    if v_isShared_1638_ == 0 {
                        leanh::lean_ctor_set(v___x_1637_, 1, v_buckets_x27_1643_);
                        leanh::lean_ctor_set(v___x_1637_, 0, v_size_x27_1641_);
                        v___x_1657_ = v___x_1637_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_size_x27_1641_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_buckets_x27_1643_);
                        v___x_1657_ = v_reuseFailAlloc_1660_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1653_ = leanh::lean_box((v___x_1635_) as usize);
                v___x_1654_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1654_, 0, v___x_1653_);
                leanh::lean_ctor_set(v___x_1654_, 1, v___x_1652_);
                return v___x_1654_;
            }
            3 => {
                v___x_1658_ = leanh::lean_box((v___x_1635_) as usize);
                v___x_1659_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1659_, 0, v___x_1658_);
                leanh::lean_ctor_set(v___x_1659_, 1, v___x_1657_);
                return v___x_1659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_containsThenInsert(
    mut v_00_u03b1_1666_: *mut leanh::LeanObject,
    mut v_inst_1667_: *mut leanh::LeanObject,
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_m_1669_: *mut leanh::LeanObject,
    mut v_a_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v_val_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut v_unused_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1671_ = leanh::lean_ctor_get(v_m_1669_, 0);
                v_buckets_1672_ = leanh::lean_ctor_get(v_m_1669_, 1);
                v___x_1673_ = leanh::lean_unsigned_to_nat(0);
                v___x_1674_ = lean_array_get_size(v_buckets_1672_);
                v___x_1675_ = lean_nat_dec_lt(v___x_1673_, v___x_1674_);
                if v___x_1675_ == 0 {
                    leanh::lean_dec(v_a_1670_);
                    leanh::lean_dec_ref(v_inst_1668_);
                    leanh::lean_dec_ref(v_inst_1667_);
                    v___x_1676_ = leanh::lean_box((v___x_1675_) as usize);
                    v___x_1677_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
                    leanh::lean_ctor_set(v___x_1677_, 1, v_m_1669_);
                    return v___x_1677_;
                } else {
                    leanh::lean_inc_ref(v_inst_1668_);
                    leanh::lean_inc_n(v_a_1670_, 2);
                    v___x_1678_ = leanh::lean_apply_1(v_inst_1668_, v_a_1670_);
                    v___x_1679_ = 32u64;
                    v___x_1680_ = leanh::lean_unbox_uint64(v___x_1678_);
                    v___x_1681_ = lean_uint64_shift_right(v___x_1680_, v___x_1679_);
                    v___x_1682_ = leanh::lean_unbox_uint64(v___x_1678_);
                    leanh::lean_dec_ref(v___x_1678_);
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
                    leanh::lean_inc(v_bkt_1692_);
                    v___x_1693_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_1667_,
                        v_a_1670_,
                        v_bkt_1692_,
                    );
                    if v___x_1693_ == 0 {
                        leanh::lean_inc_ref(v_buckets_1672_);
                        leanh::lean_inc(v_size_1671_);
                        v_isSharedCheck_1719_ = (!leanh::lean_is_exclusive(v_m_1669_)) as u8;
                        if v_isSharedCheck_1719_ == 0 {
                            v_unused_1720_ = leanh::lean_ctor_get(v_m_1669_, 1);
                            leanh::lean_dec(v_unused_1720_);
                            v_unused_1721_ = leanh::lean_ctor_get(v_m_1669_, 0);
                            leanh::lean_dec(v_unused_1721_);
                            v___x_1695_ = v_m_1669_;
                            v_isShared_1696_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_1669_);
                            v___x_1695_ = leanh::lean_box(0);
                            v_isShared_1696_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1670_);
                        leanh::lean_dec_ref(v_inst_1668_);
                        v___x_1722_ = leanh::lean_box((v___x_1693_) as usize);
                        v___x_1723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1723_, 0, v___x_1722_);
                        leanh::lean_ctor_set(v___x_1723_, 1, v_m_1669_);
                        return v___x_1723_;
                    }
                }
            }
            1 => {
                v___x_1697_ = leanh::lean_box(0);
                v___x_1698_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1699_ = lean_nat_add(v_size_1671_, v___x_1698_);
                leanh::lean_dec(v_size_1671_);
                leanh::lean_inc(v_bkt_1692_);
                v___x_1700_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1700_, 0, v_a_1670_);
                leanh::lean_ctor_set(v___x_1700_, 1, v___x_1697_);
                leanh::lean_ctor_set(v___x_1700_, 2, v_bkt_1692_);
                v_buckets_x27_1701_ = lean_array_uset(v_buckets_1672_, v___x_1691_, v___x_1700_);
                v___x_1702_ = leanh::lean_unsigned_to_nat(4);
                v___x_1703_ = lean_nat_mul(v_size_x27_1699_, v___x_1702_);
                v___x_1704_ = leanh::lean_unsigned_to_nat(3);
                v___x_1705_ = lean_nat_div(v___x_1703_, v___x_1704_);
                leanh::lean_dec(v___x_1703_);
                v___x_1706_ = lean_array_get_size(v_buckets_x27_1701_);
                v___x_1707_ = lean_nat_dec_le(v___x_1705_, v___x_1706_);
                leanh::lean_dec(v___x_1705_);
                if v___x_1707_ == 0 {
                    v_val_1708_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_1668_,
                        v_buckets_x27_1701_,
                    );
                    if v_isShared_1696_ == 0 {
                        leanh::lean_ctor_set(v___x_1695_, 1, v_val_1708_);
                        leanh::lean_ctor_set(v___x_1695_, 0, v_size_x27_1699_);
                        v___x_1710_ = v___x_1695_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1713_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_size_x27_1699_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_val_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1713_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1668_);
                    if v_isShared_1696_ == 0 {
                        leanh::lean_ctor_set(v___x_1695_, 1, v_buckets_x27_1701_);
                        leanh::lean_ctor_set(v___x_1695_, 0, v_size_x27_1699_);
                        v___x_1715_ = v___x_1695_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_size_x27_1699_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_buckets_x27_1701_);
                        v___x_1715_ = v_reuseFailAlloc_1718_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1711_ = leanh::lean_box((v___x_1693_) as usize);
                v___x_1712_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1712_, 0, v___x_1711_);
                leanh::lean_ctor_set(v___x_1712_, 1, v___x_1710_);
                return v___x_1712_;
            }
            3 => {
                v___x_1716_ = leanh::lean_box((v___x_1693_) as usize);
                v___x_1717_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1717_, 0, v___x_1716_);
                leanh::lean_ctor_set(v___x_1717_, 1, v___x_1715_);
                return v___x_1717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_contains___redArg(
    mut v_inst_1724_: *mut leanh::LeanObject,
    mut v_inst_1725_: *mut leanh::LeanObject,
    mut v_m_1726_: *mut leanh::LeanObject,
    mut v_a_1727_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    v_buckets_1728_ = leanh::lean_ctor_get(v_m_1726_, 1);
    v___x_1729_ = leanh::lean_unsigned_to_nat(0);
    v___x_1730_ = lean_array_get_size(v_buckets_1728_);
    v___x_1731_ = lean_nat_dec_lt(v___x_1729_, v___x_1730_);
    if v___x_1731_ == 0 {
        leanh::lean_dec(v_a_1727_);
        leanh::lean_dec_ref(v_inst_1725_);
        leanh::lean_dec_ref(v_inst_1724_);
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
    mut v_inst_1733_: *mut leanh::LeanObject,
    mut v_inst_1734_: *mut leanh::LeanObject,
    mut v_m_1735_: *mut leanh::LeanObject,
    mut v_a_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1737_: u8 = 0;
    let mut v_r_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1737_ =
        l_Std_HashSet_Raw_contains___redArg(v_inst_1733_, v_inst_1734_, v_m_1735_, v_a_1736_);
    leanh::lean_dec_ref(v_m_1735_);
    v_r_1738_ = leanh::lean_box((v_res_1737_) as usize);
    return v_r_1738_;
}
pub unsafe fn l_Std_HashSet_Raw_contains(
    mut v_00_u03b1_1739_: *mut leanh::LeanObject,
    mut v_inst_1740_: *mut leanh::LeanObject,
    mut v_inst_1741_: *mut leanh::LeanObject,
    mut v_m_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    v_buckets_1744_ = leanh::lean_ctor_get(v_m_1742_, 1);
    v___x_1745_ = leanh::lean_unsigned_to_nat(0);
    v___x_1746_ = lean_array_get_size(v_buckets_1744_);
    v___x_1747_ = lean_nat_dec_lt(v___x_1745_, v___x_1746_);
    if v___x_1747_ == 0 {
        leanh::lean_dec(v_a_1743_);
        leanh::lean_dec_ref(v_inst_1741_);
        leanh::lean_dec_ref(v_inst_1740_);
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
    mut v_00_u03b1_1749_: *mut leanh::LeanObject,
    mut v_inst_1750_: *mut leanh::LeanObject,
    mut v_inst_1751_: *mut leanh::LeanObject,
    mut v_m_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1754_: u8 = 0;
    let mut v_r_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Std_HashSet_Raw_contains(
        v_00_u03b1_1749_,
        v_inst_1750_,
        v_inst_1751_,
        v_m_1752_,
        v_a_1753_,
    );
    leanh::lean_dec_ref(v_m_1752_);
    v_r_1755_ = leanh::lean_box((v_res_1754_) as usize);
    return v_r_1755_;
}
pub unsafe fn l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(
    mut v_00_u03b1_1756_: *mut leanh::LeanObject,
    mut v_inst_1757_: *mut leanh::LeanObject,
    mut v_inst_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ = leanh::lean_box(0);
    return v___x_1759_;
}
pub unsafe fn l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(
    mut v_00_u03b1_1760_: *mut leanh::LeanObject,
    mut v_inst_1761_: *mut leanh::LeanObject,
    mut v_inst_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(
        v_00_u03b1_1760_,
        v_inst_1761_,
        v_inst_1762_,
    );
    leanh::lean_dec_ref(v_inst_1762_);
    leanh::lean_dec_ref(v_inst_1761_);
    return v_res_1763_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem___redArg(
    mut v_inst_1764_: *mut leanh::LeanObject,
    mut v_inst_1765_: *mut leanh::LeanObject,
    mut v_m_1766_: *mut leanh::LeanObject,
    mut v_a_1767_: *mut leanh::LeanObject,
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
    mut v_inst_1769_: *mut leanh::LeanObject,
    mut v_inst_1770_: *mut leanh::LeanObject,
    mut v_m_1771_: *mut leanh::LeanObject,
    mut v_a_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1773_: u8 = 0;
    let mut v_r_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1773_ = l_Std_HashSet_Raw_instDecidableMem___redArg(
        v_inst_1769_,
        v_inst_1770_,
        v_m_1771_,
        v_a_1772_,
    );
    leanh::lean_dec_ref(v_m_1771_);
    v_r_1774_ = leanh::lean_box((v_res_1773_) as usize);
    return v_r_1774_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem(
    mut v_00_u03b1_1775_: *mut leanh::LeanObject,
    mut v_inst_1776_: *mut leanh::LeanObject,
    mut v_inst_1777_: *mut leanh::LeanObject,
    mut v_m_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_1781_: *mut leanh::LeanObject,
    mut v_inst_1782_: *mut leanh::LeanObject,
    mut v_inst_1783_: *mut leanh::LeanObject,
    mut v_m_1784_: *mut leanh::LeanObject,
    mut v_a_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1786_: u8 = 0;
    let mut v_r_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Std_HashSet_Raw_instDecidableMem(
        v_00_u03b1_1781_,
        v_inst_1782_,
        v_inst_1783_,
        v_m_1784_,
        v_a_1785_,
    );
    leanh::lean_dec_ref(v_m_1784_);
    v_r_1787_ = leanh::lean_box((v_res_1786_) as usize);
    return v_r_1787_;
}
pub unsafe fn l_Std_HashSet_Raw_erase___redArg(
    mut v_inst_1788_: *mut leanh::LeanObject,
    mut v_inst_1789_: *mut leanh::LeanObject,
    mut v_m_1790_: *mut leanh::LeanObject,
    mut v_a_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: u8 = 0;
    v_buckets_1792_ = leanh::lean_ctor_get(v_m_1790_, 1);
    v___x_1793_ = leanh::lean_unsigned_to_nat(0);
    v___x_1794_ = lean_array_get_size(v_buckets_1792_);
    v___x_1795_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
    if v___x_1795_ == 0 {
        leanh::lean_dec(v_a_1791_);
        leanh::lean_dec_ref(v_inst_1789_);
        leanh::lean_dec_ref(v_inst_1788_);
        return v_m_1790_;
    } else {
        let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1797_: *mut leanh::LeanObject,
    mut v_inst_1798_: *mut leanh::LeanObject,
    mut v_inst_1799_: *mut leanh::LeanObject,
    mut v_m_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    v_buckets_1802_ = leanh::lean_ctor_get(v_m_1800_, 1);
    v___x_1803_ = leanh::lean_unsigned_to_nat(0);
    v___x_1804_ = lean_array_get_size(v_buckets_1802_);
    v___x_1805_ = lean_nat_dec_lt(v___x_1803_, v___x_1804_);
    if v___x_1805_ == 0 {
        leanh::lean_dec(v_a_1801_);
        leanh::lean_dec_ref(v_inst_1799_);
        leanh::lean_dec_ref(v_inst_1798_);
        return v_m_1800_;
    } else {
        let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_1808_ = leanh::lean_ctor_get(v_m_1807_, 0);
    leanh::lean_inc(v_size_1808_);
    return v_size_1808_;
}
pub unsafe fn l_Std_HashSet_Raw_size___redArg___boxed(
    mut v_m_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Std_HashSet_Raw_size___redArg(v_m_1809_);
    leanh::lean_dec_ref(v_m_1809_);
    return v_res_1810_;
}
pub unsafe fn l_Std_HashSet_Raw_size(
    mut v_00_u03b1_1811_: *mut leanh::LeanObject,
    mut v_m_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_1813_ = leanh::lean_ctor_get(v_m_1812_, 0);
    leanh::lean_inc(v_size_1813_);
    return v_size_1813_;
}
pub unsafe fn l_Std_HashSet_Raw_size___boxed(
    mut v_00_u03b1_1814_: *mut leanh::LeanObject,
    mut v_m_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Std_HashSet_Raw_size(v_00_u03b1_1814_, v_m_1815_);
    leanh::lean_dec_ref(v_m_1815_);
    return v_res_1816_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f___redArg(
    mut v_inst_1817_: *mut leanh::LeanObject,
    mut v_inst_1818_: *mut leanh::LeanObject,
    mut v_m_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    v_buckets_1821_ = leanh::lean_ctor_get(v_m_1819_, 1);
    v___x_1822_ = leanh::lean_unsigned_to_nat(0);
    v___x_1823_ = lean_array_get_size(v_buckets_1821_);
    v___x_1824_ = lean_nat_dec_lt(v___x_1822_, v___x_1823_);
    if v___x_1824_ == 0 {
        let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1820_);
        leanh::lean_dec_ref(v_inst_1818_);
        leanh::lean_dec_ref(v_inst_1817_);
        v___x_1825_ = leanh::lean_box(0);
        return v___x_1825_;
    } else {
        let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1827_: *mut leanh::LeanObject,
    mut v_inst_1828_: *mut leanh::LeanObject,
    mut v_m_1829_: *mut leanh::LeanObject,
    mut v_a_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1831_ =
        l_Std_HashSet_Raw_get_x3f___redArg(v_inst_1827_, v_inst_1828_, v_m_1829_, v_a_1830_);
    leanh::lean_dec_ref(v_m_1829_);
    return v_res_1831_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f(
    mut v_00_u03b1_1832_: *mut leanh::LeanObject,
    mut v_inst_1833_: *mut leanh::LeanObject,
    mut v_inst_1834_: *mut leanh::LeanObject,
    mut v_m_1835_: *mut leanh::LeanObject,
    mut v_a_1836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    v_buckets_1837_ = leanh::lean_ctor_get(v_m_1835_, 1);
    v___x_1838_ = leanh::lean_unsigned_to_nat(0);
    v___x_1839_ = lean_array_get_size(v_buckets_1837_);
    v___x_1840_ = lean_nat_dec_lt(v___x_1838_, v___x_1839_);
    if v___x_1840_ == 0 {
        let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1836_);
        leanh::lean_dec_ref(v_inst_1834_);
        leanh::lean_dec_ref(v_inst_1833_);
        v___x_1841_ = leanh::lean_box(0);
        return v___x_1841_;
    } else {
        let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1843_: *mut leanh::LeanObject,
    mut v_inst_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_m_1846_: *mut leanh::LeanObject,
    mut v_a_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_HashSet_Raw_get_x3f(
        v_00_u03b1_1843_,
        v_inst_1844_,
        v_inst_1845_,
        v_m_1846_,
        v_a_1847_,
    );
    leanh::lean_dec_ref(v_m_1846_);
    return v_res_1848_;
}
pub unsafe fn l_Std_HashSet_Raw_get___redArg(
    mut v_inst_1849_: *mut leanh::LeanObject,
    mut v_inst_1850_: *mut leanh::LeanObject,
    mut v_m_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1849_,
        v_inst_1850_,
        v_m_1851_,
        v_a_1852_,
    );
    return v___x_1853_;
}
pub unsafe fn l_Std_HashSet_Raw_get___redArg___boxed(
    mut v_inst_1854_: *mut leanh::LeanObject,
    mut v_inst_1855_: *mut leanh::LeanObject,
    mut v_m_1856_: *mut leanh::LeanObject,
    mut v_a_1857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_Std_HashSet_Raw_get___redArg(v_inst_1854_, v_inst_1855_, v_m_1856_, v_a_1857_);
    leanh::lean_dec_ref(v_m_1856_);
    return v_res_1858_;
}
pub unsafe fn l_Std_HashSet_Raw_get(
    mut v_00_u03b1_1859_: *mut leanh::LeanObject,
    mut v_inst_1860_: *mut leanh::LeanObject,
    mut v_inst_1861_: *mut leanh::LeanObject,
    mut v_m_1862_: *mut leanh::LeanObject,
    mut v_a_1863_: *mut leanh::LeanObject,
    mut v_h_1864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1860_,
        v_inst_1861_,
        v_m_1862_,
        v_a_1863_,
    );
    return v___x_1865_;
}
pub unsafe fn l_Std_HashSet_Raw_get___boxed(
    mut v_00_u03b1_1866_: *mut leanh::LeanObject,
    mut v_inst_1867_: *mut leanh::LeanObject,
    mut v_inst_1868_: *mut leanh::LeanObject,
    mut v_m_1869_: *mut leanh::LeanObject,
    mut v_a_1870_: *mut leanh::LeanObject,
    mut v_h_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Std_HashSet_Raw_get(
        v_00_u03b1_1866_,
        v_inst_1867_,
        v_inst_1868_,
        v_m_1869_,
        v_a_1870_,
        v_h_1871_,
    );
    leanh::lean_dec_ref(v_m_1869_);
    return v_res_1872_;
}
pub unsafe fn l_Std_HashSet_Raw_getD___redArg(
    mut v_inst_1873_: *mut leanh::LeanObject,
    mut v_inst_1874_: *mut leanh::LeanObject,
    mut v_m_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
    mut v_fallback_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    v_buckets_1878_ = leanh::lean_ctor_get(v_m_1875_, 1);
    v___x_1879_ = leanh::lean_unsigned_to_nat(0);
    v___x_1880_ = lean_array_get_size(v_buckets_1878_);
    v___x_1881_ = lean_nat_dec_lt(v___x_1879_, v___x_1880_);
    if v___x_1881_ == 0 {
        leanh::lean_dec(v_a_1876_);
        leanh::lean_dec_ref(v_inst_1874_);
        leanh::lean_dec_ref(v_inst_1873_);
        leanh::lean_inc(v_fallback_1877_);
        return v_fallback_1877_;
    } else {
        let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1883_: *mut leanh::LeanObject,
    mut v_inst_1884_: *mut leanh::LeanObject,
    mut v_m_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
    mut v_fallback_1887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Std_HashSet_Raw_getD___redArg(
        v_inst_1883_,
        v_inst_1884_,
        v_m_1885_,
        v_a_1886_,
        v_fallback_1887_,
    );
    leanh::lean_dec(v_fallback_1887_);
    leanh::lean_dec_ref(v_m_1885_);
    return v_res_1888_;
}
pub unsafe fn l_Std_HashSet_Raw_getD(
    mut v_00_u03b1_1889_: *mut leanh::LeanObject,
    mut v_inst_1890_: *mut leanh::LeanObject,
    mut v_inst_1891_: *mut leanh::LeanObject,
    mut v_m_1892_: *mut leanh::LeanObject,
    mut v_a_1893_: *mut leanh::LeanObject,
    mut v_fallback_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u8 = 0;
    v_buckets_1895_ = leanh::lean_ctor_get(v_m_1892_, 1);
    v___x_1896_ = leanh::lean_unsigned_to_nat(0);
    v___x_1897_ = lean_array_get_size(v_buckets_1895_);
    v___x_1898_ = lean_nat_dec_lt(v___x_1896_, v___x_1897_);
    if v___x_1898_ == 0 {
        leanh::lean_dec(v_a_1893_);
        leanh::lean_dec_ref(v_inst_1891_);
        leanh::lean_dec_ref(v_inst_1890_);
        leanh::lean_inc(v_fallback_1894_);
        return v_fallback_1894_;
    } else {
        let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1900_: *mut leanh::LeanObject,
    mut v_inst_1901_: *mut leanh::LeanObject,
    mut v_inst_1902_: *mut leanh::LeanObject,
    mut v_m_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
    mut v_fallback_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Std_HashSet_Raw_getD(
        v_00_u03b1_1900_,
        v_inst_1901_,
        v_inst_1902_,
        v_m_1903_,
        v_a_1904_,
        v_fallback_1905_,
    );
    leanh::lean_dec(v_fallback_1905_);
    leanh::lean_dec_ref(v_m_1903_);
    return v_res_1906_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x21___redArg(
    mut v_inst_1907_: *mut leanh::LeanObject,
    mut v_inst_1908_: *mut leanh::LeanObject,
    mut v_inst_1909_: *mut leanh::LeanObject,
    mut v_m_1910_: *mut leanh::LeanObject,
    mut v_a_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    v_buckets_1912_ = leanh::lean_ctor_get(v_m_1910_, 1);
    v___x_1913_ = leanh::lean_unsigned_to_nat(0);
    v___x_1914_ = lean_array_get_size(v_buckets_1912_);
    v___x_1915_ = lean_nat_dec_lt(v___x_1913_, v___x_1914_);
    if v___x_1915_ == 0 {
        leanh::lean_dec(v_a_1911_);
        leanh::lean_dec_ref(v_inst_1908_);
        leanh::lean_dec_ref(v_inst_1907_);
        leanh::lean_inc(v_inst_1909_);
        return v_inst_1909_;
    } else {
        let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1917_: *mut leanh::LeanObject,
    mut v_inst_1918_: *mut leanh::LeanObject,
    mut v_inst_1919_: *mut leanh::LeanObject,
    mut v_m_1920_: *mut leanh::LeanObject,
    mut v_a_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_HashSet_Raw_get_x21___redArg(
        v_inst_1917_,
        v_inst_1918_,
        v_inst_1919_,
        v_m_1920_,
        v_a_1921_,
    );
    leanh::lean_dec_ref(v_m_1920_);
    leanh::lean_dec(v_inst_1919_);
    return v_res_1922_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x21(
    mut v_00_u03b1_1923_: *mut leanh::LeanObject,
    mut v_inst_1924_: *mut leanh::LeanObject,
    mut v_inst_1925_: *mut leanh::LeanObject,
    mut v_inst_1926_: *mut leanh::LeanObject,
    mut v_m_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    v_buckets_1929_ = leanh::lean_ctor_get(v_m_1927_, 1);
    v___x_1930_ = leanh::lean_unsigned_to_nat(0);
    v___x_1931_ = lean_array_get_size(v_buckets_1929_);
    v___x_1932_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
    if v___x_1932_ == 0 {
        leanh::lean_dec(v_a_1928_);
        leanh::lean_dec_ref(v_inst_1925_);
        leanh::lean_dec_ref(v_inst_1924_);
        leanh::lean_inc(v_inst_1926_);
        return v_inst_1926_;
    } else {
        let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1934_: *mut leanh::LeanObject,
    mut v_inst_1935_: *mut leanh::LeanObject,
    mut v_inst_1936_: *mut leanh::LeanObject,
    mut v_inst_1937_: *mut leanh::LeanObject,
    mut v_m_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Std_HashSet_Raw_get_x21(
        v_00_u03b1_1934_,
        v_inst_1935_,
        v_inst_1936_,
        v_inst_1937_,
        v_m_1938_,
        v_a_1939_,
    );
    leanh::lean_dec_ref(v_m_1938_);
    leanh::lean_dec(v_inst_1937_);
    return v_res_1940_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___redArg(
    mut v_m_1941_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    v_size_1942_ = leanh::lean_ctor_get(v_m_1941_, 0);
    v___x_1943_ = leanh::lean_unsigned_to_nat(0);
    v___x_1944_ = lean_nat_dec_eq(v_size_1942_, v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___redArg___boxed(
    mut v_m_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1946_: u8 = 0;
    let mut v_r_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1946_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_1945_);
    leanh::lean_dec_ref(v_m_1945_);
    v_r_1947_ = leanh::lean_box((v_res_1946_) as usize);
    return v_r_1947_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty(
    mut v_00_u03b1_1948_: *mut leanh::LeanObject,
    mut v_m_1949_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    v_size_1950_ = leanh::lean_ctor_get(v_m_1949_, 0);
    v___x_1951_ = leanh::lean_unsigned_to_nat(0);
    v___x_1952_ = lean_nat_dec_eq(v_size_1950_, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___boxed(
    mut v_00_u03b1_1953_: *mut leanh::LeanObject,
    mut v_m_1954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1955_: u8 = 0;
    let mut v_r_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_1953_, v_m_1954_);
    leanh::lean_dec_ref(v_m_1954_);
    v_r_1956_ = leanh::lean_box((v_res_1955_) as usize);
    return v_r_1956_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg___lam__0(
    mut v_a_1957_: *mut leanh::LeanObject,
    mut v_b_1958_: *mut leanh::LeanObject,
    mut v_d_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1960_, 0, v_a_1957_);
    leanh::lean_ctor_set(v___x_1960_, 1, v_d_1959_);
    return v___x_1960_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg___lam__1(
    mut v___x_1961_: *mut leanh::LeanObject,
    mut v___f_1962_: *mut leanh::LeanObject,
    mut v_l_1963_: *mut leanh::LeanObject,
    mut v_acc_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1961_,
        v___f_1962_,
        v_acc_1964_,
        v_l_1963_,
    );
    return v___x_1965_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg(
    mut v_m_1989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    v___x_1990_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_1991_ = leanh::lean_ctor_get(v_m_1989_, 1);
    leanh::lean_inc_ref(v_buckets_1991_);
    leanh::lean_dec_ref(v_m_1989_);
    v___x_1992_ = leanh::lean_box(0);
    v___x_1993_ = lean_array_get_size(v_buckets_1991_);
    v___x_1994_ = leanh::lean_unsigned_to_nat(0);
    v___x_1995_ = lean_nat_dec_lt(v___x_1994_, v___x_1993_);
    if v___x_1995_ == 0 {
        leanh::lean_dec_ref(v_buckets_1991_);
        return v___x_1992_;
    } else {
        let mut v___f_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: usize = 0;
        let mut v___x_1998_: usize = 0;
        let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1996_ = l_Std_HashSet_Raw_toList___redArg___closed__11;
        v___x_1997_ = lean_usize_of_nat(v___x_1993_);
        v___x_1998_ = 0usize;
        v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_2000_: *mut leanh::LeanObject,
    mut v_m_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    v___x_2002_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2003_ = leanh::lean_ctor_get(v_m_2001_, 1);
    leanh::lean_inc_ref(v_buckets_2003_);
    leanh::lean_dec_ref(v_m_2001_);
    v___x_2004_ = leanh::lean_box(0);
    v___x_2005_ = lean_array_get_size(v_buckets_2003_);
    v___x_2006_ = leanh::lean_unsigned_to_nat(0);
    v___x_2007_ = lean_nat_dec_lt(v___x_2006_, v___x_2005_);
    if v___x_2007_ == 0 {
        leanh::lean_dec_ref(v_buckets_2003_);
        return v___x_2004_;
    } else {
        let mut v___f_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: usize = 0;
        let mut v___x_2010_: usize = 0;
        let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2008_ = l_Std_HashSet_Raw_toList___redArg___closed__11;
        v___x_2009_ = lean_usize_of_nat(v___x_2005_);
        v___x_2010_ = 0usize;
        v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_inst_2016_: *mut leanh::LeanObject,
    mut v_inst_2017_: *mut leanh::LeanObject,
    mut v_l_2018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: u8 = 0;
    v___x_2019_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2020_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2020_ == 0 {
        leanh::lean_dec(v_l_2018_);
        leanh::lean_dec_ref(v_inst_2017_);
        leanh::lean_dec_ref(v_inst_2016_);
        return v___x_2019_;
    } else {
        let mut v___f_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2023_: *mut leanh::LeanObject,
    mut v_inst_2024_: *mut leanh::LeanObject,
    mut v_inst_2025_: *mut leanh::LeanObject,
    mut v_l_2026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    v___x_2027_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2028_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2028_ == 0 {
        leanh::lean_dec(v_l_2026_);
        leanh::lean_dec_ref(v_inst_2025_);
        leanh::lean_dec_ref(v_inst_2024_);
        return v___x_2027_;
    } else {
        let mut v___f_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_f_2031_: *mut leanh::LeanObject,
    mut v_b_2032_: *mut leanh::LeanObject,
    mut v_a_2033_: *mut leanh::LeanObject,
    mut v_x_2034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = leanh::lean_apply_2(v_f_2031_, v_b_2032_, v_a_2033_);
    return v___x_2035_;
}
pub unsafe fn l_Std_HashSet_Raw_foldM___redArg___lam__1(
    mut v_inst_2036_: *mut leanh::LeanObject,
    mut v___f_2037_: *mut leanh::LeanObject,
    mut v_acc_2038_: *mut leanh::LeanObject,
    mut v_l_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2040_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2036_,
        v___f_2037_,
        v_acc_2038_,
        v_l_2039_,
    );
    return v___x_2040_;
}
pub unsafe fn l_Std_HashSet_Raw_foldM___redArg(
    mut v_inst_2041_: *mut leanh::LeanObject,
    mut v_f_2042_: *mut leanh::LeanObject,
    mut v_init_2043_: *mut leanh::LeanObject,
    mut v_b_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: u8 = 0;
    v_buckets_2045_ = leanh::lean_ctor_get(v_b_2044_, 1);
    leanh::lean_inc_ref(v_buckets_2045_);
    leanh::lean_dec_ref(v_b_2044_);
    v___x_2046_ = leanh::lean_unsigned_to_nat(0);
    v___x_2047_ = lean_array_get_size(v_buckets_2045_);
    v___x_2048_ = lean_nat_dec_lt(v___x_2046_, v___x_2047_);
    if v___x_2048_ == 0 {
        let mut v_toApplicative_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2045_);
        leanh::lean_dec(v_f_2042_);
        v_toApplicative_2049_ = leanh::lean_ctor_get(v_inst_2041_, 0);
        leanh::lean_inc_ref(v_toApplicative_2049_);
        leanh::lean_dec_ref(v_inst_2041_);
        v_toPure_2050_ = leanh::lean_ctor_get(v_toApplicative_2049_, 1);
        leanh::lean_inc(v_toPure_2050_);
        leanh::lean_dec_ref(v_toApplicative_2049_);
        v___x_2051_ =
            leanh::lean_apply_2(v_toPure_2050_, leanh::lean_box(0), v_init_2043_);
        return v___x_2051_;
    } else {
        let mut v___f_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: u8 = 0;
        v___f_2052_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2052_, 0, v_f_2042_);
        leanh::lean_inc_ref(v_inst_2041_);
        v___f_2053_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2053_, 0, v_inst_2041_);
        leanh::lean_closure_set(v___f_2053_, 1, v___f_2052_);
        v___x_2054_ = lean_nat_dec_le(v___x_2047_, v___x_2047_);
        if v___x_2054_ == 0 {
            if v___x_2048_ == 0 {
                let mut v_toApplicative_2055_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2053_);
                leanh::lean_dec_ref(v_buckets_2045_);
                v_toApplicative_2055_ = leanh::lean_ctor_get(v_inst_2041_, 0);
                leanh::lean_inc_ref(v_toApplicative_2055_);
                leanh::lean_dec_ref(v_inst_2041_);
                v_toPure_2056_ = leanh::lean_ctor_get(v_toApplicative_2055_, 1);
                leanh::lean_inc(v_toPure_2056_);
                leanh::lean_dec_ref(v_toApplicative_2055_);
                v___x_2057_ = leanh::lean_apply_2(
                    v_toPure_2056_,
                    leanh::lean_box(0),
                    v_init_2043_,
                );
                return v___x_2057_;
            } else {
                let mut v___x_2058_: usize = 0;
                let mut v___x_2059_: usize = 0;
                let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2058_ = 0usize;
                v___x_2059_ = lean_usize_of_nat(v___x_2047_);
                v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2061_ = 0usize;
            v___x_2062_ = lean_usize_of_nat(v___x_2047_);
            v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_2064_: *mut leanh::LeanObject,
    mut v_m_2065_: *mut leanh::LeanObject,
    mut v_inst_2066_: *mut leanh::LeanObject,
    mut v_00_u03b2_2067_: *mut leanh::LeanObject,
    mut v_f_2068_: *mut leanh::LeanObject,
    mut v_init_2069_: *mut leanh::LeanObject,
    mut v_b_2070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    v_buckets_2071_ = leanh::lean_ctor_get(v_b_2070_, 1);
    leanh::lean_inc_ref(v_buckets_2071_);
    leanh::lean_dec_ref(v_b_2070_);
    v___x_2072_ = leanh::lean_unsigned_to_nat(0);
    v___x_2073_ = lean_array_get_size(v_buckets_2071_);
    v___x_2074_ = lean_nat_dec_lt(v___x_2072_, v___x_2073_);
    if v___x_2074_ == 0 {
        let mut v_toApplicative_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2071_);
        leanh::lean_dec(v_f_2068_);
        v_toApplicative_2075_ = leanh::lean_ctor_get(v_inst_2066_, 0);
        leanh::lean_inc_ref(v_toApplicative_2075_);
        leanh::lean_dec_ref(v_inst_2066_);
        v_toPure_2076_ = leanh::lean_ctor_get(v_toApplicative_2075_, 1);
        leanh::lean_inc(v_toPure_2076_);
        leanh::lean_dec_ref(v_toApplicative_2075_);
        v___x_2077_ =
            leanh::lean_apply_2(v_toPure_2076_, leanh::lean_box(0), v_init_2069_);
        return v___x_2077_;
    } else {
        let mut v___f_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: u8 = 0;
        v___f_2078_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2078_, 0, v_f_2068_);
        leanh::lean_inc_ref(v_inst_2066_);
        v___f_2079_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2079_, 0, v_inst_2066_);
        leanh::lean_closure_set(v___f_2079_, 1, v___f_2078_);
        v___x_2080_ = lean_nat_dec_le(v___x_2073_, v___x_2073_);
        if v___x_2080_ == 0 {
            if v___x_2074_ == 0 {
                let mut v_toApplicative_2081_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2079_);
                leanh::lean_dec_ref(v_buckets_2071_);
                v_toApplicative_2081_ = leanh::lean_ctor_get(v_inst_2066_, 0);
                leanh::lean_inc_ref(v_toApplicative_2081_);
                leanh::lean_dec_ref(v_inst_2066_);
                v_toPure_2082_ = leanh::lean_ctor_get(v_toApplicative_2081_, 1);
                leanh::lean_inc(v_toPure_2082_);
                leanh::lean_dec_ref(v_toApplicative_2081_);
                v___x_2083_ = leanh::lean_apply_2(
                    v_toPure_2082_,
                    leanh::lean_box(0),
                    v_init_2069_,
                );
                return v___x_2083_;
            } else {
                let mut v___x_2084_: usize = 0;
                let mut v___x_2085_: usize = 0;
                let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2084_ = 0usize;
                v___x_2085_ = lean_usize_of_nat(v___x_2073_);
                v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2087_ = 0usize;
            v___x_2088_ = lean_usize_of_nat(v___x_2073_);
            v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_f_2090_: *mut leanh::LeanObject,
    mut v_x1_2091_: *mut leanh::LeanObject,
    mut v_x2_2092_: *mut leanh::LeanObject,
    mut v_x3_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = leanh::lean_apply_2(v_f_2090_, v_x1_2091_, v_x2_2092_);
    return v___x_2094_;
}
pub unsafe fn l_Std_HashSet_Raw_fold___redArg___lam__1(
    mut v___x_2095_: *mut leanh::LeanObject,
    mut v___f_2096_: *mut leanh::LeanObject,
    mut v_acc_2097_: *mut leanh::LeanObject,
    mut v_l_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2099_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2095_,
        v___f_2096_,
        v_acc_2097_,
        v_l_2098_,
    );
    return v___x_2099_;
}
pub unsafe fn l_Std_HashSet_Raw_fold___redArg(
    mut v_f_2100_: *mut leanh::LeanObject,
    mut v_init_2101_: *mut leanh::LeanObject,
    mut v_m_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: u8 = 0;
    v___x_2103_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2104_ = leanh::lean_ctor_get(v_m_2102_, 1);
    leanh::lean_inc_ref(v_buckets_2104_);
    leanh::lean_dec_ref(v_m_2102_);
    v___x_2105_ = leanh::lean_unsigned_to_nat(0);
    v___x_2106_ = lean_array_get_size(v_buckets_2104_);
    v___x_2107_ = lean_nat_dec_lt(v___x_2105_, v___x_2106_);
    if v___x_2107_ == 0 {
        leanh::lean_dec_ref(v_buckets_2104_);
        leanh::lean_dec(v_f_2100_);
        return v_init_2101_;
    } else {
        let mut v___f_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: u8 = 0;
        v___f_2108_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2108_, 0, v_f_2100_);
        v___f_2109_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2109_, 0, v___x_2103_);
        leanh::lean_closure_set(v___f_2109_, 1, v___f_2108_);
        v___x_2110_ = lean_nat_dec_le(v___x_2106_, v___x_2106_);
        if v___x_2110_ == 0 {
            if v___x_2107_ == 0 {
                leanh::lean_dec_ref(v___f_2109_);
                leanh::lean_dec_ref(v_buckets_2104_);
                return v_init_2101_;
            } else {
                let mut v___x_2111_: usize = 0;
                let mut v___x_2112_: usize = 0;
                let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2111_ = 0usize;
                v___x_2112_ = lean_usize_of_nat(v___x_2106_);
                v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2114_ = 0usize;
            v___x_2115_ = lean_usize_of_nat(v___x_2106_);
            v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_2117_: *mut leanh::LeanObject,
    mut v_00_u03b2_2118_: *mut leanh::LeanObject,
    mut v_f_2119_: *mut leanh::LeanObject,
    mut v_init_2120_: *mut leanh::LeanObject,
    mut v_m_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    v___x_2122_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2123_ = leanh::lean_ctor_get(v_m_2121_, 1);
    leanh::lean_inc_ref(v_buckets_2123_);
    leanh::lean_dec_ref(v_m_2121_);
    v___x_2124_ = leanh::lean_unsigned_to_nat(0);
    v___x_2125_ = lean_array_get_size(v_buckets_2123_);
    v___x_2126_ = lean_nat_dec_lt(v___x_2124_, v___x_2125_);
    if v___x_2126_ == 0 {
        leanh::lean_dec_ref(v_buckets_2123_);
        leanh::lean_dec(v_f_2119_);
        return v_init_2120_;
    } else {
        let mut v___f_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2129_: u8 = 0;
        v___f_2127_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2127_, 0, v_f_2119_);
        v___f_2128_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2128_, 0, v___x_2122_);
        leanh::lean_closure_set(v___f_2128_, 1, v___f_2127_);
        v___x_2129_ = lean_nat_dec_le(v___x_2125_, v___x_2125_);
        if v___x_2129_ == 0 {
            if v___x_2126_ == 0 {
                leanh::lean_dec_ref(v___f_2128_);
                leanh::lean_dec_ref(v_buckets_2123_);
                return v_init_2120_;
            } else {
                let mut v___x_2130_: usize = 0;
                let mut v___x_2131_: usize = 0;
                let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2130_ = 0usize;
                v___x_2131_ = lean_usize_of_nat(v___x_2125_);
                v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2133_ = 0usize;
            v___x_2134_ = lean_usize_of_nat(v___x_2125_);
            v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_f_2136_: *mut leanh::LeanObject,
    mut v_x_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = leanh::lean_apply_1(v_f_2136_, v___y_2138_);
    return v___x_2140_;
}
pub unsafe fn l_Std_HashSet_Raw_forM___redArg___lam__1(
    mut v_inst_2141_: *mut leanh::LeanObject,
    mut v___f_2142_: *mut leanh::LeanObject,
    mut v_x_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2145_ = leanh::lean_box(0);
    v___x_2146_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2141_,
        v___f_2142_,
        v___x_2145_,
        v___y_2144_,
    );
    return v___x_2146_;
}
pub unsafe fn l_Std_HashSet_Raw_forM___redArg(
    mut v_inst_2147_: *mut leanh::LeanObject,
    mut v_f_2148_: *mut leanh::LeanObject,
    mut v_b_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    v_buckets_2150_ = leanh::lean_ctor_get(v_b_2149_, 1);
    leanh::lean_inc_ref(v_buckets_2150_);
    leanh::lean_dec_ref(v_b_2149_);
    v___x_2151_ = leanh::lean_unsigned_to_nat(0);
    v___x_2152_ = lean_array_get_size(v_buckets_2150_);
    v___x_2153_ = leanh::lean_box(0);
    v___x_2154_ = lean_nat_dec_lt(v___x_2151_, v___x_2152_);
    if v___x_2154_ == 0 {
        let mut v_toApplicative_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2150_);
        leanh::lean_dec(v_f_2148_);
        v_toApplicative_2155_ = leanh::lean_ctor_get(v_inst_2147_, 0);
        leanh::lean_inc_ref(v_toApplicative_2155_);
        leanh::lean_dec_ref(v_inst_2147_);
        v_toPure_2156_ = leanh::lean_ctor_get(v_toApplicative_2155_, 1);
        leanh::lean_inc(v_toPure_2156_);
        leanh::lean_dec_ref(v_toApplicative_2155_);
        v___x_2157_ =
            leanh::lean_apply_2(v_toPure_2156_, leanh::lean_box(0), v___x_2153_);
        return v___x_2157_;
    } else {
        let mut v___f_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: u8 = 0;
        v___f_2158_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2158_, 0, v_f_2148_);
        leanh::lean_inc_ref(v_inst_2147_);
        v___f_2159_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2159_, 0, v_inst_2147_);
        leanh::lean_closure_set(v___f_2159_, 1, v___f_2158_);
        v___x_2160_ = lean_nat_dec_le(v___x_2152_, v___x_2152_);
        if v___x_2160_ == 0 {
            if v___x_2154_ == 0 {
                let mut v_toApplicative_2161_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2159_);
                leanh::lean_dec_ref(v_buckets_2150_);
                v_toApplicative_2161_ = leanh::lean_ctor_get(v_inst_2147_, 0);
                leanh::lean_inc_ref(v_toApplicative_2161_);
                leanh::lean_dec_ref(v_inst_2147_);
                v_toPure_2162_ = leanh::lean_ctor_get(v_toApplicative_2161_, 1);
                leanh::lean_inc(v_toPure_2162_);
                leanh::lean_dec_ref(v_toApplicative_2161_);
                v___x_2163_ = leanh::lean_apply_2(
                    v_toPure_2162_,
                    leanh::lean_box(0),
                    v___x_2153_,
                );
                return v___x_2163_;
            } else {
                let mut v___x_2164_: usize = 0;
                let mut v___x_2165_: usize = 0;
                let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2164_ = 0usize;
                v___x_2165_ = lean_usize_of_nat(v___x_2152_);
                v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2167_ = 0usize;
            v___x_2168_ = lean_usize_of_nat(v___x_2152_);
            v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_2170_: *mut leanh::LeanObject,
    mut v_m_2171_: *mut leanh::LeanObject,
    mut v_inst_2172_: *mut leanh::LeanObject,
    mut v_f_2173_: *mut leanh::LeanObject,
    mut v_b_2174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    v_buckets_2175_ = leanh::lean_ctor_get(v_b_2174_, 1);
    leanh::lean_inc_ref(v_buckets_2175_);
    leanh::lean_dec_ref(v_b_2174_);
    v___x_2176_ = leanh::lean_unsigned_to_nat(0);
    v___x_2177_ = lean_array_get_size(v_buckets_2175_);
    v___x_2178_ = leanh::lean_box(0);
    v___x_2179_ = lean_nat_dec_lt(v___x_2176_, v___x_2177_);
    if v___x_2179_ == 0 {
        let mut v_toApplicative_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2175_);
        leanh::lean_dec(v_f_2173_);
        v_toApplicative_2180_ = leanh::lean_ctor_get(v_inst_2172_, 0);
        leanh::lean_inc_ref(v_toApplicative_2180_);
        leanh::lean_dec_ref(v_inst_2172_);
        v_toPure_2181_ = leanh::lean_ctor_get(v_toApplicative_2180_, 1);
        leanh::lean_inc(v_toPure_2181_);
        leanh::lean_dec_ref(v_toApplicative_2180_);
        v___x_2182_ =
            leanh::lean_apply_2(v_toPure_2181_, leanh::lean_box(0), v___x_2178_);
        return v___x_2182_;
    } else {
        let mut v___f_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: u8 = 0;
        v___f_2183_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2183_, 0, v_f_2173_);
        leanh::lean_inc_ref(v_inst_2172_);
        v___f_2184_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2184_, 0, v_inst_2172_);
        leanh::lean_closure_set(v___f_2184_, 1, v___f_2183_);
        v___x_2185_ = lean_nat_dec_le(v___x_2177_, v___x_2177_);
        if v___x_2185_ == 0 {
            if v___x_2179_ == 0 {
                let mut v_toApplicative_2186_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2184_);
                leanh::lean_dec_ref(v_buckets_2175_);
                v_toApplicative_2186_ = leanh::lean_ctor_get(v_inst_2172_, 0);
                leanh::lean_inc_ref(v_toApplicative_2186_);
                leanh::lean_dec_ref(v_inst_2172_);
                v_toPure_2187_ = leanh::lean_ctor_get(v_toApplicative_2186_, 1);
                leanh::lean_inc(v_toPure_2187_);
                leanh::lean_dec_ref(v_toApplicative_2186_);
                v___x_2188_ = leanh::lean_apply_2(
                    v_toPure_2187_,
                    leanh::lean_box(0),
                    v___x_2178_,
                );
                return v___x_2188_;
            } else {
                let mut v___x_2189_: usize = 0;
                let mut v___x_2190_: usize = 0;
                let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2189_ = 0usize;
                v___x_2190_ = lean_usize_of_nat(v___x_2177_);
                v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2192_ = 0usize;
            v___x_2193_ = lean_usize_of_nat(v___x_2177_);
            v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_f_2195_: *mut leanh::LeanObject,
    mut v_a_2196_: *mut leanh::LeanObject,
    mut v_x_2197_: *mut leanh::LeanObject,
    mut v_acc_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = leanh::lean_apply_2(v_f_2195_, v_a_2196_, v_acc_2198_);
    return v___x_2199_;
}
pub unsafe fn l_Std_HashSet_Raw_forIn___redArg___lam__1(
    mut v_inst_2200_: *mut leanh::LeanObject,
    mut v___f_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_x_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_inst_2200_, v___f_2201_, v_a_2202_, v___y_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Std_HashSet_Raw_forIn___redArg(
    mut v_inst_2206_: *mut leanh::LeanObject,
    mut v_f_2207_: *mut leanh::LeanObject,
    mut v_init_2208_: *mut leanh::LeanObject,
    mut v_b_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2210_ = leanh::lean_ctor_get(v_b_2209_, 1);
    leanh::lean_inc_ref(v_buckets_2210_);
    leanh::lean_dec_ref(v_b_2209_);
    v___f_2211_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2211_, 0, v_f_2207_);
    leanh::lean_inc_ref(v_inst_2206_);
    v___f_2212_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2212_, 0, v_inst_2206_);
    leanh::lean_closure_set(v___f_2212_, 1, v___f_2211_);
    v_sz_2213_ = lean_array_size(v_buckets_2210_);
    v___x_2214_ = 0usize;
    v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
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
    mut v_00_u03b1_2216_: *mut leanh::LeanObject,
    mut v_m_2217_: *mut leanh::LeanObject,
    mut v_inst_2218_: *mut leanh::LeanObject,
    mut v_00_u03b2_2219_: *mut leanh::LeanObject,
    mut v_f_2220_: *mut leanh::LeanObject,
    mut v_init_2221_: *mut leanh::LeanObject,
    mut v_b_2222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2226_: usize = 0;
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2223_ = leanh::lean_ctor_get(v_b_2222_, 1);
    leanh::lean_inc_ref(v_buckets_2223_);
    leanh::lean_dec_ref(v_b_2222_);
    v___f_2224_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2224_, 0, v_f_2220_);
    leanh::lean_inc_ref(v_inst_2218_);
    v___f_2225_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2225_, 0, v_inst_2218_);
    leanh::lean_closure_set(v___f_2225_, 1, v___f_2224_);
    v_sz_2226_ = lean_array_size(v_buckets_2223_);
    v___x_2227_ = 0usize;
    v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
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
    mut v_inst_2229_: *mut leanh::LeanObject,
    mut v_m_2230_: *mut leanh::LeanObject,
    mut v_f_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    v_buckets_2232_ = leanh::lean_ctor_get(v_m_2230_, 1);
    leanh::lean_inc_ref(v_buckets_2232_);
    leanh::lean_dec_ref(v_m_2230_);
    v___x_2233_ = leanh::lean_unsigned_to_nat(0);
    v___x_2234_ = lean_array_get_size(v_buckets_2232_);
    v___x_2235_ = leanh::lean_box(0);
    v___x_2236_ = lean_nat_dec_lt(v___x_2233_, v___x_2234_);
    if v___x_2236_ == 0 {
        let mut v_toApplicative_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_2232_);
        leanh::lean_dec(v_f_2231_);
        v_toApplicative_2237_ = leanh::lean_ctor_get(v_inst_2229_, 0);
        leanh::lean_inc_ref(v_toApplicative_2237_);
        leanh::lean_dec_ref(v_inst_2229_);
        v_toPure_2238_ = leanh::lean_ctor_get(v_toApplicative_2237_, 1);
        leanh::lean_inc(v_toPure_2238_);
        leanh::lean_dec_ref(v_toApplicative_2237_);
        v___x_2239_ =
            leanh::lean_apply_2(v_toPure_2238_, leanh::lean_box(0), v___x_2235_);
        return v___x_2239_;
    } else {
        let mut v___f_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: u8 = 0;
        v___f_2240_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_2240_, 0, v_f_2231_);
        leanh::lean_inc_ref(v_inst_2229_);
        v___f_2241_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2241_, 0, v_inst_2229_);
        leanh::lean_closure_set(v___f_2241_, 1, v___f_2240_);
        v___x_2242_ = lean_nat_dec_le(v___x_2234_, v___x_2234_);
        if v___x_2242_ == 0 {
            if v___x_2236_ == 0 {
                let mut v_toApplicative_2243_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_2241_);
                leanh::lean_dec_ref(v_buckets_2232_);
                v_toApplicative_2243_ = leanh::lean_ctor_get(v_inst_2229_, 0);
                leanh::lean_inc_ref(v_toApplicative_2243_);
                leanh::lean_dec_ref(v_inst_2229_);
                v_toPure_2244_ = leanh::lean_ctor_get(v_toApplicative_2243_, 1);
                leanh::lean_inc(v_toPure_2244_);
                leanh::lean_dec_ref(v_toApplicative_2243_);
                v___x_2245_ = leanh::lean_apply_2(
                    v_toPure_2244_,
                    leanh::lean_box(0),
                    v___x_2235_,
                );
                return v___x_2245_;
            } else {
                let mut v___x_2246_: usize = 0;
                let mut v___x_2247_: usize = 0;
                let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2246_ = 0usize;
                v___x_2247_ = lean_usize_of_nat(v___x_2234_);
                v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2249_ = 0usize;
            v___x_2250_ = lean_usize_of_nat(v___x_2234_);
            v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_inst_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2253_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2253_, 0, v_inst_2252_);
    return v___f_2253_;
}
pub unsafe fn l_Std_HashSet_Raw_instForMOfMonad(
    mut v_00_u03b1_2254_: *mut leanh::LeanObject,
    mut v_m_2255_: *mut leanh::LeanObject,
    mut v_inst_2256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2257_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2257_, 0, v_inst_2256_);
    return v___f_2257_;
}
pub unsafe fn l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(
    mut v_inst_2258_: *mut leanh::LeanObject,
    mut v_00_u03b2_2259_: *mut leanh::LeanObject,
    mut v_m_2260_: *mut leanh::LeanObject,
    mut v_init_2261_: *mut leanh::LeanObject,
    mut v_f_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2266_: usize = 0;
    let mut v___x_2267_: usize = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2263_ = leanh::lean_ctor_get(v_m_2260_, 1);
    leanh::lean_inc_ref(v_buckets_2263_);
    leanh::lean_dec_ref(v_m_2260_);
    v___f_2264_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2264_, 0, v_f_2262_);
    leanh::lean_inc_ref(v_inst_2258_);
    v___f_2265_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2265_, 0, v_inst_2258_);
    leanh::lean_closure_set(v___f_2265_, 1, v___f_2264_);
    v_sz_2266_ = lean_array_size(v_buckets_2263_);
    v___x_2267_ = 0usize;
    v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
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
    mut v_inst_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2270_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2270_, 0, v_inst_2269_);
    return v___f_2270_;
}
pub unsafe fn l_Std_HashSet_Raw_instForInOfMonad(
    mut v_00_u03b1_2271_: *mut leanh::LeanObject,
    mut v_m_2272_: *mut leanh::LeanObject,
    mut v_inst_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2274_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2274_, 0, v_inst_2273_);
    return v___f_2274_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg___lam__0(
    mut v_f_2275_: *mut leanh::LeanObject,
    mut v_a_2276_: *mut leanh::LeanObject,
    mut v_x_2277_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: u8 = 0;
    v___x_2278_ = leanh::lean_apply_1(v_f_2275_, v_a_2276_);
    v___x_2279_ = (leanh::lean_unbox(v___x_2278_) as u8);
    return v___x_2279_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(
    mut v_f_2280_: *mut leanh::LeanObject,
    mut v_a_2281_: *mut leanh::LeanObject,
    mut v_x_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2283_: u8 = 0;
    let mut v_r_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_2280_, v_a_2281_, v_x_2282_);
    v_r_2284_ = leanh::lean_box((v_res_2283_) as usize);
    return v_r_2284_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg(
    mut v_f_2285_: *mut leanh::LeanObject,
    mut v_m_2286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    v_buckets_2287_ = leanh::lean_ctor_get(v_m_2286_, 1);
    v___x_2288_ = leanh::lean_unsigned_to_nat(0);
    v___x_2289_ = lean_array_get_size(v_buckets_2287_);
    v___x_2290_ = lean_nat_dec_lt(v___x_2288_, v___x_2289_);
    if v___x_2290_ == 0 {
        let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_2286_);
        leanh::lean_dec_ref(v_f_2285_);
        v___x_2291_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
        );
        return v___x_2291_;
    } else {
        let mut v___f_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2292_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_2292_, 0, v_f_2285_);
        v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2292_, v_m_2286_);
        return v___x_2293_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_filter(
    mut v_00_u03b1_2294_: *mut leanh::LeanObject,
    mut v_inst_2295_: *mut leanh::LeanObject,
    mut v_inst_2296_: *mut leanh::LeanObject,
    mut v_f_2297_: *mut leanh::LeanObject,
    mut v_m_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    v_buckets_2299_ = leanh::lean_ctor_get(v_m_2298_, 1);
    v___x_2300_ = leanh::lean_unsigned_to_nat(0);
    v___x_2301_ = lean_array_get_size(v_buckets_2299_);
    v___x_2302_ = lean_nat_dec_lt(v___x_2300_, v___x_2301_);
    if v___x_2302_ == 0 {
        let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_2298_);
        leanh::lean_dec_ref(v_f_2297_);
        v___x_2303_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
        );
        return v___x_2303_;
    } else {
        let mut v___f_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_2304_ = leanh::lean_alloc_closure(
            l_Std_HashSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_2304_, 0, v_f_2297_);
        v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2304_, v_m_2298_);
        return v___x_2305_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_filter___boxed(
    mut v_00_u03b1_2306_: *mut leanh::LeanObject,
    mut v_inst_2307_: *mut leanh::LeanObject,
    mut v_inst_2308_: *mut leanh::LeanObject,
    mut v_f_2309_: *mut leanh::LeanObject,
    mut v_m_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2311_ = l_Std_HashSet_Raw_filter(
        v_00_u03b1_2306_,
        v_inst_2307_,
        v_inst_2308_,
        v_f_2309_,
        v_m_2310_,
    );
    leanh::lean_dec_ref(v_inst_2308_);
    leanh::lean_dec_ref(v_inst_2307_);
    return v_res_2311_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg___lam__0(
    mut v_x1_2312_: *mut leanh::LeanObject,
    mut v_x2_2313_: *mut leanh::LeanObject,
    mut v_x3_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = lean_array_push(v_x1_2312_, v_x2_2313_);
    return v___x_2315_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg___lam__1(
    mut v___x_2316_: *mut leanh::LeanObject,
    mut v___f_2317_: *mut leanh::LeanObject,
    mut v_acc_2318_: *mut leanh::LeanObject,
    mut v_l_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2316_,
        v___f_2317_,
        v_acc_2318_,
        v_l_2319_,
    );
    return v___x_2320_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg(
    mut v_m_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    v_size_2326_ = leanh::lean_ctor_get(v_m_2325_, 0);
    leanh::lean_inc(v_size_2326_);
    v_buckets_2327_ = leanh::lean_ctor_get(v_m_2325_, 1);
    leanh::lean_inc_ref(v_buckets_2327_);
    leanh::lean_dec_ref(v_m_2325_);
    v___x_2328_ = lean_mk_empty_array_with_capacity(v_size_2326_);
    leanh::lean_dec(v_size_2326_);
    v___x_2329_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v___x_2330_ = leanh::lean_unsigned_to_nat(0);
    v___x_2331_ = lean_array_get_size(v_buckets_2327_);
    v___x_2332_ = lean_nat_dec_lt(v___x_2330_, v___x_2331_);
    if v___x_2332_ == 0 {
        leanh::lean_dec_ref(v_buckets_2327_);
        return v___x_2328_;
    } else {
        let mut v___f_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        v___f_2333_ = l_Std_HashSet_Raw_toArray___redArg___closed__1;
        v___x_2334_ = lean_nat_dec_le(v___x_2331_, v___x_2331_);
        if v___x_2334_ == 0 {
            if v___x_2332_ == 0 {
                leanh::lean_dec_ref(v_buckets_2327_);
                return v___x_2328_;
            } else {
                let mut v___x_2335_: usize = 0;
                let mut v___x_2336_: usize = 0;
                let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2335_ = 0usize;
                v___x_2336_ = lean_usize_of_nat(v___x_2331_);
                v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2338_ = 0usize;
            v___x_2339_ = lean_usize_of_nat(v___x_2331_);
            v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_2341_: *mut leanh::LeanObject,
    mut v_m_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: u8 = 0;
    v_size_2343_ = leanh::lean_ctor_get(v_m_2342_, 0);
    leanh::lean_inc(v_size_2343_);
    v_buckets_2344_ = leanh::lean_ctor_get(v_m_2342_, 1);
    leanh::lean_inc_ref(v_buckets_2344_);
    leanh::lean_dec_ref(v_m_2342_);
    v___x_2345_ = lean_mk_empty_array_with_capacity(v_size_2343_);
    leanh::lean_dec(v_size_2343_);
    v___x_2346_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v___x_2347_ = leanh::lean_unsigned_to_nat(0);
    v___x_2348_ = lean_array_get_size(v_buckets_2344_);
    v___x_2349_ = lean_nat_dec_lt(v___x_2347_, v___x_2348_);
    if v___x_2349_ == 0 {
        leanh::lean_dec_ref(v_buckets_2344_);
        return v___x_2345_;
    } else {
        let mut v___f_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: u8 = 0;
        v___f_2350_ = l_Std_HashSet_Raw_toArray___redArg___closed__1;
        v___x_2351_ = lean_nat_dec_le(v___x_2348_, v___x_2348_);
        if v___x_2351_ == 0 {
            if v___x_2349_ == 0 {
                leanh::lean_dec_ref(v_buckets_2344_);
                return v___x_2345_;
            } else {
                let mut v___x_2352_: usize = 0;
                let mut v___x_2353_: usize = 0;
                let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2352_ = 0usize;
                v___x_2353_ = lean_usize_of_nat(v___x_2348_);
                v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2355_ = 0usize;
            v___x_2356_ = lean_usize_of_nat(v___x_2348_);
            v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_inst_2358_: *mut leanh::LeanObject,
    mut v_inst_2359_: *mut leanh::LeanObject,
    mut v_a_2360_: *mut leanh::LeanObject,
    mut v_b_2361_: *mut leanh::LeanObject,
    mut v_acc_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_2363_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_2358_,
        v_inst_2359_,
        v_acc_2362_,
        v_a_2360_,
        v_b_2361_,
    );
    v___x_2364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2364_, 0, v_r_2363_);
    return v___x_2364_;
}
pub unsafe fn l_Std_HashSet_Raw_union___redArg___lam__1(
    mut v___x_2365_: *mut leanh::LeanObject,
    mut v___f_2366_: *mut leanh::LeanObject,
    mut v_a_2367_: *mut leanh::LeanObject,
    mut v_x_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_2365_, v___f_2366_, v_a_2367_, v___y_2369_);
    return v___x_2370_;
}
pub unsafe fn l_Std_HashSet_Raw_union___redArg(
    mut v_inst_2373_: *mut leanh::LeanObject,
    mut v_inst_2374_: *mut leanh::LeanObject,
    mut v_m_u2081_2375_: *mut leanh::LeanObject,
    mut v_m_u2082_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    v_size_2377_ = leanh::lean_ctor_get(v_m_u2081_2375_, 0);
    v_buckets_2378_ = leanh::lean_ctor_get(v_m_u2081_2375_, 1);
    v___x_2379_ = leanh::lean_unsigned_to_nat(0);
    v___x_2380_ = lean_array_get_size(v_buckets_2378_);
    v___x_2381_ = lean_nat_dec_lt(v___x_2379_, v___x_2380_);
    if v___x_2381_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_2375_);
        leanh::lean_dec_ref(v_inst_2374_);
        leanh::lean_dec_ref(v_inst_2373_);
        return v_m_u2082_2376_;
    } else {
        let mut v_size_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: u8 = 0;
        v_size_2382_ = leanh::lean_ctor_get(v_m_u2082_2376_, 0);
        v_buckets_2383_ = leanh::lean_ctor_get(v_m_u2082_2376_, 1);
        v___x_2384_ = lean_array_get_size(v_buckets_2383_);
        v___x_2385_ = lean_nat_dec_lt(v___x_2379_, v___x_2384_);
        if v___x_2385_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_2376_);
            leanh::lean_dec_ref(v_inst_2374_);
            leanh::lean_dec_ref(v_inst_2373_);
            return v_m_u2081_2375_;
        } else {
            let mut v___x_2386_: u8 = 0;
            v___x_2386_ = lean_nat_dec_le(v_size_2377_, v_size_2382_);
            if v___x_2386_ == 0 {
                let mut v___f_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___f_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_2392_: usize = 0;
                let mut v___x_2393_: usize = 0;
                let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_buckets_2378_);
                leanh::lean_dec_ref(v_m_u2081_2375_);
                v___f_2389_ = leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_2389_, 0, v_inst_2373_);
                leanh::lean_closure_set(v___f_2389_, 1, v_inst_2374_);
                v___x_2390_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v___f_2391_ = leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_2391_, 0, v___x_2390_);
                leanh::lean_closure_set(v___f_2391_, 1, v___f_2389_);
                v_sz_2392_ = lean_array_size(v_buckets_2378_);
                v___x_2393_ = 0usize;
                v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_00_u03b1_2395_: *mut leanh::LeanObject,
    mut v_inst_2396_: *mut leanh::LeanObject,
    mut v_inst_2397_: *mut leanh::LeanObject,
    mut v_m_u2081_2398_: *mut leanh::LeanObject,
    mut v_m_u2082_2399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: u8 = 0;
    v_size_2400_ = leanh::lean_ctor_get(v_m_u2081_2398_, 0);
    v_buckets_2401_ = leanh::lean_ctor_get(v_m_u2081_2398_, 1);
    v___x_2402_ = leanh::lean_unsigned_to_nat(0);
    v___x_2403_ = lean_array_get_size(v_buckets_2401_);
    v___x_2404_ = lean_nat_dec_lt(v___x_2402_, v___x_2403_);
    if v___x_2404_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_2398_);
        leanh::lean_dec_ref(v_inst_2397_);
        leanh::lean_dec_ref(v_inst_2396_);
        return v_m_u2082_2399_;
    } else {
        let mut v_size_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: u8 = 0;
        v_size_2405_ = leanh::lean_ctor_get(v_m_u2082_2399_, 0);
        v_buckets_2406_ = leanh::lean_ctor_get(v_m_u2082_2399_, 1);
        v___x_2407_ = lean_array_get_size(v_buckets_2406_);
        v___x_2408_ = lean_nat_dec_lt(v___x_2402_, v___x_2407_);
        if v___x_2408_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_2399_);
            leanh::lean_dec_ref(v_inst_2397_);
            leanh::lean_dec_ref(v_inst_2396_);
            return v_m_u2081_2398_;
        } else {
            let mut v___x_2409_: u8 = 0;
            v___x_2409_ = lean_nat_dec_le(v_size_2400_, v_size_2405_);
            if v___x_2409_ == 0 {
                let mut v___f_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___f_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_2415_: usize = 0;
                let mut v___x_2416_: usize = 0;
                let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_buckets_2401_);
                leanh::lean_dec_ref(v_m_u2081_2398_);
                v___f_2412_ = leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_2412_, 0, v_inst_2396_);
                leanh::lean_closure_set(v___f_2412_, 1, v_inst_2397_);
                v___x_2413_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v___f_2414_ = leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_2414_, 0, v___x_2413_);
                leanh::lean_closure_set(v___f_2414_, 1, v___f_2412_);
                v_sz_2415_ = lean_array_size(v_buckets_2401_);
                v___x_2416_ = 0usize;
                v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_inst_2418_: *mut leanh::LeanObject,
    mut v_inst_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ =
        leanh::lean_alloc_closure(l_Std_HashSet_Raw_union as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2420_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2420_, 1, v_inst_2418_);
    leanh::lean_closure_set(v___x_2420_, 2, v_inst_2419_);
    return v___x_2420_;
}
pub unsafe fn l_Std_HashSet_Raw_instUnionOfBEqOfHashable(
    mut v_00_u03b1_2421_: *mut leanh::LeanObject,
    mut v_inst_2422_: *mut leanh::LeanObject,
    mut v_inst_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ =
        leanh::lean_alloc_closure(l_Std_HashSet_Raw_union as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2424_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2424_, 1, v_inst_2422_);
    leanh::lean_closure_set(v___x_2424_, 2, v_inst_2423_);
    return v___x_2424_;
}
pub unsafe fn l_Std_HashSet_Raw_inter___redArg(
    mut v_inst_2425_: *mut leanh::LeanObject,
    mut v_inst_2426_: *mut leanh::LeanObject,
    mut v_m_u2081_2427_: *mut leanh::LeanObject,
    mut v_m_u2082_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    v_buckets_2429_ = leanh::lean_ctor_get(v_m_u2081_2427_, 1);
    v___x_2430_ = leanh::lean_unsigned_to_nat(0);
    v___x_2431_ = lean_array_get_size(v_buckets_2429_);
    v___x_2432_ = lean_nat_dec_lt(v___x_2430_, v___x_2431_);
    if v___x_2432_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_2427_);
        leanh::lean_dec_ref(v_inst_2426_);
        leanh::lean_dec_ref(v_inst_2425_);
        return v_m_u2082_2428_;
    } else {
        let mut v_buckets_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2435_: u8 = 0;
        v_buckets_2433_ = leanh::lean_ctor_get(v_m_u2082_2428_, 1);
        v___x_2434_ = lean_array_get_size(v_buckets_2433_);
        v___x_2435_ = lean_nat_dec_lt(v___x_2430_, v___x_2434_);
        if v___x_2435_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_2428_);
            leanh::lean_dec_ref(v_inst_2426_);
            leanh::lean_dec_ref(v_inst_2425_);
            return v_m_u2081_2427_;
        } else {
            let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2437_: *mut leanh::LeanObject,
    mut v_inst_2438_: *mut leanh::LeanObject,
    mut v_inst_2439_: *mut leanh::LeanObject,
    mut v_m_u2081_2440_: *mut leanh::LeanObject,
    mut v_m_u2082_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    v_buckets_2442_ = leanh::lean_ctor_get(v_m_u2081_2440_, 1);
    v___x_2443_ = leanh::lean_unsigned_to_nat(0);
    v___x_2444_ = lean_array_get_size(v_buckets_2442_);
    v___x_2445_ = lean_nat_dec_lt(v___x_2443_, v___x_2444_);
    if v___x_2445_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_2440_);
        leanh::lean_dec_ref(v_inst_2439_);
        leanh::lean_dec_ref(v_inst_2438_);
        return v_m_u2082_2441_;
    } else {
        let mut v_buckets_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2448_: u8 = 0;
        v_buckets_2446_ = leanh::lean_ctor_get(v_m_u2082_2441_, 1);
        v___x_2447_ = lean_array_get_size(v_buckets_2446_);
        v___x_2448_ = lean_nat_dec_lt(v___x_2443_, v___x_2447_);
        if v___x_2448_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_2441_);
            leanh::lean_dec_ref(v_inst_2439_);
            leanh::lean_dec_ref(v_inst_2438_);
            return v_m_u2081_2440_;
        } else {
            let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2450_: *mut leanh::LeanObject,
    mut v_inst_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ =
        leanh::lean_alloc_closure(l_Std_HashSet_Raw_inter as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2452_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2452_, 1, v_inst_2450_);
    leanh::lean_closure_set(v___x_2452_, 2, v_inst_2451_);
    return v___x_2452_;
}
pub unsafe fn l_Std_HashSet_Raw_instInterOfBEqOfHashable(
    mut v_00_u03b1_2453_: *mut leanh::LeanObject,
    mut v_inst_2454_: *mut leanh::LeanObject,
    mut v_inst_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ =
        leanh::lean_alloc_closure(l_Std_HashSet_Raw_inter as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2456_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2456_, 1, v_inst_2454_);
    leanh::lean_closure_set(v___x_2456_, 2, v_inst_2455_);
    return v___x_2456_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_beq___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_2458_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2458_, 0, v___x_2457_);
    return v___f_2458_;
}
pub unsafe fn l_Std_HashSet_Raw_beq___redArg(
    mut v_inst_2459_: *mut leanh::LeanObject,
    mut v_inst_2460_: *mut leanh::LeanObject,
    mut v_m_u2081_2461_: *mut leanh::LeanObject,
    mut v_m_u2082_2462_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u8 = 0;
    v___f_2463_ = leanh::lean_obj_once(
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
    mut v_inst_2465_: *mut leanh::LeanObject,
    mut v_inst_2466_: *mut leanh::LeanObject,
    mut v_m_u2081_2467_: *mut leanh::LeanObject,
    mut v_m_u2082_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2469_: u8 = 0;
    let mut v_r_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2469_ = l_Std_HashSet_Raw_beq___redArg(
        v_inst_2465_,
        v_inst_2466_,
        v_m_u2081_2467_,
        v_m_u2082_2468_,
    );
    v_r_2470_ = leanh::lean_box((v_res_2469_) as usize);
    return v_r_2470_;
}
pub unsafe fn l_Std_HashSet_Raw_beq(
    mut v_00_u03b1_2471_: *mut leanh::LeanObject,
    mut v_inst_2472_: *mut leanh::LeanObject,
    mut v_inst_2473_: *mut leanh::LeanObject,
    mut v_m_u2081_2474_: *mut leanh::LeanObject,
    mut v_m_u2082_2475_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_2477_: *mut leanh::LeanObject,
    mut v_inst_2478_: *mut leanh::LeanObject,
    mut v_inst_2479_: *mut leanh::LeanObject,
    mut v_m_u2081_2480_: *mut leanh::LeanObject,
    mut v_m_u2082_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2482_: u8 = 0;
    let mut v_r_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2482_ = l_Std_HashSet_Raw_beq(
        v_00_u03b1_2477_,
        v_inst_2478_,
        v_inst_2479_,
        v_m_u2081_2480_,
        v_m_u2082_2481_,
    );
    v_r_2483_ = leanh::lean_box((v_res_2482_) as usize);
    return v_r_2483_;
}
pub unsafe fn l_Std_HashSet_Raw_instBEqOfHashable___redArg(
    mut v_inst_2484_: *mut leanh::LeanObject,
    mut v_inst_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_beq___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_2486_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2486_, 1, v_inst_2484_);
    leanh::lean_closure_set(v___x_2486_, 2, v_inst_2485_);
    return v___x_2486_;
}
pub unsafe fn l_Std_HashSet_Raw_instBEqOfHashable(
    mut v_00_u03b1_2487_: *mut leanh::LeanObject,
    mut v_inst_2488_: *mut leanh::LeanObject,
    mut v_inst_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_beq___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_2490_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2490_, 1, v_inst_2488_);
    leanh::lean_closure_set(v___x_2490_, 2, v_inst_2489_);
    return v___x_2490_;
}
pub unsafe fn l_Std_HashSet_Raw_diff___redArg___lam__0(
    mut v_inst_2491_: *mut leanh::LeanObject,
    mut v_inst_2492_: *mut leanh::LeanObject,
    mut v_m_u2082_2493_: *mut leanh::LeanObject,
    mut v___x_2494_: u8,
    mut v_k_2495_: *mut leanh::LeanObject,
    mut v_x_2496_: *mut leanh::LeanObject,
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
    mut v_inst_2499_: *mut leanh::LeanObject,
    mut v_inst_2500_: *mut leanh::LeanObject,
    mut v_m_u2082_2501_: *mut leanh::LeanObject,
    mut v___x_2502_: *mut leanh::LeanObject,
    mut v_k_2503_: *mut leanh::LeanObject,
    mut v_x_2504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_97__boxed_2505_: u8 = 0;
    let mut v_res_2506_: u8 = 0;
    let mut v_r_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_97__boxed_2505_ = (leanh::lean_unbox(v___x_2502_) as u8);
    v_res_2506_ = l_Std_HashSet_Raw_diff___redArg___lam__0(
        v_inst_2499_,
        v_inst_2500_,
        v_m_u2082_2501_,
        v___x_97__boxed_2505_,
        v_k_2503_,
        v_x_2504_,
    );
    leanh::lean_dec_ref(v_m_u2082_2501_);
    v_r_2507_ = leanh::lean_box((v_res_2506_) as usize);
    return v_r_2507_;
}
pub unsafe fn l_Std_HashSet_Raw_diff___redArg(
    mut v_inst_2508_: *mut leanh::LeanObject,
    mut v_inst_2509_: *mut leanh::LeanObject,
    mut v_m_u2081_2510_: *mut leanh::LeanObject,
    mut v_m_u2082_2511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    v_size_2512_ = leanh::lean_ctor_get(v_m_u2081_2510_, 0);
    v_buckets_2513_ = leanh::lean_ctor_get(v_m_u2081_2510_, 1);
    v___x_2514_ = leanh::lean_unsigned_to_nat(0);
    v___x_2515_ = lean_array_get_size(v_buckets_2513_);
    v___x_2516_ = lean_nat_dec_lt(v___x_2514_, v___x_2515_);
    if v___x_2516_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_2510_);
        leanh::lean_dec_ref(v_inst_2509_);
        leanh::lean_dec_ref(v_inst_2508_);
        return v_m_u2082_2511_;
    } else {
        let mut v_size_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: u8 = 0;
        v_size_2517_ = leanh::lean_ctor_get(v_m_u2082_2511_, 0);
        v_buckets_2518_ = leanh::lean_ctor_get(v_m_u2082_2511_, 1);
        v___x_2519_ = lean_array_get_size(v_buckets_2518_);
        v___x_2520_ = lean_nat_dec_lt(v___x_2514_, v___x_2519_);
        if v___x_2520_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_2511_);
            leanh::lean_dec_ref(v_inst_2509_);
            leanh::lean_dec_ref(v_inst_2508_);
            return v_m_u2081_2510_;
        } else {
            let mut v___x_2521_: u8 = 0;
            v___x_2521_ = lean_nat_dec_le(v_size_2512_, v_size_2517_);
            if v___x_2521_ == 0 {
                let mut v___f_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2524_ = leanh::lean_box((v___x_2521_) as usize);
                v___f_2525_ = leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_2525_, 0, v_inst_2508_);
                leanh::lean_closure_set(v___f_2525_, 1, v_inst_2509_);
                leanh::lean_closure_set(v___f_2525_, 2, v_m_u2082_2511_);
                leanh::lean_closure_set(v___f_2525_, 3, v___x_2524_);
                v___x_2526_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2525_, v_m_u2081_2510_);
                return v___x_2526_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_diff(
    mut v_00_u03b1_2527_: *mut leanh::LeanObject,
    mut v_inst_2528_: *mut leanh::LeanObject,
    mut v_inst_2529_: *mut leanh::LeanObject,
    mut v_m_u2081_2530_: *mut leanh::LeanObject,
    mut v_m_u2082_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    v_size_2532_ = leanh::lean_ctor_get(v_m_u2081_2530_, 0);
    v_buckets_2533_ = leanh::lean_ctor_get(v_m_u2081_2530_, 1);
    v___x_2534_ = leanh::lean_unsigned_to_nat(0);
    v___x_2535_ = lean_array_get_size(v_buckets_2533_);
    v___x_2536_ = lean_nat_dec_lt(v___x_2534_, v___x_2535_);
    if v___x_2536_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_2530_);
        leanh::lean_dec_ref(v_inst_2529_);
        leanh::lean_dec_ref(v_inst_2528_);
        return v_m_u2082_2531_;
    } else {
        let mut v_size_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2540_: u8 = 0;
        v_size_2537_ = leanh::lean_ctor_get(v_m_u2082_2531_, 0);
        v_buckets_2538_ = leanh::lean_ctor_get(v_m_u2082_2531_, 1);
        v___x_2539_ = lean_array_get_size(v_buckets_2538_);
        v___x_2540_ = lean_nat_dec_lt(v___x_2534_, v___x_2539_);
        if v___x_2540_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_2531_);
            leanh::lean_dec_ref(v_inst_2529_);
            leanh::lean_dec_ref(v_inst_2528_);
            return v_m_u2081_2530_;
        } else {
            let mut v___x_2541_: u8 = 0;
            v___x_2541_ = lean_nat_dec_le(v_size_2532_, v_size_2537_);
            if v___x_2541_ == 0 {
                let mut v___f_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2544_ = leanh::lean_box((v___x_2541_) as usize);
                v___f_2545_ = leanh::lean_alloc_closure(
                    l_Std_HashSet_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_2545_, 0, v_inst_2528_);
                leanh::lean_closure_set(v___f_2545_, 1, v_inst_2529_);
                leanh::lean_closure_set(v___f_2545_, 2, v_m_u2082_2531_);
                leanh::lean_closure_set(v___f_2545_, 3, v___x_2544_);
                v___x_2546_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2545_, v_m_u2081_2530_);
                return v___x_2546_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(
    mut v_inst_2547_: *mut leanh::LeanObject,
    mut v_inst_2548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2549_ =
        leanh::lean_alloc_closure(l_Std_HashSet_Raw_diff as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2549_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2549_, 1, v_inst_2547_);
    leanh::lean_closure_set(v___x_2549_, 2, v_inst_2548_);
    return v___x_2549_;
}
pub unsafe fn l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(
    mut v_00_u03b1_2550_: *mut leanh::LeanObject,
    mut v_inst_2551_: *mut leanh::LeanObject,
    mut v_inst_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ =
        leanh::lean_alloc_closure(l_Std_HashSet_Raw_diff as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2553_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2553_, 1, v_inst_2551_);
    leanh::lean_closure_set(v___x_2553_, 2, v_inst_2552_);
    return v___x_2553_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__0(
    mut v_p_2554_: *mut leanh::LeanObject,
    mut v___x_2555_: *mut leanh::LeanObject,
    mut v___x_2556_: *mut leanh::LeanObject,
    mut v_a_2557_: *mut leanh::LeanObject,
    mut v_b_2558_: *mut leanh::LeanObject,
    mut v_acc_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    v___x_2560_ = leanh::lean_apply_1(v_p_2554_, v_a_2557_);
    v___x_2561_ = (leanh::lean_unbox(v___x_2560_) as u8);
    if v___x_2561_ == 0 {
        let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2556_);
        v___x_2562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2562_, 0, v___x_2560_);
        v___x_2563_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2563_, 0, v___x_2562_);
        leanh::lean_ctor_set(v___x_2563_, 1, v___x_2555_);
        v___x_2564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
        return v___x_2564_;
    } else {
        let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2565_, 0, v___x_2556_);
        return v___x_2565_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__0___boxed(
    mut v_p_2566_: *mut leanh::LeanObject,
    mut v___x_2567_: *mut leanh::LeanObject,
    mut v___x_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
    mut v_b_2570_: *mut leanh::LeanObject,
    mut v_acc_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Std_HashSet_Raw_all___redArg___lam__0(
        v_p_2566_,
        v___x_2567_,
        v___x_2568_,
        v_a_2569_,
        v_b_2570_,
        v_acc_2571_,
    );
    leanh::lean_dec_ref(v_acc_2571_);
    return v_res_2572_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__1(
    mut v___x_2573_: *mut leanh::LeanObject,
    mut v___f_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
    mut v_x_2576_: *mut leanh::LeanObject,
    mut v___y_2577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_2573_, v___f_2574_, v_a_2575_, v___y_2577_);
    return v___x_2578_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg(
    mut v_m_2582_: *mut leanh::LeanObject,
    mut v_p_2583_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2590_: usize = 0;
    let mut v___x_2591_: usize = 0;
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2585_ = leanh::lean_ctor_get(v_m_2582_, 1);
    leanh::lean_inc_ref(v_buckets_2585_);
    leanh::lean_dec_ref(v_m_2582_);
    v___x_2586_ = leanh::lean_box(0);
    v___x_2587_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2588_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2588_, 0, v_p_2583_);
    leanh::lean_closure_set(v___f_2588_, 1, v___x_2586_);
    leanh::lean_closure_set(v___f_2588_, 2, v___x_2587_);
    v___f_2589_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2589_, 0, v___x_2584_);
    leanh::lean_closure_set(v___f_2589_, 1, v___f_2588_);
    v_sz_2590_ = lean_array_size(v_buckets_2585_);
    v___x_2591_ = 0usize;
    v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2584_,
        v_buckets_2585_,
        v___f_2589_,
        v_sz_2590_,
        v___x_2591_,
        v___x_2587_,
    );
    v_fst_2593_ = leanh::lean_ctor_get(v___x_2592_, 0);
    leanh::lean_inc(v_fst_2593_);
    leanh::lean_dec(v___x_2592_);
    if leanh::lean_obj_tag(v_fst_2593_) == 0 {
        let mut v___x_2594_: u8 = 0;
        v___x_2594_ = 1;
        return v___x_2594_;
    } else {
        let mut v_val_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2596_: u8 = 0;
        v_val_2595_ = leanh::lean_ctor_get(v_fst_2593_, 0);
        leanh::lean_inc(v_val_2595_);
        leanh::lean_dec_ref_known(v_fst_2593_, 1);
        v___x_2596_ = (leanh::lean_unbox(v_val_2595_) as u8);
        leanh::lean_dec(v_val_2595_);
        return v___x_2596_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___boxed(
    mut v_m_2597_: *mut leanh::LeanObject,
    mut v_p_2598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2599_: u8 = 0;
    let mut v_r_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2599_ = l_Std_HashSet_Raw_all___redArg(v_m_2597_, v_p_2598_);
    v_r_2600_ = leanh::lean_box((v_res_2599_) as usize);
    return v_r_2600_;
}
pub unsafe fn l_Std_HashSet_Raw_all(
    mut v_00_u03b1_2601_: *mut leanh::LeanObject,
    mut v_m_2602_: *mut leanh::LeanObject,
    mut v_p_2603_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2605_ = leanh::lean_ctor_get(v_m_2602_, 1);
    leanh::lean_inc_ref(v_buckets_2605_);
    leanh::lean_dec_ref(v_m_2602_);
    v___x_2606_ = leanh::lean_box(0);
    v___x_2607_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2608_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2608_, 0, v_p_2603_);
    leanh::lean_closure_set(v___f_2608_, 1, v___x_2606_);
    leanh::lean_closure_set(v___f_2608_, 2, v___x_2607_);
    v___f_2609_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2609_, 0, v___x_2604_);
    leanh::lean_closure_set(v___f_2609_, 1, v___f_2608_);
    v_sz_2610_ = lean_array_size(v_buckets_2605_);
    v___x_2611_ = 0usize;
    v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2604_,
        v_buckets_2605_,
        v___f_2609_,
        v_sz_2610_,
        v___x_2611_,
        v___x_2607_,
    );
    v_fst_2613_ = leanh::lean_ctor_get(v___x_2612_, 0);
    leanh::lean_inc(v_fst_2613_);
    leanh::lean_dec(v___x_2612_);
    if leanh::lean_obj_tag(v_fst_2613_) == 0 {
        let mut v___x_2614_: u8 = 0;
        v___x_2614_ = 1;
        return v___x_2614_;
    } else {
        let mut v_val_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2616_: u8 = 0;
        v_val_2615_ = leanh::lean_ctor_get(v_fst_2613_, 0);
        leanh::lean_inc(v_val_2615_);
        leanh::lean_dec_ref_known(v_fst_2613_, 1);
        v___x_2616_ = (leanh::lean_unbox(v_val_2615_) as u8);
        leanh::lean_dec(v_val_2615_);
        return v___x_2616_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___boxed(
    mut v_00_u03b1_2617_: *mut leanh::LeanObject,
    mut v_m_2618_: *mut leanh::LeanObject,
    mut v_p_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2620_: u8 = 0;
    let mut v_r_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2620_ = l_Std_HashSet_Raw_all(v_00_u03b1_2617_, v_m_2618_, v_p_2619_);
    v_r_2621_ = leanh::lean_box((v_res_2620_) as usize);
    return v_r_2621_;
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___lam__0(
    mut v_p_2622_: *mut leanh::LeanObject,
    mut v___x_2623_: *mut leanh::LeanObject,
    mut v___x_2624_: *mut leanh::LeanObject,
    mut v_a_2625_: *mut leanh::LeanObject,
    mut v_b_2626_: *mut leanh::LeanObject,
    mut v_acc_2627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    v___x_2628_ = leanh::lean_apply_1(v_p_2622_, v_a_2625_);
    v___x_2629_ = (leanh::lean_unbox(v___x_2628_) as u8);
    if v___x_2629_ == 0 {
        let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2630_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2630_, 0, v___x_2623_);
        return v___x_2630_;
    } else {
        let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2623_);
        v___x_2631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2631_, 0, v___x_2628_);
        v___x_2632_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2632_, 0, v___x_2631_);
        leanh::lean_ctor_set(v___x_2632_, 1, v___x_2624_);
        v___x_2633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2633_, 0, v___x_2632_);
        return v___x_2633_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___lam__0___boxed(
    mut v_p_2634_: *mut leanh::LeanObject,
    mut v___x_2635_: *mut leanh::LeanObject,
    mut v___x_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
    mut v_b_2638_: *mut leanh::LeanObject,
    mut v_acc_2639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2640_ = l_Std_HashSet_Raw_any___redArg___lam__0(
        v_p_2634_,
        v___x_2635_,
        v___x_2636_,
        v_a_2637_,
        v_b_2638_,
        v_acc_2639_,
    );
    leanh::lean_dec_ref(v_acc_2639_);
    return v_res_2640_;
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg(
    mut v_m_2641_: *mut leanh::LeanObject,
    mut v_p_2642_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2649_: usize = 0;
    let mut v___x_2650_: usize = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2643_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2644_ = leanh::lean_ctor_get(v_m_2641_, 1);
    leanh::lean_inc_ref(v_buckets_2644_);
    leanh::lean_dec_ref(v_m_2641_);
    v___x_2645_ = leanh::lean_box(0);
    v___x_2646_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2647_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2647_, 0, v_p_2642_);
    leanh::lean_closure_set(v___f_2647_, 1, v___x_2646_);
    leanh::lean_closure_set(v___f_2647_, 2, v___x_2645_);
    v___f_2648_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2648_, 0, v___x_2643_);
    leanh::lean_closure_set(v___f_2648_, 1, v___f_2647_);
    v_sz_2649_ = lean_array_size(v_buckets_2644_);
    v___x_2650_ = 0usize;
    v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2643_,
        v_buckets_2644_,
        v___f_2648_,
        v_sz_2649_,
        v___x_2650_,
        v___x_2646_,
    );
    v_fst_2652_ = leanh::lean_ctor_get(v___x_2651_, 0);
    leanh::lean_inc(v_fst_2652_);
    leanh::lean_dec(v___x_2651_);
    if leanh::lean_obj_tag(v_fst_2652_) == 0 {
        let mut v___x_2653_: u8 = 0;
        v___x_2653_ = 0;
        return v___x_2653_;
    } else {
        let mut v_val_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: u8 = 0;
        v_val_2654_ = leanh::lean_ctor_get(v_fst_2652_, 0);
        leanh::lean_inc(v_val_2654_);
        leanh::lean_dec_ref_known(v_fst_2652_, 1);
        v___x_2655_ = (leanh::lean_unbox(v_val_2654_) as u8);
        leanh::lean_dec(v_val_2654_);
        return v___x_2655_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___boxed(
    mut v_m_2656_: *mut leanh::LeanObject,
    mut v_p_2657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2658_: u8 = 0;
    let mut v_r_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2658_ = l_Std_HashSet_Raw_any___redArg(v_m_2656_, v_p_2657_);
    v_r_2659_ = leanh::lean_box((v_res_2658_) as usize);
    return v_r_2659_;
}
pub unsafe fn l_Std_HashSet_Raw_any(
    mut v_00_u03b1_2660_: *mut leanh::LeanObject,
    mut v_m_2661_: *mut leanh::LeanObject,
    mut v_p_2662_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2669_: usize = 0;
    let mut v___x_2670_: usize = 0;
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2663_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2664_ = leanh::lean_ctor_get(v_m_2661_, 1);
    leanh::lean_inc_ref(v_buckets_2664_);
    leanh::lean_dec_ref(v_m_2661_);
    v___x_2665_ = leanh::lean_box(0);
    v___x_2666_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2667_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_2667_, 0, v_p_2662_);
    leanh::lean_closure_set(v___f_2667_, 1, v___x_2666_);
    leanh::lean_closure_set(v___f_2667_, 2, v___x_2665_);
    v___f_2668_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2668_, 0, v___x_2663_);
    leanh::lean_closure_set(v___f_2668_, 1, v___f_2667_);
    v_sz_2669_ = lean_array_size(v_buckets_2664_);
    v___x_2670_ = 0usize;
    v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2663_,
        v_buckets_2664_,
        v___f_2668_,
        v_sz_2669_,
        v___x_2670_,
        v___x_2666_,
    );
    v_fst_2672_ = leanh::lean_ctor_get(v___x_2671_, 0);
    leanh::lean_inc(v_fst_2672_);
    leanh::lean_dec(v___x_2671_);
    if leanh::lean_obj_tag(v_fst_2672_) == 0 {
        let mut v___x_2673_: u8 = 0;
        v___x_2673_ = 0;
        return v___x_2673_;
    } else {
        let mut v_val_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: u8 = 0;
        v_val_2674_ = leanh::lean_ctor_get(v_fst_2672_, 0);
        leanh::lean_inc(v_val_2674_);
        leanh::lean_dec_ref_known(v_fst_2672_, 1);
        v___x_2675_ = (leanh::lean_unbox(v_val_2674_) as u8);
        leanh::lean_dec(v_val_2674_);
        return v___x_2675_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___boxed(
    mut v_00_u03b1_2676_: *mut leanh::LeanObject,
    mut v_m_2677_: *mut leanh::LeanObject,
    mut v_p_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2679_: u8 = 0;
    let mut v_r_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Std_HashSet_Raw_any(v_00_u03b1_2676_, v_m_2677_, v_p_2678_);
    v_r_2680_ = leanh::lean_box((v_res_2679_) as usize);
    return v_r_2680_;
}
pub unsafe fn l_Std_HashSet_Raw_insertMany___redArg(
    mut v_inst_2681_: *mut leanh::LeanObject,
    mut v_inst_2682_: *mut leanh::LeanObject,
    mut v_inst_2683_: *mut leanh::LeanObject,
    mut v_m_2684_: *mut leanh::LeanObject,
    mut v_l_2685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: u8 = 0;
    v_buckets_2686_ = leanh::lean_ctor_get(v_m_2684_, 1);
    v___x_2687_ = leanh::lean_unsigned_to_nat(0);
    v___x_2688_ = lean_array_get_size(v_buckets_2686_);
    v___x_2689_ = lean_nat_dec_lt(v___x_2687_, v___x_2688_);
    if v___x_2689_ == 0 {
        leanh::lean_dec(v_l_2685_);
        leanh::lean_dec(v_inst_2683_);
        leanh::lean_dec_ref(v_inst_2682_);
        leanh::lean_dec_ref(v_inst_2681_);
        return v_m_2684_;
    } else {
        let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2691_: *mut leanh::LeanObject,
    mut v_inst_2692_: *mut leanh::LeanObject,
    mut v_inst_2693_: *mut leanh::LeanObject,
    mut v_00_u03c1_2694_: *mut leanh::LeanObject,
    mut v_inst_2695_: *mut leanh::LeanObject,
    mut v_m_2696_: *mut leanh::LeanObject,
    mut v_l_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    v_buckets_2698_ = leanh::lean_ctor_get(v_m_2696_, 1);
    v___x_2699_ = leanh::lean_unsigned_to_nat(0);
    v___x_2700_ = lean_array_get_size(v_buckets_2698_);
    v___x_2701_ = lean_nat_dec_lt(v___x_2699_, v___x_2700_);
    if v___x_2701_ == 0 {
        leanh::lean_dec(v_l_2697_);
        leanh::lean_dec(v_inst_2695_);
        leanh::lean_dec_ref(v_inst_2693_);
        leanh::lean_dec_ref(v_inst_2692_);
        return v_m_2696_;
    } else {
        let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2707_: *mut leanh::LeanObject,
    mut v_inst_2708_: *mut leanh::LeanObject,
    mut v_l_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    v___x_2710_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2711_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2711_ == 0 {
        leanh::lean_dec_ref(v_l_2709_);
        leanh::lean_dec_ref(v_inst_2708_);
        leanh::lean_dec_ref(v_inst_2707_);
        return v___x_2710_;
    } else {
        let mut v___f_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2714_: *mut leanh::LeanObject,
    mut v_inst_2715_: *mut leanh::LeanObject,
    mut v_inst_2716_: *mut leanh::LeanObject,
    mut v_l_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: u8 = 0;
    v___x_2718_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2719_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2719_ == 0 {
        leanh::lean_dec_ref(v_l_2717_);
        leanh::lean_dec_ref(v_inst_2716_);
        leanh::lean_dec_ref(v_inst_2715_);
        return v___x_2718_;
    } else {
        let mut v___f_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_2722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2722_);
    return v___x_2723_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(
    mut v_m_2724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_2724_);
    leanh::lean_dec_ref(v_m_2724_);
    return v_res_2725_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets(
    mut v_00_u03b1_2726_: *mut leanh::LeanObject,
    mut v_m_2727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2727_);
    return v___x_2728_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets___boxed(
    mut v_00_u03b1_2729_: *mut leanh::LeanObject,
    mut v_m_2730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_2729_, v_m_2730_);
    leanh::lean_dec_ref(v_m_2730_);
    return v_res_2731_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr___redArg___lam__2(
    mut v_inst_2735_: *mut leanh::LeanObject,
    mut v___f_2736_: *mut leanh::LeanObject,
    mut v_m_2737_: *mut leanh::LeanObject,
    mut v_prec_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2743_: u8 = 0;
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___f_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut v_unused_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2739_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v_buckets_2740_ = leanh::lean_ctor_get(v_m_2737_, 1);
                v_isSharedCheck_2760_ = (!leanh::lean_is_exclusive(v_m_2737_)) as u8;
                if v_isSharedCheck_2760_ == 0 {
                    v_unused_2761_ = leanh::lean_ctor_get(v_m_2737_, 0);
                    leanh::lean_dec(v_unused_2761_);
                    v___x_2742_ = v_m_2737_;
                    v_isShared_2743_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2740_);
                    leanh::lean_dec(v_m_2737_);
                    v___x_2742_ = leanh::lean_box(0);
                    v_isShared_2743_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2744_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1;
                v___x_2752_ = leanh::lean_box(0);
                v___x_2753_ = lean_array_get_size(v_buckets_2740_);
                v___x_2754_ = leanh::lean_unsigned_to_nat(0);
                v___x_2755_ = lean_nat_dec_lt(v___x_2754_, v___x_2753_);
                if v___x_2755_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2740_);
                    leanh::lean_dec_ref(v___f_2736_);
                    v___y_2746_ = v___x_2752_;
                    state = 2;
                    continue;
                } else {
                    v___f_2756_ = leanh::lean_alloc_closure(
                        l_Std_HashSet_Raw_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2756_, 0, v___x_2739_);
                    leanh::lean_closure_set(v___f_2756_, 1, v___f_2736_);
                    v___x_2757_ = lean_usize_of_nat(v___x_2753_);
                    v___x_2758_ = 0usize;
                    v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
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
                    leanh::lean_ctor_set_tag(v___x_2742_, 5);
                    leanh::lean_ctor_set(v___x_2742_, 1, v___x_2747_);
                    leanh::lean_ctor_set(v___x_2742_, 0, v___x_2744_);
                    v___x_2749_ = v___x_2742_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2747_);
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
    mut v_inst_2762_: *mut leanh::LeanObject,
    mut v___f_2763_: *mut leanh::LeanObject,
    mut v_m_2764_: *mut leanh::LeanObject,
    mut v_prec_2765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2766_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(
        v_inst_2762_,
        v___f_2763_,
        v_m_2764_,
        v_prec_2765_,
    );
    leanh::lean_dec(v_prec_2765_);
    return v_res_2766_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr___redArg(
    mut v_inst_2767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2768_ = l_Std_HashSet_Raw_toList___redArg___closed__10;
    v___f_2769_ = leanh::lean_alloc_closure(
        l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2769_, 0, v_inst_2767_);
    leanh::lean_closure_set(v___f_2769_, 1, v___f_2768_);
    return v___f_2769_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr(
    mut v_00_u03b1_2770_: *mut leanh::LeanObject,
    mut v_inst_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_2771_);
    return v___x_2772_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_Raw(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashSet_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashSet_Raw(builtin);
}