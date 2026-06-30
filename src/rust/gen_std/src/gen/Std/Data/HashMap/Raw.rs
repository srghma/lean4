// Lean compiler output
// Module: Std.Data.HashMap.Raw
// Imports: Std.Data.DHashMap.Raw
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
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0,
};
use crate::r#gen::Init::Data::List::Control::l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::Repr::{
    l_List_repr___redArg, l_Prod_repr___boxed, l_Repr_addAppParen,
    l_instReprTupleOfRepr___redArg___lam__0,
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
    l_Std_DHashMap_Internal_AssocList_replace___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_erase___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_expand___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_inter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_map___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Raw::{
    initialize_Std_Data_DHashMap_Raw, l_Std_DHashMap_Raw_Const_beq___redArg,
    l_Std_DHashMap_Raw_Internal_numBuckets___redArg, l_Std_DHashMap_Raw_instDecidableMem___redArg,
    runtime_initialize_Std_Data_DHashMap_Raw,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2;
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashMap_Raw_term___x7em___00__closed__0_value: leanh::LeanStringObject<4> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__1_value: leanh::LeanStringObject<8> =
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
        m_data: [72, 97, 115, 104, 77, 97, 112, 0],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__2_value: leanh::LeanStringObject<4> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__3_value: leanh::LeanStringObject<9> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__1_value)
                as *mut leanh::LeanObject,
            7102038059608022050 as *mut leanh::LeanObject,
        ],
    };
static l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__2_value)
                as *mut leanh::LeanObject,
            8317422437539803697 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_HashMap_Raw_term___x7em___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__3_value)
                as *mut leanh::LeanObject,
            11341035097657881147 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__5_value: leanh::LeanStringObject<8> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__5_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__7_value: leanh::LeanStringObject<5> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__8_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__9_value: leanh::LeanStringObject<5> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__9_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__11_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__10_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__13_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_HashMap_Raw_term___x7em__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,6049842283740396800 as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value) as *mut leanh::LeanObject;
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__1_value) as *mut leanh::LeanObject,7102038059608022050 as *mut leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__2_value) as *mut leanh::LeanObject,8317422437539803697 as *mut leanh::LeanObject] };
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,14692178904334265170 as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1: u8 = 0;
pub static l_Std_HashMap_Raw_keys___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__10_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_Raw_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__11_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_Raw_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofList___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_ofList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofList___redArg___closed__1_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_ofList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_ofList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_ofArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofArray___redArg___closed__1_value: leanh::LeanClosureObject<
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
        core::ptr::addr_of!(l_Std_HashMap_Raw_ofArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_ofArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_Raw_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_toList___redArg___closed__1_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_Raw_toList___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_toList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_toList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_all___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_HashMap_Raw_all___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_all___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_union___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_union___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_union___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_toArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashMap_Raw_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_toArray___redArg___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashMap_Raw_toArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keysArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashMap_Raw_keysArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keysArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_keysArray___redArg___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashMap_Raw_keysArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_keysArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keysArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_values___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_Raw_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_Raw_values___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_values___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_values___redArg___closed__1_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_Raw_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_values___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_values___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_values___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashMap_Raw_valuesArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_HashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_valuesArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value:
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
        83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 46, 82, 97, 119, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity___redArg(
    mut v_capacity_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = leanh::lean_unsigned_to_nat(0);
    v___x_2201_ = leanh::lean_unsigned_to_nat(4);
    v___x_2202_ = lean_nat_mul(v_capacity_2199_, v___x_2201_);
    v___x_2203_ = leanh::lean_unsigned_to_nat(3);
    v___x_2204_ = lean_nat_div(v___x_2202_, v___x_2203_);
    leanh::lean_dec(v___x_2202_);
    v___x_2205_ = l_Nat_nextPowerOfTwo(v___x_2204_);
    leanh::lean_dec(v___x_2204_);
    v___x_2206_ = leanh::lean_box(0);
    v___x_2207_ = lean_mk_array(v___x_2205_, v___x_2206_);
    v___x_2208_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2208_, 0, v___x_2200_);
    leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity___redArg___boxed(
    mut v_capacity_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2210_ = l_Std_HashMap_Raw_emptyWithCapacity___redArg(v_capacity_2209_);
    leanh::lean_dec(v_capacity_2209_);
    return v_res_2210_;
}
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity(
    mut v_00_u03b1_2211_: *mut leanh::LeanObject,
    mut v_00_u03b2_2212_: *mut leanh::LeanObject,
    mut v_capacity_2213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = leanh::lean_unsigned_to_nat(0);
    v___x_2215_ = leanh::lean_unsigned_to_nat(4);
    v___x_2216_ = lean_nat_mul(v_capacity_2213_, v___x_2215_);
    v___x_2217_ = leanh::lean_unsigned_to_nat(3);
    v___x_2218_ = lean_nat_div(v___x_2216_, v___x_2217_);
    leanh::lean_dec(v___x_2216_);
    v___x_2219_ = l_Nat_nextPowerOfTwo(v___x_2218_);
    leanh::lean_dec(v___x_2218_);
    v___x_2220_ = leanh::lean_box(0);
    v___x_2221_ = lean_mk_array(v___x_2219_, v___x_2220_);
    v___x_2222_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2222_, 0, v___x_2214_);
    leanh::lean_ctor_set(v___x_2222_, 1, v___x_2221_);
    return v___x_2222_;
}
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity___boxed(
    mut v_00_u03b1_2223_: *mut leanh::LeanObject,
    mut v_00_u03b2_2224_: *mut leanh::LeanObject,
    mut v_capacity_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2226_ =
        l_Std_HashMap_Raw_emptyWithCapacity(v_00_u03b1_2223_, v_00_u03b2_2224_, v_capacity_2225_);
    leanh::lean_dec(v_capacity_2225_);
    return v_res_2226_;
}
pub unsafe fn _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2227_ = leanh::lean_box(0);
    v___x_2228_ = leanh::lean_unsigned_to_nat(16);
    v___x_2229_ = lean_mk_array(v___x_2228_, v___x_2227_);
    return v___x_2229_;
}
pub unsafe fn _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2231_ = leanh::lean_unsigned_to_nat(0);
    v___x_2232_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    leanh::lean_ctor_set(v___x_2232_, 1, v___x_2230_);
    return v___x_2232_;
}
pub unsafe fn l_Std_HashMap_Raw_instEmptyCollection(
    mut v_00_u03b1_2233_: *mut leanh::LeanObject,
    mut v_00_u03b2_2234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2235_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2235_;
}
pub unsafe fn l_Std_HashMap_Raw_instInhabited(
    mut v_00_u03b1_2236_: *mut leanh::LeanObject,
    mut v_00_u03b2_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2238_;
}
pub unsafe fn _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2279_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5;
    v___x_2280_ = l_String_toRawSubstring_x27(v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(
    mut v_x_2302_: *mut leanh::LeanObject,
    mut v_a_2303_: *mut leanh::LeanObject,
    mut v_a_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    v___x_2305_ = l_Std_HashMap_Raw_term___x7em___00__closed__4;
    leanh::lean_inc(v_x_2302_);
    v___x_2306_ = l_Lean_Syntax_isOfKind(v_x_2302_, v___x_2305_);
    if v___x_2306_ == 0 {
        let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2302_);
        v___x_2307_ = leanh::lean_box(1);
        v___x_2308_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
        leanh::lean_ctor_set(v___x_2308_, 1, v_a_2304_);
        return v___x_2308_;
    } else {
        let mut v_quotContext_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2316_: u8 = 0;
        let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2309_ = leanh::lean_ctor_get(v_a_2303_, 1);
        v_currMacroScope_2310_ = leanh::lean_ctor_get(v_a_2303_, 2);
        v_ref_2311_ = leanh::lean_ctor_get(v_a_2303_, 5);
        v___x_2312_ = leanh::lean_unsigned_to_nat(0);
        v___x_2313_ = l_Lean_Syntax_getArg(v_x_2302_, v___x_2312_);
        v___x_2314_ = leanh::lean_unsigned_to_nat(2);
        v___x_2315_ = l_Lean_Syntax_getArg(v_x_2302_, v___x_2314_);
        leanh::lean_dec(v_x_2302_);
        v___x_2316_ = 0;
        v___x_2317_ = l_Lean_SourceInfo_fromRef(v_ref_2311_, v___x_2316_);
        v___x_2318_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4;
        v___x_2319_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once), _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
        v___x_2320_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7;
        leanh::lean_inc(v_currMacroScope_2310_);
        leanh::lean_inc(v_quotContext_2309_);
        v___x_2321_ =
            l_Lean_addMacroScope(v_quotContext_2309_, v___x_2320_, v_currMacroScope_2310_);
        v___x_2322_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12;
        leanh::lean_inc_n(v___x_2317_, 2);
        v___x_2323_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2323_, 0, v___x_2317_);
        leanh::lean_ctor_set(v___x_2323_, 1, v___x_2319_);
        leanh::lean_ctor_set(v___x_2323_, 2, v___x_2321_);
        leanh::lean_ctor_set(v___x_2323_, 3, v___x_2322_);
        v___x_2324_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14;
        v___x_2325_ = l_Lean_Syntax_node2(v___x_2317_, v___x_2324_, v___x_2313_, v___x_2315_);
        v___x_2326_ = l_Lean_Syntax_node2(v___x_2317_, v___x_2318_, v___x_2323_, v___x_2325_);
        v___x_2327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2327_, 0, v___x_2326_);
        leanh::lean_ctor_set(v___x_2327_, 1, v_a_2304_);
        return v___x_2327_;
    }
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(
    mut v_x_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
    mut v_a_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(v_x_2328_, v_a_2329_, v_a_2330_);
    leanh::lean_dec_ref(v_a_2329_);
    return v_res_2331_;
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v_a_2336_: *mut leanh::LeanObject,
    mut v_a_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    v___x_2338_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4;
    leanh::lean_inc(v_x_2335_);
    v___x_2339_ = l_Lean_Syntax_isOfKind(v_x_2335_, v___x_2338_);
    if v___x_2339_ == 0 {
        let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2335_);
        v___x_2340_ = leanh::lean_box(0);
        v___x_2341_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2341_, 0, v___x_2340_);
        leanh::lean_ctor_set(v___x_2341_, 1, v_a_2337_);
        return v___x_2341_;
    } else {
        let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2345_: u8 = 0;
        v___x_2342_ = leanh::lean_unsigned_to_nat(0);
        v___x_2343_ = l_Lean_Syntax_getArg(v_x_2335_, v___x_2342_);
        v___x_2344_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1;
        leanh::lean_inc(v___x_2343_);
        v___x_2345_ = l_Lean_Syntax_isOfKind(v___x_2343_, v___x_2344_);
        if v___x_2345_ == 0 {
            let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2343_);
            leanh::lean_dec(v_x_2335_);
            v___x_2346_ = leanh::lean_box(0);
            v___x_2347_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2347_, 0, v___x_2346_);
            leanh::lean_ctor_set(v___x_2347_, 1, v_a_2337_);
            return v___x_2347_;
        } else {
            let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2351_: u8 = 0;
            v___x_2348_ = leanh::lean_unsigned_to_nat(1);
            v___x_2349_ = l_Lean_Syntax_getArg(v_x_2335_, v___x_2348_);
            leanh::lean_dec(v_x_2335_);
            v___x_2350_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_2349_);
            v___x_2351_ = l_Lean_Syntax_matchesNull(v___x_2349_, v___x_2350_);
            if v___x_2351_ == 0 {
                let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_2349_);
                leanh::lean_dec(v___x_2343_);
                v___x_2352_ = leanh::lean_box(0);
                v___x_2353_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2353_, 0, v___x_2352_);
                leanh::lean_ctor_set(v___x_2353_, 1, v_a_2337_);
                return v___x_2353_;
            } else {
                let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2357_: u8 = 0;
                let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2354_ = l_Lean_Syntax_getArg(v___x_2349_, v___x_2342_);
                v___x_2355_ = l_Lean_Syntax_getArg(v___x_2349_, v___x_2348_);
                leanh::lean_dec(v___x_2349_);
                v_ref_2356_ = l_Lean_replaceRef(v___x_2343_, v_a_2336_);
                leanh::lean_dec(v___x_2343_);
                v___x_2357_ = 0;
                v___x_2358_ = l_Lean_SourceInfo_fromRef(v_ref_2356_, v___x_2357_);
                leanh::lean_dec(v_ref_2356_);
                v___x_2359_ = l_Std_HashMap_Raw_term___x7em___00__closed__4;
                v___x_2360_ = l_Std_HashMap_Raw_term___x7em___00__closed__7;
                leanh::lean_inc(v___x_2358_);
                v___x_2361_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2361_, 0, v___x_2358_);
                leanh::lean_ctor_set(v___x_2361_, 1, v___x_2360_);
                v___x_2362_ = l_Lean_Syntax_node3(
                    v___x_2358_,
                    v___x_2359_,
                    v___x_2354_,
                    v___x_2361_,
                    v___x_2355_,
                );
                v___x_2363_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2363_, 0, v___x_2362_);
                leanh::lean_ctor_set(v___x_2363_, 1, v_a_2337_);
                return v___x_2363_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(
    mut v_x_2364_: *mut leanh::LeanObject,
    mut v_a_2365_: *mut leanh::LeanObject,
    mut v_a_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2367_ =
        l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(
            v_x_2364_, v_a_2365_, v_a_2366_,
        );
    leanh::lean_dec(v_a_2365_);
    return v_res_2367_;
}
pub unsafe fn l_Std_HashMap_Raw_insert___redArg(
    mut v_beq_2368_: *mut leanh::LeanObject,
    mut v_inst_2369_: *mut leanh::LeanObject,
    mut v_m_2370_: *mut leanh::LeanObject,
    mut v_a_2371_: *mut leanh::LeanObject,
    mut v_b_2372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: u8 = 0;
    v_buckets_2373_ = leanh::lean_ctor_get(v_m_2370_, 1);
    v___x_2374_ = leanh::lean_unsigned_to_nat(0);
    v___x_2375_ = lean_array_get_size(v_buckets_2373_);
    v___x_2376_ = lean_nat_dec_lt(v___x_2374_, v___x_2375_);
    if v___x_2376_ == 0 {
        leanh::lean_dec(v_b_2372_);
        leanh::lean_dec(v_a_2371_);
        leanh::lean_dec_ref(v_inst_2369_);
        leanh::lean_dec_ref(v_beq_2368_);
        return v_m_2370_;
    } else {
        let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2377_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_beq_2368_,
            v_inst_2369_,
            v_m_2370_,
            v_a_2371_,
            v_b_2372_,
        );
        return v___x_2377_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_insert(
    mut v_00_u03b1_2378_: *mut leanh::LeanObject,
    mut v_00_u03b2_2379_: *mut leanh::LeanObject,
    mut v_beq_2380_: *mut leanh::LeanObject,
    mut v_inst_2381_: *mut leanh::LeanObject,
    mut v_m_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
    mut v_b_2384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    v_buckets_2385_ = leanh::lean_ctor_get(v_m_2382_, 1);
    v___x_2386_ = leanh::lean_unsigned_to_nat(0);
    v___x_2387_ = lean_array_get_size(v_buckets_2385_);
    v___x_2388_ = lean_nat_dec_lt(v___x_2386_, v___x_2387_);
    if v___x_2388_ == 0 {
        leanh::lean_dec(v_b_2384_);
        leanh::lean_dec(v_a_2383_);
        leanh::lean_dec_ref(v_inst_2381_);
        leanh::lean_dec_ref(v_beq_2380_);
        return v_m_2382_;
    } else {
        let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2389_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_beq_2380_,
            v_inst_2381_,
            v_m_2382_,
            v_a_2383_,
            v_b_2384_,
        );
        return v___x_2389_;
    }
}
pub unsafe fn _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2390_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2391_ = lean_array_get_size(v___x_2390_);
    return v___x_2391_;
}
pub unsafe fn _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1()
-> u8 {
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    v___x_2392_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0,
    );
    v___x_2393_ = leanh::lean_unsigned_to_nat(0);
    v___x_2394_ = lean_nat_dec_lt(v___x_2393_, v___x_2392_);
    return v___x_2394_;
}
pub unsafe fn l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2395_: *mut leanh::LeanObject,
    mut v_inst_2396_: *mut leanh::LeanObject,
    mut v_x_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    v_fst_2398_ = leanh::lean_ctor_get(v_x_2397_, 0);
    leanh::lean_inc(v_fst_2398_);
    v_snd_2399_ = leanh::lean_ctor_get(v_x_2397_, 1);
    leanh::lean_inc(v_snd_2399_);
    leanh::lean_dec_ref(v_x_2397_);
    v___x_2400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_2401_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2401_ == 0 {
        leanh::lean_dec(v_snd_2399_);
        leanh::lean_dec(v_fst_2398_);
        leanh::lean_dec_ref(v_inst_2396_);
        leanh::lean_dec_ref(v_inst_2395_);
        return v___x_2400_;
    } else {
        let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2402_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_2395_,
            v_inst_2396_,
            v___x_2400_,
            v_fst_2398_,
            v_snd_2399_,
        );
        return v___x_2402_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(
    mut v_inst_2403_: *mut leanh::LeanObject,
    mut v_inst_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2405_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2405_, 0, v_inst_2403_);
    leanh::lean_closure_set(v___f_2405_, 1, v_inst_2404_);
    return v___f_2405_;
}
pub unsafe fn l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(
    mut v_00_u03b1_2406_: *mut leanh::LeanObject,
    mut v_00_u03b2_2407_: *mut leanh::LeanObject,
    mut v_inst_2408_: *mut leanh::LeanObject,
    mut v_inst_2409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2410_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2410_, 0, v_inst_2408_);
    leanh::lean_closure_set(v___f_2410_, 1, v_inst_2409_);
    return v___f_2410_;
}
pub unsafe fn l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2411_: *mut leanh::LeanObject,
    mut v_inst_2412_: *mut leanh::LeanObject,
    mut v_x_2413_: *mut leanh::LeanObject,
    mut v_s_2414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    v_fst_2415_ = leanh::lean_ctor_get(v_x_2413_, 0);
    leanh::lean_inc(v_fst_2415_);
    v_snd_2416_ = leanh::lean_ctor_get(v_x_2413_, 1);
    leanh::lean_inc(v_snd_2416_);
    leanh::lean_dec_ref(v_x_2413_);
    v_buckets_2417_ = leanh::lean_ctor_get(v_s_2414_, 1);
    v___x_2418_ = leanh::lean_unsigned_to_nat(0);
    v___x_2419_ = lean_array_get_size(v_buckets_2417_);
    v___x_2420_ = lean_nat_dec_lt(v___x_2418_, v___x_2419_);
    if v___x_2420_ == 0 {
        leanh::lean_dec(v_snd_2416_);
        leanh::lean_dec(v_fst_2415_);
        leanh::lean_dec_ref(v_inst_2412_);
        leanh::lean_dec_ref(v_inst_2411_);
        return v_s_2414_;
    } else {
        let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_2411_,
            v_inst_2412_,
            v_s_2414_,
            v_fst_2415_,
            v_snd_2416_,
        );
        return v___x_2421_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(
    mut v_inst_2422_: *mut leanh::LeanObject,
    mut v_inst_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2424_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2424_, 0, v_inst_2422_);
    leanh::lean_closure_set(v___f_2424_, 1, v_inst_2423_);
    return v___f_2424_;
}
pub unsafe fn l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(
    mut v_00_u03b1_2425_: *mut leanh::LeanObject,
    mut v_00_u03b2_2426_: *mut leanh::LeanObject,
    mut v_inst_2427_: *mut leanh::LeanObject,
    mut v_inst_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2429_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2429_, 0, v_inst_2427_);
    leanh::lean_closure_set(v___f_2429_, 1, v_inst_2428_);
    return v___f_2429_;
}
pub unsafe fn l_Std_HashMap_Raw_insertIfNew___redArg(
    mut v_inst_2430_: *mut leanh::LeanObject,
    mut v_inst_2431_: *mut leanh::LeanObject,
    mut v_m_2432_: *mut leanh::LeanObject,
    mut v_a_2433_: *mut leanh::LeanObject,
    mut v_b_2434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    v_buckets_2435_ = leanh::lean_ctor_get(v_m_2432_, 1);
    v___x_2436_ = leanh::lean_unsigned_to_nat(0);
    v___x_2437_ = lean_array_get_size(v_buckets_2435_);
    v___x_2438_ = lean_nat_dec_lt(v___x_2436_, v___x_2437_);
    if v___x_2438_ == 0 {
        leanh::lean_dec(v_b_2434_);
        leanh::lean_dec(v_a_2433_);
        leanh::lean_dec_ref(v_inst_2431_);
        leanh::lean_dec_ref(v_inst_2430_);
        return v_m_2432_;
    } else {
        let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2439_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_2430_,
            v_inst_2431_,
            v_m_2432_,
            v_a_2433_,
            v_b_2434_,
        );
        return v___x_2439_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_insertIfNew(
    mut v_00_u03b1_2440_: *mut leanh::LeanObject,
    mut v_00_u03b2_2441_: *mut leanh::LeanObject,
    mut v_inst_2442_: *mut leanh::LeanObject,
    mut v_inst_2443_: *mut leanh::LeanObject,
    mut v_m_2444_: *mut leanh::LeanObject,
    mut v_a_2445_: *mut leanh::LeanObject,
    mut v_b_2446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    v_buckets_2447_ = leanh::lean_ctor_get(v_m_2444_, 1);
    v___x_2448_ = leanh::lean_unsigned_to_nat(0);
    v___x_2449_ = lean_array_get_size(v_buckets_2447_);
    v___x_2450_ = lean_nat_dec_lt(v___x_2448_, v___x_2449_);
    if v___x_2450_ == 0 {
        leanh::lean_dec(v_b_2446_);
        leanh::lean_dec(v_a_2445_);
        leanh::lean_dec_ref(v_inst_2443_);
        leanh::lean_dec_ref(v_inst_2442_);
        return v_m_2444_;
    } else {
        let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2451_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v_inst_2442_,
            v_inst_2443_,
            v_m_2444_,
            v_a_2445_,
            v_b_2446_,
        );
        return v___x_2451_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_containsThenInsert___redArg(
    mut v_inst_2452_: *mut leanh::LeanObject,
    mut v_inst_2453_: *mut leanh::LeanObject,
    mut v_m_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_b_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: u64 = 0;
    let mut v___x_2469_: u64 = 0;
    let mut v___x_2470_: u64 = 0;
    let mut v___x_2471_: u64 = 0;
    let mut v_fold_2472_: u64 = 0;
    let mut v___x_2473_: u64 = 0;
    let mut v___x_2474_: u64 = 0;
    let mut v___x_2475_: u64 = 0;
    let mut v___x_2476_: usize = 0;
    let mut v___x_2477_: usize = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: usize = 0;
    let mut v___x_2480_: usize = 0;
    let mut v_bkt_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: u8 = 0;
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v_val_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut v_unused_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2457_ = leanh::lean_ctor_get(v_m_2454_, 0);
                v_buckets_2458_ = leanh::lean_ctor_get(v_m_2454_, 1);
                v___x_2459_ = leanh::lean_unsigned_to_nat(0);
                v___x_2460_ = lean_array_get_size(v_buckets_2458_);
                v___x_2461_ = lean_nat_dec_lt(v___x_2459_, v___x_2460_);
                if v___x_2461_ == 0 {
                    leanh::lean_dec(v_b_2456_);
                    leanh::lean_dec(v_a_2455_);
                    leanh::lean_dec_ref(v_inst_2453_);
                    leanh::lean_dec_ref(v_inst_2452_);
                    v___x_2462_ = leanh::lean_box((v___x_2461_) as usize);
                    v___x_2463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2463_, 0, v___x_2462_);
                    leanh::lean_ctor_set(v___x_2463_, 1, v_m_2454_);
                    return v___x_2463_;
                } else {
                    leanh::lean_inc_ref(v_buckets_2458_);
                    leanh::lean_inc(v_size_2457_);
                    v_isSharedCheck_2513_ = (!leanh::lean_is_exclusive(v_m_2454_)) as u8;
                    if v_isSharedCheck_2513_ == 0 {
                        v_unused_2514_ = leanh::lean_ctor_get(v_m_2454_, 1);
                        leanh::lean_dec(v_unused_2514_);
                        v_unused_2515_ = leanh::lean_ctor_get(v_m_2454_, 0);
                        leanh::lean_dec(v_unused_2515_);
                        v___x_2465_ = v_m_2454_;
                        v_isShared_2466_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2454_);
                        v___x_2465_ = leanh::lean_box(0);
                        v_isShared_2466_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_2453_);
                leanh::lean_inc_n(v_a_2455_, 2);
                v___x_2467_ = leanh::lean_apply_1(v_inst_2453_, v_a_2455_);
                v___x_2468_ = 32u64;
                v___x_2469_ = leanh::lean_unbox_uint64(v___x_2467_);
                v___x_2470_ = lean_uint64_shift_right(v___x_2469_, v___x_2468_);
                v___x_2471_ = leanh::lean_unbox_uint64(v___x_2467_);
                leanh::lean_dec_ref(v___x_2467_);
                v_fold_2472_ = lean_uint64_xor(v___x_2471_, v___x_2470_);
                v___x_2473_ = 16u64;
                v___x_2474_ = lean_uint64_shift_right(v_fold_2472_, v___x_2473_);
                v___x_2475_ = lean_uint64_xor(v_fold_2472_, v___x_2474_);
                v___x_2476_ = lean_uint64_to_usize(v___x_2475_);
                v___x_2477_ = lean_usize_of_nat(v___x_2460_);
                v___x_2478_ = 1usize;
                v___x_2479_ = lean_usize_sub(v___x_2477_, v___x_2478_);
                v___x_2480_ = lean_usize_land(v___x_2476_, v___x_2479_);
                v_bkt_2481_ = lean_array_uget_borrowed(v_buckets_2458_, v___x_2480_);
                leanh::lean_inc(v_bkt_2481_);
                leanh::lean_inc_ref(v_inst_2452_);
                v___x_2482_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2452_,
                    v_a_2455_,
                    v_bkt_2481_,
                );
                if v___x_2482_ == 0 {
                    leanh::lean_dec_ref(v_inst_2452_);
                    v___x_2483_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2484_ = lean_nat_add(v_size_2457_, v___x_2483_);
                    leanh::lean_dec(v_size_2457_);
                    leanh::lean_inc(v_bkt_2481_);
                    v___x_2485_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2485_, 0, v_a_2455_);
                    leanh::lean_ctor_set(v___x_2485_, 1, v_b_2456_);
                    leanh::lean_ctor_set(v___x_2485_, 2, v_bkt_2481_);
                    v_buckets_x27_2486_ =
                        lean_array_uset(v_buckets_2458_, v___x_2480_, v___x_2485_);
                    v___x_2487_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2488_ = lean_nat_mul(v_size_x27_2484_, v___x_2487_);
                    v___x_2489_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2490_ = lean_nat_div(v___x_2488_, v___x_2489_);
                    leanh::lean_dec(v___x_2488_);
                    v___x_2491_ = lean_array_get_size(v_buckets_x27_2486_);
                    v___x_2492_ = lean_nat_dec_le(v___x_2490_, v___x_2491_);
                    leanh::lean_dec(v___x_2490_);
                    if v___x_2492_ == 0 {
                        v_val_2493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2453_,
                            v_buckets_x27_2486_,
                        );
                        if v_isShared_2466_ == 0 {
                            leanh::lean_ctor_set(v___x_2465_, 1, v_val_2493_);
                            leanh::lean_ctor_set(v___x_2465_, 0, v_size_x27_2484_);
                            v___x_2495_ = v___x_2465_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2498_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2498_,
                                0,
                                v_size_x27_2484_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_val_2493_);
                            v___x_2495_ = v_reuseFailAlloc_2498_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_2453_);
                        if v_isShared_2466_ == 0 {
                            leanh::lean_ctor_set(v___x_2465_, 1, v_buckets_x27_2486_);
                            leanh::lean_ctor_set(v___x_2465_, 0, v_size_x27_2484_);
                            v___x_2500_ = v___x_2465_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2503_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2503_,
                                0,
                                v_size_x27_2484_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2503_,
                                1,
                                v_buckets_x27_2486_,
                            );
                            v___x_2500_ = v_reuseFailAlloc_2503_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2481_);
                    leanh::lean_dec_ref(v_inst_2453_);
                    v___x_2504_ = leanh::lean_box(0);
                    v_buckets_x27_2505_ =
                        lean_array_uset(v_buckets_2458_, v___x_2480_, v___x_2504_);
                    v___x_2506_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_2452_,
                        v_a_2455_,
                        v_b_2456_,
                        v_bkt_2481_,
                    );
                    v___x_2507_ = lean_array_uset(v_buckets_x27_2505_, v___x_2480_, v___x_2506_);
                    if v_isShared_2466_ == 0 {
                        leanh::lean_ctor_set(v___x_2465_, 1, v___x_2507_);
                        v___x_2509_ = v___x_2465_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2512_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_size_2457_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2507_);
                        v___x_2509_ = v_reuseFailAlloc_2512_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2496_ = leanh::lean_box((v___x_2482_) as usize);
                v___x_2497_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2497_, 0, v___x_2496_);
                leanh::lean_ctor_set(v___x_2497_, 1, v___x_2495_);
                return v___x_2497_;
            }
            3 => {
                v___x_2501_ = leanh::lean_box((v___x_2482_) as usize);
                v___x_2502_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2502_, 0, v___x_2501_);
                leanh::lean_ctor_set(v___x_2502_, 1, v___x_2500_);
                return v___x_2502_;
            }
            4 => {
                v___x_2510_ = leanh::lean_box((v___x_2482_) as usize);
                v___x_2511_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2511_, 0, v___x_2510_);
                leanh::lean_ctor_set(v___x_2511_, 1, v___x_2509_);
                return v___x_2511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_containsThenInsert(
    mut v_00_u03b1_2516_: *mut leanh::LeanObject,
    mut v_00_u03b2_2517_: *mut leanh::LeanObject,
    mut v_inst_2518_: *mut leanh::LeanObject,
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v_m_2520_: *mut leanh::LeanObject,
    mut v_a_2521_: *mut leanh::LeanObject,
    mut v_b_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: u64 = 0;
    let mut v___x_2535_: u64 = 0;
    let mut v___x_2536_: u64 = 0;
    let mut v___x_2537_: u64 = 0;
    let mut v_fold_2538_: u64 = 0;
    let mut v___x_2539_: u64 = 0;
    let mut v___x_2540_: u64 = 0;
    let mut v___x_2541_: u64 = 0;
    let mut v___x_2542_: usize = 0;
    let mut v___x_2543_: usize = 0;
    let mut v___x_2544_: usize = 0;
    let mut v___x_2545_: usize = 0;
    let mut v___x_2546_: usize = 0;
    let mut v_bkt_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    let mut v_val_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_unused_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2523_ = leanh::lean_ctor_get(v_m_2520_, 0);
                v_buckets_2524_ = leanh::lean_ctor_get(v_m_2520_, 1);
                v___x_2525_ = leanh::lean_unsigned_to_nat(0);
                v___x_2526_ = lean_array_get_size(v_buckets_2524_);
                v___x_2527_ = lean_nat_dec_lt(v___x_2525_, v___x_2526_);
                if v___x_2527_ == 0 {
                    leanh::lean_dec(v_b_2522_);
                    leanh::lean_dec(v_a_2521_);
                    leanh::lean_dec_ref(v_inst_2519_);
                    leanh::lean_dec_ref(v_inst_2518_);
                    v___x_2528_ = leanh::lean_box((v___x_2527_) as usize);
                    v___x_2529_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2529_, 0, v___x_2528_);
                    leanh::lean_ctor_set(v___x_2529_, 1, v_m_2520_);
                    return v___x_2529_;
                } else {
                    leanh::lean_inc_ref(v_buckets_2524_);
                    leanh::lean_inc(v_size_2523_);
                    v_isSharedCheck_2579_ = (!leanh::lean_is_exclusive(v_m_2520_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v_unused_2580_ = leanh::lean_ctor_get(v_m_2520_, 1);
                        leanh::lean_dec(v_unused_2580_);
                        v_unused_2581_ = leanh::lean_ctor_get(v_m_2520_, 0);
                        leanh::lean_dec(v_unused_2581_);
                        v___x_2531_ = v_m_2520_;
                        v_isShared_2532_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2520_);
                        v___x_2531_ = leanh::lean_box(0);
                        v_isShared_2532_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_2519_);
                leanh::lean_inc_n(v_a_2521_, 2);
                v___x_2533_ = leanh::lean_apply_1(v_inst_2519_, v_a_2521_);
                v___x_2534_ = 32u64;
                v___x_2535_ = leanh::lean_unbox_uint64(v___x_2533_);
                v___x_2536_ = lean_uint64_shift_right(v___x_2535_, v___x_2534_);
                v___x_2537_ = leanh::lean_unbox_uint64(v___x_2533_);
                leanh::lean_dec_ref(v___x_2533_);
                v_fold_2538_ = lean_uint64_xor(v___x_2537_, v___x_2536_);
                v___x_2539_ = 16u64;
                v___x_2540_ = lean_uint64_shift_right(v_fold_2538_, v___x_2539_);
                v___x_2541_ = lean_uint64_xor(v_fold_2538_, v___x_2540_);
                v___x_2542_ = lean_uint64_to_usize(v___x_2541_);
                v___x_2543_ = lean_usize_of_nat(v___x_2526_);
                v___x_2544_ = 1usize;
                v___x_2545_ = lean_usize_sub(v___x_2543_, v___x_2544_);
                v___x_2546_ = lean_usize_land(v___x_2542_, v___x_2545_);
                v_bkt_2547_ = lean_array_uget_borrowed(v_buckets_2524_, v___x_2546_);
                leanh::lean_inc(v_bkt_2547_);
                leanh::lean_inc_ref(v_inst_2518_);
                v___x_2548_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2518_,
                    v_a_2521_,
                    v_bkt_2547_,
                );
                if v___x_2548_ == 0 {
                    leanh::lean_dec_ref(v_inst_2518_);
                    v___x_2549_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2550_ = lean_nat_add(v_size_2523_, v___x_2549_);
                    leanh::lean_dec(v_size_2523_);
                    leanh::lean_inc(v_bkt_2547_);
                    v___x_2551_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2551_, 0, v_a_2521_);
                    leanh::lean_ctor_set(v___x_2551_, 1, v_b_2522_);
                    leanh::lean_ctor_set(v___x_2551_, 2, v_bkt_2547_);
                    v_buckets_x27_2552_ =
                        lean_array_uset(v_buckets_2524_, v___x_2546_, v___x_2551_);
                    v___x_2553_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2554_ = lean_nat_mul(v_size_x27_2550_, v___x_2553_);
                    v___x_2555_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2556_ = lean_nat_div(v___x_2554_, v___x_2555_);
                    leanh::lean_dec(v___x_2554_);
                    v___x_2557_ = lean_array_get_size(v_buckets_x27_2552_);
                    v___x_2558_ = lean_nat_dec_le(v___x_2556_, v___x_2557_);
                    leanh::lean_dec(v___x_2556_);
                    if v___x_2558_ == 0 {
                        v_val_2559_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2519_,
                            v_buckets_x27_2552_,
                        );
                        if v_isShared_2532_ == 0 {
                            leanh::lean_ctor_set(v___x_2531_, 1, v_val_2559_);
                            leanh::lean_ctor_set(v___x_2531_, 0, v_size_x27_2550_);
                            v___x_2561_ = v___x_2531_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2564_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2564_,
                                0,
                                v_size_x27_2550_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_val_2559_);
                            v___x_2561_ = v_reuseFailAlloc_2564_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_2519_);
                        if v_isShared_2532_ == 0 {
                            leanh::lean_ctor_set(v___x_2531_, 1, v_buckets_x27_2552_);
                            leanh::lean_ctor_set(v___x_2531_, 0, v_size_x27_2550_);
                            v___x_2566_ = v___x_2531_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2569_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2569_,
                                0,
                                v_size_x27_2550_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2569_,
                                1,
                                v_buckets_x27_2552_,
                            );
                            v___x_2566_ = v_reuseFailAlloc_2569_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2547_);
                    leanh::lean_dec_ref(v_inst_2519_);
                    v___x_2570_ = leanh::lean_box(0);
                    v_buckets_x27_2571_ =
                        lean_array_uset(v_buckets_2524_, v___x_2546_, v___x_2570_);
                    v___x_2572_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_2518_,
                        v_a_2521_,
                        v_b_2522_,
                        v_bkt_2547_,
                    );
                    v___x_2573_ = lean_array_uset(v_buckets_x27_2571_, v___x_2546_, v___x_2572_);
                    if v_isShared_2532_ == 0 {
                        leanh::lean_ctor_set(v___x_2531_, 1, v___x_2573_);
                        v___x_2575_ = v___x_2531_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2578_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_size_2523_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2573_);
                        v___x_2575_ = v_reuseFailAlloc_2578_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2562_ = leanh::lean_box((v___x_2548_) as usize);
                v___x_2563_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2563_, 0, v___x_2562_);
                leanh::lean_ctor_set(v___x_2563_, 1, v___x_2561_);
                return v___x_2563_;
            }
            3 => {
                v___x_2567_ = leanh::lean_box((v___x_2548_) as usize);
                v___x_2568_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                leanh::lean_ctor_set(v___x_2568_, 1, v___x_2566_);
                return v___x_2568_;
            }
            4 => {
                v___x_2576_ = leanh::lean_box((v___x_2548_) as usize);
                v___x_2577_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2577_, 0, v___x_2576_);
                leanh::lean_ctor_set(v___x_2577_, 1, v___x_2575_);
                return v___x_2577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(
    mut v_inst_2582_: *mut leanh::LeanObject,
    mut v_inst_2583_: *mut leanh::LeanObject,
    mut v_m_2584_: *mut leanh::LeanObject,
    mut v_a_2585_: *mut leanh::LeanObject,
    mut v_b_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: u64 = 0;
    let mut v___x_2596_: u64 = 0;
    let mut v___x_2597_: u64 = 0;
    let mut v___x_2598_: u64 = 0;
    let mut v_fold_2599_: u64 = 0;
    let mut v___x_2600_: u64 = 0;
    let mut v___x_2601_: u64 = 0;
    let mut v___x_2602_: u64 = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: usize = 0;
    let mut v___x_2605_: usize = 0;
    let mut v___x_2606_: usize = 0;
    let mut v___x_2607_: usize = 0;
    let mut v_bkt_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v_val_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_unused_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2587_ = leanh::lean_ctor_get(v_m_2584_, 0);
                v_buckets_2588_ = leanh::lean_ctor_get(v_m_2584_, 1);
                v___x_2589_ = leanh::lean_unsigned_to_nat(0);
                v___x_2590_ = lean_array_get_size(v_buckets_2588_);
                v___x_2591_ = lean_nat_dec_lt(v___x_2589_, v___x_2590_);
                if v___x_2591_ == 0 {
                    leanh::lean_dec(v_b_2586_);
                    leanh::lean_dec(v_a_2585_);
                    leanh::lean_dec_ref(v_inst_2583_);
                    leanh::lean_dec_ref(v_inst_2582_);
                    v___x_2592_ = leanh::lean_box((v___x_2591_) as usize);
                    v___x_2593_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2593_, 0, v___x_2592_);
                    leanh::lean_ctor_set(v___x_2593_, 1, v_m_2584_);
                    return v___x_2593_;
                } else {
                    leanh::lean_inc_ref(v_inst_2583_);
                    leanh::lean_inc_n(v_a_2585_, 2);
                    v___x_2594_ = leanh::lean_apply_1(v_inst_2583_, v_a_2585_);
                    v___x_2595_ = 32u64;
                    v___x_2596_ = leanh::lean_unbox_uint64(v___x_2594_);
                    v___x_2597_ = lean_uint64_shift_right(v___x_2596_, v___x_2595_);
                    v___x_2598_ = leanh::lean_unbox_uint64(v___x_2594_);
                    leanh::lean_dec_ref(v___x_2594_);
                    v_fold_2599_ = lean_uint64_xor(v___x_2598_, v___x_2597_);
                    v___x_2600_ = 16u64;
                    v___x_2601_ = lean_uint64_shift_right(v_fold_2599_, v___x_2600_);
                    v___x_2602_ = lean_uint64_xor(v_fold_2599_, v___x_2601_);
                    v___x_2603_ = lean_uint64_to_usize(v___x_2602_);
                    v___x_2604_ = lean_usize_of_nat(v___x_2590_);
                    v___x_2605_ = 1usize;
                    v___x_2606_ = lean_usize_sub(v___x_2604_, v___x_2605_);
                    v___x_2607_ = lean_usize_land(v___x_2603_, v___x_2606_);
                    v_bkt_2608_ = lean_array_uget_borrowed(v_buckets_2588_, v___x_2607_);
                    leanh::lean_inc(v_bkt_2608_);
                    v___x_2609_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_2582_,
                        v_a_2585_,
                        v_bkt_2608_,
                    );
                    if v___x_2609_ == 0 {
                        leanh::lean_inc_ref(v_buckets_2588_);
                        leanh::lean_inc(v_size_2587_);
                        v_isSharedCheck_2634_ = (!leanh::lean_is_exclusive(v_m_2584_)) as u8;
                        if v_isSharedCheck_2634_ == 0 {
                            v_unused_2635_ = leanh::lean_ctor_get(v_m_2584_, 1);
                            leanh::lean_dec(v_unused_2635_);
                            v_unused_2636_ = leanh::lean_ctor_get(v_m_2584_, 0);
                            leanh::lean_dec(v_unused_2636_);
                            v___x_2611_ = v_m_2584_;
                            v_isShared_2612_ = v_isSharedCheck_2634_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_2584_);
                            v___x_2611_ = leanh::lean_box(0);
                            v_isShared_2612_ = v_isSharedCheck_2634_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_2586_);
                        leanh::lean_dec(v_a_2585_);
                        leanh::lean_dec_ref(v_inst_2583_);
                        v___x_2637_ = leanh::lean_box((v___x_2609_) as usize);
                        v___x_2638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2638_, 0, v___x_2637_);
                        leanh::lean_ctor_set(v___x_2638_, 1, v_m_2584_);
                        return v___x_2638_;
                    }
                }
            }
            1 => {
                v___x_2613_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2614_ = lean_nat_add(v_size_2587_, v___x_2613_);
                leanh::lean_dec(v_size_2587_);
                leanh::lean_inc(v_bkt_2608_);
                v___x_2615_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2615_, 0, v_a_2585_);
                leanh::lean_ctor_set(v___x_2615_, 1, v_b_2586_);
                leanh::lean_ctor_set(v___x_2615_, 2, v_bkt_2608_);
                v_buckets_x27_2616_ = lean_array_uset(v_buckets_2588_, v___x_2607_, v___x_2615_);
                v___x_2617_ = leanh::lean_unsigned_to_nat(4);
                v___x_2618_ = lean_nat_mul(v_size_x27_2614_, v___x_2617_);
                v___x_2619_ = leanh::lean_unsigned_to_nat(3);
                v___x_2620_ = lean_nat_div(v___x_2618_, v___x_2619_);
                leanh::lean_dec(v___x_2618_);
                v___x_2621_ = lean_array_get_size(v_buckets_x27_2616_);
                v___x_2622_ = lean_nat_dec_le(v___x_2620_, v___x_2621_);
                leanh::lean_dec(v___x_2620_);
                if v___x_2622_ == 0 {
                    v_val_2623_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2583_,
                        v_buckets_x27_2616_,
                    );
                    if v_isShared_2612_ == 0 {
                        leanh::lean_ctor_set(v___x_2611_, 1, v_val_2623_);
                        leanh::lean_ctor_set(v___x_2611_, 0, v_size_x27_2614_);
                        v___x_2625_ = v___x_2611_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2628_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_size_x27_2614_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_val_2623_);
                        v___x_2625_ = v_reuseFailAlloc_2628_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2583_);
                    if v_isShared_2612_ == 0 {
                        leanh::lean_ctor_set(v___x_2611_, 1, v_buckets_x27_2616_);
                        leanh::lean_ctor_set(v___x_2611_, 0, v_size_x27_2614_);
                        v___x_2630_ = v___x_2611_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_size_x27_2614_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_buckets_x27_2616_);
                        v___x_2630_ = v_reuseFailAlloc_2633_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2626_ = leanh::lean_box((v___x_2609_) as usize);
                v___x_2627_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2627_, 0, v___x_2626_);
                leanh::lean_ctor_set(v___x_2627_, 1, v___x_2625_);
                return v___x_2627_;
            }
            3 => {
                v___x_2631_ = leanh::lean_box((v___x_2609_) as usize);
                v___x_2632_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2632_, 0, v___x_2631_);
                leanh::lean_ctor_set(v___x_2632_, 1, v___x_2630_);
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_containsThenInsertIfNew(
    mut v_00_u03b1_2639_: *mut leanh::LeanObject,
    mut v_00_u03b2_2640_: *mut leanh::LeanObject,
    mut v_inst_2641_: *mut leanh::LeanObject,
    mut v_inst_2642_: *mut leanh::LeanObject,
    mut v_m_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_b_2645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: u64 = 0;
    let mut v___x_2655_: u64 = 0;
    let mut v___x_2656_: u64 = 0;
    let mut v___x_2657_: u64 = 0;
    let mut v_fold_2658_: u64 = 0;
    let mut v___x_2659_: u64 = 0;
    let mut v___x_2660_: u64 = 0;
    let mut v___x_2661_: u64 = 0;
    let mut v___x_2662_: usize = 0;
    let mut v___x_2663_: usize = 0;
    let mut v___x_2664_: usize = 0;
    let mut v___x_2665_: usize = 0;
    let mut v___x_2666_: usize = 0;
    let mut v_bkt_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v_val_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_unused_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2646_ = leanh::lean_ctor_get(v_m_2643_, 0);
                v_buckets_2647_ = leanh::lean_ctor_get(v_m_2643_, 1);
                v___x_2648_ = leanh::lean_unsigned_to_nat(0);
                v___x_2649_ = lean_array_get_size(v_buckets_2647_);
                v___x_2650_ = lean_nat_dec_lt(v___x_2648_, v___x_2649_);
                if v___x_2650_ == 0 {
                    leanh::lean_dec(v_b_2645_);
                    leanh::lean_dec(v_a_2644_);
                    leanh::lean_dec_ref(v_inst_2642_);
                    leanh::lean_dec_ref(v_inst_2641_);
                    v___x_2651_ = leanh::lean_box((v___x_2650_) as usize);
                    v___x_2652_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2652_, 0, v___x_2651_);
                    leanh::lean_ctor_set(v___x_2652_, 1, v_m_2643_);
                    return v___x_2652_;
                } else {
                    leanh::lean_inc_ref(v_inst_2642_);
                    leanh::lean_inc_n(v_a_2644_, 2);
                    v___x_2653_ = leanh::lean_apply_1(v_inst_2642_, v_a_2644_);
                    v___x_2654_ = 32u64;
                    v___x_2655_ = leanh::lean_unbox_uint64(v___x_2653_);
                    v___x_2656_ = lean_uint64_shift_right(v___x_2655_, v___x_2654_);
                    v___x_2657_ = leanh::lean_unbox_uint64(v___x_2653_);
                    leanh::lean_dec_ref(v___x_2653_);
                    v_fold_2658_ = lean_uint64_xor(v___x_2657_, v___x_2656_);
                    v___x_2659_ = 16u64;
                    v___x_2660_ = lean_uint64_shift_right(v_fold_2658_, v___x_2659_);
                    v___x_2661_ = lean_uint64_xor(v_fold_2658_, v___x_2660_);
                    v___x_2662_ = lean_uint64_to_usize(v___x_2661_);
                    v___x_2663_ = lean_usize_of_nat(v___x_2649_);
                    v___x_2664_ = 1usize;
                    v___x_2665_ = lean_usize_sub(v___x_2663_, v___x_2664_);
                    v___x_2666_ = lean_usize_land(v___x_2662_, v___x_2665_);
                    v_bkt_2667_ = lean_array_uget_borrowed(v_buckets_2647_, v___x_2666_);
                    leanh::lean_inc(v_bkt_2667_);
                    v___x_2668_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_2641_,
                        v_a_2644_,
                        v_bkt_2667_,
                    );
                    if v___x_2668_ == 0 {
                        leanh::lean_inc_ref(v_buckets_2647_);
                        leanh::lean_inc(v_size_2646_);
                        v_isSharedCheck_2693_ = (!leanh::lean_is_exclusive(v_m_2643_)) as u8;
                        if v_isSharedCheck_2693_ == 0 {
                            v_unused_2694_ = leanh::lean_ctor_get(v_m_2643_, 1);
                            leanh::lean_dec(v_unused_2694_);
                            v_unused_2695_ = leanh::lean_ctor_get(v_m_2643_, 0);
                            leanh::lean_dec(v_unused_2695_);
                            v___x_2670_ = v_m_2643_;
                            v_isShared_2671_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_2643_);
                            v___x_2670_ = leanh::lean_box(0);
                            v_isShared_2671_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_2645_);
                        leanh::lean_dec(v_a_2644_);
                        leanh::lean_dec_ref(v_inst_2642_);
                        v___x_2696_ = leanh::lean_box((v___x_2668_) as usize);
                        v___x_2697_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2697_, 0, v___x_2696_);
                        leanh::lean_ctor_set(v___x_2697_, 1, v_m_2643_);
                        return v___x_2697_;
                    }
                }
            }
            1 => {
                v___x_2672_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2673_ = lean_nat_add(v_size_2646_, v___x_2672_);
                leanh::lean_dec(v_size_2646_);
                leanh::lean_inc(v_bkt_2667_);
                v___x_2674_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2674_, 0, v_a_2644_);
                leanh::lean_ctor_set(v___x_2674_, 1, v_b_2645_);
                leanh::lean_ctor_set(v___x_2674_, 2, v_bkt_2667_);
                v_buckets_x27_2675_ = lean_array_uset(v_buckets_2647_, v___x_2666_, v___x_2674_);
                v___x_2676_ = leanh::lean_unsigned_to_nat(4);
                v___x_2677_ = lean_nat_mul(v_size_x27_2673_, v___x_2676_);
                v___x_2678_ = leanh::lean_unsigned_to_nat(3);
                v___x_2679_ = lean_nat_div(v___x_2677_, v___x_2678_);
                leanh::lean_dec(v___x_2677_);
                v___x_2680_ = lean_array_get_size(v_buckets_x27_2675_);
                v___x_2681_ = lean_nat_dec_le(v___x_2679_, v___x_2680_);
                leanh::lean_dec(v___x_2679_);
                if v___x_2681_ == 0 {
                    v_val_2682_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2642_,
                        v_buckets_x27_2675_,
                    );
                    if v_isShared_2671_ == 0 {
                        leanh::lean_ctor_set(v___x_2670_, 1, v_val_2682_);
                        leanh::lean_ctor_set(v___x_2670_, 0, v_size_x27_2673_);
                        v___x_2684_ = v___x_2670_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2687_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_size_x27_2673_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_val_2682_);
                        v___x_2684_ = v_reuseFailAlloc_2687_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2642_);
                    if v_isShared_2671_ == 0 {
                        leanh::lean_ctor_set(v___x_2670_, 1, v_buckets_x27_2675_);
                        leanh::lean_ctor_set(v___x_2670_, 0, v_size_x27_2673_);
                        v___x_2689_ = v___x_2670_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2692_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_size_x27_2673_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_buckets_x27_2675_);
                        v___x_2689_ = v_reuseFailAlloc_2692_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2685_ = leanh::lean_box((v___x_2668_) as usize);
                v___x_2686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2686_, 0, v___x_2685_);
                leanh::lean_ctor_set(v___x_2686_, 1, v___x_2684_);
                return v___x_2686_;
            }
            3 => {
                v___x_2690_ = leanh::lean_box((v___x_2668_) as usize);
                v___x_2691_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                leanh::lean_ctor_set(v___x_2691_, 1, v___x_2689_);
                return v___x_2691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(
    mut v_inst_2698_: *mut leanh::LeanObject,
    mut v_inst_2699_: *mut leanh::LeanObject,
    mut v_m_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_b_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u64 = 0;
    let mut v___x_2712_: u64 = 0;
    let mut v___x_2713_: u64 = 0;
    let mut v___x_2714_: u64 = 0;
    let mut v_fold_2715_: u64 = 0;
    let mut v___x_2716_: u64 = 0;
    let mut v___x_2717_: u64 = 0;
    let mut v___x_2718_: u64 = 0;
    let mut v___x_2719_: usize = 0;
    let mut v___x_2720_: usize = 0;
    let mut v___x_2721_: usize = 0;
    let mut v___x_2722_: usize = 0;
    let mut v___x_2723_: usize = 0;
    let mut v_bkt_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: u8 = 0;
    let mut v_val_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_unused_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2703_ = leanh::lean_ctor_get(v_m_2700_, 0);
                v_buckets_2704_ = leanh::lean_ctor_get(v_m_2700_, 1);
                v___x_2705_ = leanh::lean_unsigned_to_nat(0);
                v___x_2706_ = lean_array_get_size(v_buckets_2704_);
                v___x_2707_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
                if v___x_2707_ == 0 {
                    leanh::lean_dec(v_b_2702_);
                    leanh::lean_dec(v_a_2701_);
                    leanh::lean_dec_ref(v_inst_2699_);
                    leanh::lean_dec_ref(v_inst_2698_);
                    v___x_2708_ = leanh::lean_box(0);
                    v___x_2709_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2709_, 0, v___x_2708_);
                    leanh::lean_ctor_set(v___x_2709_, 1, v_m_2700_);
                    return v___x_2709_;
                } else {
                    leanh::lean_inc_ref(v_inst_2699_);
                    leanh::lean_inc_n(v_a_2701_, 2);
                    v___x_2710_ = leanh::lean_apply_1(v_inst_2699_, v_a_2701_);
                    v___x_2711_ = 32u64;
                    v___x_2712_ = leanh::lean_unbox_uint64(v___x_2710_);
                    v___x_2713_ = lean_uint64_shift_right(v___x_2712_, v___x_2711_);
                    v___x_2714_ = leanh::lean_unbox_uint64(v___x_2710_);
                    leanh::lean_dec_ref(v___x_2710_);
                    v_fold_2715_ = lean_uint64_xor(v___x_2714_, v___x_2713_);
                    v___x_2716_ = 16u64;
                    v___x_2717_ = lean_uint64_shift_right(v_fold_2715_, v___x_2716_);
                    v___x_2718_ = lean_uint64_xor(v_fold_2715_, v___x_2717_);
                    v___x_2719_ = lean_uint64_to_usize(v___x_2718_);
                    v___x_2720_ = lean_usize_of_nat(v___x_2706_);
                    v___x_2721_ = 1usize;
                    v___x_2722_ = lean_usize_sub(v___x_2720_, v___x_2721_);
                    v___x_2723_ = lean_usize_land(v___x_2719_, v___x_2722_);
                    v_bkt_2724_ = lean_array_uget_borrowed(v_buckets_2704_, v___x_2723_);
                    leanh::lean_inc(v_bkt_2724_);
                    v___x_2725_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_2698_,
                        v_a_2701_,
                        v_bkt_2724_,
                    );
                    if leanh::lean_obj_tag(v___x_2725_) == 0 {
                        leanh::lean_inc_ref(v_buckets_2704_);
                        leanh::lean_inc(v_size_2703_);
                        v_isSharedCheck_2748_ = (!leanh::lean_is_exclusive(v_m_2700_)) as u8;
                        if v_isSharedCheck_2748_ == 0 {
                            v_unused_2749_ = leanh::lean_ctor_get(v_m_2700_, 1);
                            leanh::lean_dec(v_unused_2749_);
                            v_unused_2750_ = leanh::lean_ctor_get(v_m_2700_, 0);
                            leanh::lean_dec(v_unused_2750_);
                            v___x_2727_ = v_m_2700_;
                            v_isShared_2728_ = v_isSharedCheck_2748_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_2700_);
                            v___x_2727_ = leanh::lean_box(0);
                            v_isShared_2728_ = v_isSharedCheck_2748_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_2702_);
                        leanh::lean_dec(v_a_2701_);
                        leanh::lean_dec_ref(v_inst_2699_);
                        v___x_2751_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2751_, 0, v___x_2725_);
                        leanh::lean_ctor_set(v___x_2751_, 1, v_m_2700_);
                        return v___x_2751_;
                    }
                }
            }
            1 => {
                v___x_2729_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2730_ = lean_nat_add(v_size_2703_, v___x_2729_);
                leanh::lean_dec(v_size_2703_);
                leanh::lean_inc(v_bkt_2724_);
                v___x_2731_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2731_, 0, v_a_2701_);
                leanh::lean_ctor_set(v___x_2731_, 1, v_b_2702_);
                leanh::lean_ctor_set(v___x_2731_, 2, v_bkt_2724_);
                v_buckets_x27_2732_ = lean_array_uset(v_buckets_2704_, v___x_2723_, v___x_2731_);
                v___x_2733_ = leanh::lean_unsigned_to_nat(4);
                v___x_2734_ = lean_nat_mul(v_size_x27_2730_, v___x_2733_);
                v___x_2735_ = leanh::lean_unsigned_to_nat(3);
                v___x_2736_ = lean_nat_div(v___x_2734_, v___x_2735_);
                leanh::lean_dec(v___x_2734_);
                v___x_2737_ = lean_array_get_size(v_buckets_x27_2732_);
                v___x_2738_ = lean_nat_dec_le(v___x_2736_, v___x_2737_);
                leanh::lean_dec(v___x_2736_);
                if v___x_2738_ == 0 {
                    v_val_2739_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2699_,
                        v_buckets_x27_2732_,
                    );
                    if v_isShared_2728_ == 0 {
                        leanh::lean_ctor_set(v___x_2727_, 1, v_val_2739_);
                        leanh::lean_ctor_set(v___x_2727_, 0, v_size_x27_2730_);
                        v___x_2741_ = v___x_2727_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2743_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_size_x27_2730_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_val_2739_);
                        v___x_2741_ = v_reuseFailAlloc_2743_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2699_);
                    if v_isShared_2728_ == 0 {
                        leanh::lean_ctor_set(v___x_2727_, 1, v_buckets_x27_2732_);
                        leanh::lean_ctor_set(v___x_2727_, 0, v_size_x27_2730_);
                        v___x_2745_ = v___x_2727_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2747_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_size_x27_2730_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_buckets_x27_2732_);
                        v___x_2745_ = v_reuseFailAlloc_2747_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2742_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2742_, 0, v___x_2725_);
                leanh::lean_ctor_set(v___x_2742_, 1, v___x_2741_);
                return v___x_2742_;
            }
            3 => {
                v___x_2746_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2746_, 0, v___x_2725_);
                leanh::lean_ctor_set(v___x_2746_, 1, v___x_2745_);
                return v___x_2746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2752_: *mut leanh::LeanObject,
    mut v_00_u03b2_2753_: *mut leanh::LeanObject,
    mut v_inst_2754_: *mut leanh::LeanObject,
    mut v_inst_2755_: *mut leanh::LeanObject,
    mut v_m_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
    mut v_b_2758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u64 = 0;
    let mut v___x_2768_: u64 = 0;
    let mut v___x_2769_: u64 = 0;
    let mut v___x_2770_: u64 = 0;
    let mut v_fold_2771_: u64 = 0;
    let mut v___x_2772_: u64 = 0;
    let mut v___x_2773_: u64 = 0;
    let mut v___x_2774_: u64 = 0;
    let mut v___x_2775_: usize = 0;
    let mut v___x_2776_: usize = 0;
    let mut v___x_2777_: usize = 0;
    let mut v___x_2778_: usize = 0;
    let mut v___x_2779_: usize = 0;
    let mut v_bkt_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v_val_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_unused_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2759_ = leanh::lean_ctor_get(v_m_2756_, 0);
                v_buckets_2760_ = leanh::lean_ctor_get(v_m_2756_, 1);
                v___x_2761_ = leanh::lean_unsigned_to_nat(0);
                v___x_2762_ = lean_array_get_size(v_buckets_2760_);
                v___x_2763_ = lean_nat_dec_lt(v___x_2761_, v___x_2762_);
                if v___x_2763_ == 0 {
                    leanh::lean_dec(v_b_2758_);
                    leanh::lean_dec(v_a_2757_);
                    leanh::lean_dec_ref(v_inst_2755_);
                    leanh::lean_dec_ref(v_inst_2754_);
                    v___x_2764_ = leanh::lean_box(0);
                    v___x_2765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2765_, 0, v___x_2764_);
                    leanh::lean_ctor_set(v___x_2765_, 1, v_m_2756_);
                    return v___x_2765_;
                } else {
                    leanh::lean_inc_ref(v_inst_2755_);
                    leanh::lean_inc_n(v_a_2757_, 2);
                    v___x_2766_ = leanh::lean_apply_1(v_inst_2755_, v_a_2757_);
                    v___x_2767_ = 32u64;
                    v___x_2768_ = leanh::lean_unbox_uint64(v___x_2766_);
                    v___x_2769_ = lean_uint64_shift_right(v___x_2768_, v___x_2767_);
                    v___x_2770_ = leanh::lean_unbox_uint64(v___x_2766_);
                    leanh::lean_dec_ref(v___x_2766_);
                    v_fold_2771_ = lean_uint64_xor(v___x_2770_, v___x_2769_);
                    v___x_2772_ = 16u64;
                    v___x_2773_ = lean_uint64_shift_right(v_fold_2771_, v___x_2772_);
                    v___x_2774_ = lean_uint64_xor(v_fold_2771_, v___x_2773_);
                    v___x_2775_ = lean_uint64_to_usize(v___x_2774_);
                    v___x_2776_ = lean_usize_of_nat(v___x_2762_);
                    v___x_2777_ = 1usize;
                    v___x_2778_ = lean_usize_sub(v___x_2776_, v___x_2777_);
                    v___x_2779_ = lean_usize_land(v___x_2775_, v___x_2778_);
                    v_bkt_2780_ = lean_array_uget_borrowed(v_buckets_2760_, v___x_2779_);
                    leanh::lean_inc(v_bkt_2780_);
                    v___x_2781_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_2754_,
                        v_a_2757_,
                        v_bkt_2780_,
                    );
                    if leanh::lean_obj_tag(v___x_2781_) == 0 {
                        leanh::lean_inc_ref(v_buckets_2760_);
                        leanh::lean_inc(v_size_2759_);
                        v_isSharedCheck_2804_ = (!leanh::lean_is_exclusive(v_m_2756_)) as u8;
                        if v_isSharedCheck_2804_ == 0 {
                            v_unused_2805_ = leanh::lean_ctor_get(v_m_2756_, 1);
                            leanh::lean_dec(v_unused_2805_);
                            v_unused_2806_ = leanh::lean_ctor_get(v_m_2756_, 0);
                            leanh::lean_dec(v_unused_2806_);
                            v___x_2783_ = v_m_2756_;
                            v_isShared_2784_ = v_isSharedCheck_2804_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_2756_);
                            v___x_2783_ = leanh::lean_box(0);
                            v_isShared_2784_ = v_isSharedCheck_2804_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_2758_);
                        leanh::lean_dec(v_a_2757_);
                        leanh::lean_dec_ref(v_inst_2755_);
                        v___x_2807_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2807_, 0, v___x_2781_);
                        leanh::lean_ctor_set(v___x_2807_, 1, v_m_2756_);
                        return v___x_2807_;
                    }
                }
            }
            1 => {
                v___x_2785_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2786_ = lean_nat_add(v_size_2759_, v___x_2785_);
                leanh::lean_dec(v_size_2759_);
                leanh::lean_inc(v_bkt_2780_);
                v___x_2787_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2787_, 0, v_a_2757_);
                leanh::lean_ctor_set(v___x_2787_, 1, v_b_2758_);
                leanh::lean_ctor_set(v___x_2787_, 2, v_bkt_2780_);
                v_buckets_x27_2788_ = lean_array_uset(v_buckets_2760_, v___x_2779_, v___x_2787_);
                v___x_2789_ = leanh::lean_unsigned_to_nat(4);
                v___x_2790_ = lean_nat_mul(v_size_x27_2786_, v___x_2789_);
                v___x_2791_ = leanh::lean_unsigned_to_nat(3);
                v___x_2792_ = lean_nat_div(v___x_2790_, v___x_2791_);
                leanh::lean_dec(v___x_2790_);
                v___x_2793_ = lean_array_get_size(v_buckets_x27_2788_);
                v___x_2794_ = lean_nat_dec_le(v___x_2792_, v___x_2793_);
                leanh::lean_dec(v___x_2792_);
                if v___x_2794_ == 0 {
                    v_val_2795_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2755_,
                        v_buckets_x27_2788_,
                    );
                    if v_isShared_2784_ == 0 {
                        leanh::lean_ctor_set(v___x_2783_, 1, v_val_2795_);
                        leanh::lean_ctor_set(v___x_2783_, 0, v_size_x27_2786_);
                        v___x_2797_ = v___x_2783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_size_x27_2786_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_val_2795_);
                        v___x_2797_ = v_reuseFailAlloc_2799_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2755_);
                    if v_isShared_2784_ == 0 {
                        leanh::lean_ctor_set(v___x_2783_, 1, v_buckets_x27_2788_);
                        leanh::lean_ctor_set(v___x_2783_, 0, v_size_x27_2786_);
                        v___x_2801_ = v___x_2783_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2803_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_size_x27_2786_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_buckets_x27_2788_);
                        v___x_2801_ = v_reuseFailAlloc_2803_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2798_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2798_, 0, v___x_2781_);
                leanh::lean_ctor_set(v___x_2798_, 1, v___x_2797_);
                return v___x_2798_;
            }
            3 => {
                v___x_2802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2802_, 0, v___x_2781_);
                leanh::lean_ctor_set(v___x_2802_, 1, v___x_2801_);
                return v___x_2802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_get_x3f___redArg(
    mut v_beq_2808_: *mut leanh::LeanObject,
    mut v_inst_2809_: *mut leanh::LeanObject,
    mut v_m_2810_: *mut leanh::LeanObject,
    mut v_a_2811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    v_buckets_2812_ = leanh::lean_ctor_get(v_m_2810_, 1);
    v___x_2813_ = leanh::lean_unsigned_to_nat(0);
    v___x_2814_ = lean_array_get_size(v_buckets_2812_);
    v___x_2815_ = lean_nat_dec_lt(v___x_2813_, v___x_2814_);
    if v___x_2815_ == 0 {
        let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_2811_);
        leanh::lean_dec_ref(v_inst_2809_);
        leanh::lean_dec_ref(v_beq_2808_);
        v___x_2816_ = leanh::lean_box(0);
        return v___x_2816_;
    } else {
        let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_beq_2808_,
            v_inst_2809_,
            v_m_2810_,
            v_a_2811_,
        );
        return v___x_2817_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_get_x3f___redArg___boxed(
    mut v_beq_2818_: *mut leanh::LeanObject,
    mut v_inst_2819_: *mut leanh::LeanObject,
    mut v_m_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2822_ =
        l_Std_HashMap_Raw_get_x3f___redArg(v_beq_2818_, v_inst_2819_, v_m_2820_, v_a_2821_);
    leanh::lean_dec_ref(v_m_2820_);
    return v_res_2822_;
}
pub unsafe fn l_Std_HashMap_Raw_get_x3f(
    mut v_00_u03b1_2823_: *mut leanh::LeanObject,
    mut v_00_u03b2_2824_: *mut leanh::LeanObject,
    mut v_beq_2825_: *mut leanh::LeanObject,
    mut v_inst_2826_: *mut leanh::LeanObject,
    mut v_m_2827_: *mut leanh::LeanObject,
    mut v_a_2828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    v_buckets_2829_ = leanh::lean_ctor_get(v_m_2827_, 1);
    v___x_2830_ = leanh::lean_unsigned_to_nat(0);
    v___x_2831_ = lean_array_get_size(v_buckets_2829_);
    v___x_2832_ = lean_nat_dec_lt(v___x_2830_, v___x_2831_);
    if v___x_2832_ == 0 {
        let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_2828_);
        leanh::lean_dec_ref(v_inst_2826_);
        leanh::lean_dec_ref(v_beq_2825_);
        v___x_2833_ = leanh::lean_box(0);
        return v___x_2833_;
    } else {
        let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_beq_2825_,
            v_inst_2826_,
            v_m_2827_,
            v_a_2828_,
        );
        return v___x_2834_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_get_x3f___boxed(
    mut v_00_u03b1_2835_: *mut leanh::LeanObject,
    mut v_00_u03b2_2836_: *mut leanh::LeanObject,
    mut v_beq_2837_: *mut leanh::LeanObject,
    mut v_inst_2838_: *mut leanh::LeanObject,
    mut v_m_2839_: *mut leanh::LeanObject,
    mut v_a_2840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2841_ = l_Std_HashMap_Raw_get_x3f(
        v_00_u03b1_2835_,
        v_00_u03b2_2836_,
        v_beq_2837_,
        v_inst_2838_,
        v_m_2839_,
        v_a_2840_,
    );
    leanh::lean_dec_ref(v_m_2839_);
    return v_res_2841_;
}
pub unsafe fn l_Std_HashMap_Raw_contains___redArg(
    mut v_inst_2842_: *mut leanh::LeanObject,
    mut v_inst_2843_: *mut leanh::LeanObject,
    mut v_m_2844_: *mut leanh::LeanObject,
    mut v_a_2845_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    v_buckets_2846_ = leanh::lean_ctor_get(v_m_2844_, 1);
    v___x_2847_ = leanh::lean_unsigned_to_nat(0);
    v___x_2848_ = lean_array_get_size(v_buckets_2846_);
    v___x_2849_ = lean_nat_dec_lt(v___x_2847_, v___x_2848_);
    if v___x_2849_ == 0 {
        leanh::lean_dec(v_a_2845_);
        leanh::lean_dec_ref(v_inst_2843_);
        leanh::lean_dec_ref(v_inst_2842_);
        return v___x_2849_;
    } else {
        let mut v___x_2850_: u8 = 0;
        v___x_2850_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_2842_,
            v_inst_2843_,
            v_m_2844_,
            v_a_2845_,
        );
        return v___x_2850_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_contains___redArg___boxed(
    mut v_inst_2851_: *mut leanh::LeanObject,
    mut v_inst_2852_: *mut leanh::LeanObject,
    mut v_m_2853_: *mut leanh::LeanObject,
    mut v_a_2854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2855_: u8 = 0;
    let mut v_r_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2855_ =
        l_Std_HashMap_Raw_contains___redArg(v_inst_2851_, v_inst_2852_, v_m_2853_, v_a_2854_);
    leanh::lean_dec_ref(v_m_2853_);
    v_r_2856_ = leanh::lean_box((v_res_2855_) as usize);
    return v_r_2856_;
}
pub unsafe fn l_Std_HashMap_Raw_contains(
    mut v_00_u03b1_2857_: *mut leanh::LeanObject,
    mut v_00_u03b2_2858_: *mut leanh::LeanObject,
    mut v_inst_2859_: *mut leanh::LeanObject,
    mut v_inst_2860_: *mut leanh::LeanObject,
    mut v_m_2861_: *mut leanh::LeanObject,
    mut v_a_2862_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    v_buckets_2863_ = leanh::lean_ctor_get(v_m_2861_, 1);
    v___x_2864_ = leanh::lean_unsigned_to_nat(0);
    v___x_2865_ = lean_array_get_size(v_buckets_2863_);
    v___x_2866_ = lean_nat_dec_lt(v___x_2864_, v___x_2865_);
    if v___x_2866_ == 0 {
        leanh::lean_dec(v_a_2862_);
        leanh::lean_dec_ref(v_inst_2860_);
        leanh::lean_dec_ref(v_inst_2859_);
        return v___x_2866_;
    } else {
        let mut v___x_2867_: u8 = 0;
        v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_2859_,
            v_inst_2860_,
            v_m_2861_,
            v_a_2862_,
        );
        return v___x_2867_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_contains___boxed(
    mut v_00_u03b1_2868_: *mut leanh::LeanObject,
    mut v_00_u03b2_2869_: *mut leanh::LeanObject,
    mut v_inst_2870_: *mut leanh::LeanObject,
    mut v_inst_2871_: *mut leanh::LeanObject,
    mut v_m_2872_: *mut leanh::LeanObject,
    mut v_a_2873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2874_: u8 = 0;
    let mut v_r_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2874_ = l_Std_HashMap_Raw_contains(
        v_00_u03b1_2868_,
        v_00_u03b2_2869_,
        v_inst_2870_,
        v_inst_2871_,
        v_m_2872_,
        v_a_2873_,
    );
    leanh::lean_dec_ref(v_m_2872_);
    v_r_2875_ = leanh::lean_box((v_res_2874_) as usize);
    return v_r_2875_;
}
pub unsafe fn l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(
    mut v_00_u03b1_2876_: *mut leanh::LeanObject,
    mut v_00_u03b2_2877_: *mut leanh::LeanObject,
    mut v_inst_2878_: *mut leanh::LeanObject,
    mut v_inst_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = leanh::lean_box(0);
    return v___x_2880_;
}
pub unsafe fn l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(
    mut v_00_u03b1_2881_: *mut leanh::LeanObject,
    mut v_00_u03b2_2882_: *mut leanh::LeanObject,
    mut v_inst_2883_: *mut leanh::LeanObject,
    mut v_inst_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2885_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(
        v_00_u03b1_2881_,
        v_00_u03b2_2882_,
        v_inst_2883_,
        v_inst_2884_,
    );
    leanh::lean_dec_ref(v_inst_2884_);
    leanh::lean_dec_ref(v_inst_2883_);
    return v_res_2885_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableMem___redArg(
    mut v_inst_2886_: *mut leanh::LeanObject,
    mut v_inst_2887_: *mut leanh::LeanObject,
    mut v_m_2888_: *mut leanh::LeanObject,
    mut v_a_2889_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2890_: u8 = 0;
    v___x_2890_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(
        v_inst_2886_,
        v_inst_2887_,
        v_m_2888_,
        v_a_2889_,
    );
    return v___x_2890_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(
    mut v_inst_2891_: *mut leanh::LeanObject,
    mut v_inst_2892_: *mut leanh::LeanObject,
    mut v_m_2893_: *mut leanh::LeanObject,
    mut v_a_2894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2895_: u8 = 0;
    let mut v_r_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Std_HashMap_Raw_instDecidableMem___redArg(
        v_inst_2891_,
        v_inst_2892_,
        v_m_2893_,
        v_a_2894_,
    );
    leanh::lean_dec_ref(v_m_2893_);
    v_r_2896_ = leanh::lean_box((v_res_2895_) as usize);
    return v_r_2896_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableMem(
    mut v_00_u03b1_2897_: *mut leanh::LeanObject,
    mut v_00_u03b2_2898_: *mut leanh::LeanObject,
    mut v_inst_2899_: *mut leanh::LeanObject,
    mut v_inst_2900_: *mut leanh::LeanObject,
    mut v_m_2901_: *mut leanh::LeanObject,
    mut v_a_2902_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2903_: u8 = 0;
    v___x_2903_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(
        v_inst_2899_,
        v_inst_2900_,
        v_m_2901_,
        v_a_2902_,
    );
    return v___x_2903_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableMem___boxed(
    mut v_00_u03b1_2904_: *mut leanh::LeanObject,
    mut v_00_u03b2_2905_: *mut leanh::LeanObject,
    mut v_inst_2906_: *mut leanh::LeanObject,
    mut v_inst_2907_: *mut leanh::LeanObject,
    mut v_m_2908_: *mut leanh::LeanObject,
    mut v_a_2909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2910_: u8 = 0;
    let mut v_r_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2910_ = l_Std_HashMap_Raw_instDecidableMem(
        v_00_u03b1_2904_,
        v_00_u03b2_2905_,
        v_inst_2906_,
        v_inst_2907_,
        v_m_2908_,
        v_a_2909_,
    );
    leanh::lean_dec_ref(v_m_2908_);
    v_r_2911_ = leanh::lean_box((v_res_2910_) as usize);
    return v_r_2911_;
}
pub unsafe fn l_Std_HashMap_Raw_get___redArg(
    mut v_inst_2912_: *mut leanh::LeanObject,
    mut v_inst_2913_: *mut leanh::LeanObject,
    mut v_m_2914_: *mut leanh::LeanObject,
    mut v_a_2915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_2912_,
        v_inst_2913_,
        v_m_2914_,
        v_a_2915_,
    );
    return v___x_2916_;
}
pub unsafe fn l_Std_HashMap_Raw_get___redArg___boxed(
    mut v_inst_2917_: *mut leanh::LeanObject,
    mut v_inst_2918_: *mut leanh::LeanObject,
    mut v_m_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Std_HashMap_Raw_get___redArg(v_inst_2917_, v_inst_2918_, v_m_2919_, v_a_2920_);
    leanh::lean_dec_ref(v_m_2919_);
    return v_res_2921_;
}
pub unsafe fn l_Std_HashMap_Raw_get(
    mut v_00_u03b1_2922_: *mut leanh::LeanObject,
    mut v_00_u03b2_2923_: *mut leanh::LeanObject,
    mut v_inst_2924_: *mut leanh::LeanObject,
    mut v_inst_2925_: *mut leanh::LeanObject,
    mut v_m_2926_: *mut leanh::LeanObject,
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_h_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_2924_,
        v_inst_2925_,
        v_m_2926_,
        v_a_2927_,
    );
    return v___x_2929_;
}
pub unsafe fn l_Std_HashMap_Raw_get___boxed(
    mut v_00_u03b1_2930_: *mut leanh::LeanObject,
    mut v_00_u03b2_2931_: *mut leanh::LeanObject,
    mut v_inst_2932_: *mut leanh::LeanObject,
    mut v_inst_2933_: *mut leanh::LeanObject,
    mut v_m_2934_: *mut leanh::LeanObject,
    mut v_a_2935_: *mut leanh::LeanObject,
    mut v_h_2936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2937_ = l_Std_HashMap_Raw_get(
        v_00_u03b1_2930_,
        v_00_u03b2_2931_,
        v_inst_2932_,
        v_inst_2933_,
        v_m_2934_,
        v_a_2935_,
        v_h_2936_,
    );
    leanh::lean_dec_ref(v_m_2934_);
    return v_res_2937_;
}
pub unsafe fn l_Std_HashMap_Raw_getD___redArg(
    mut v_inst_2938_: *mut leanh::LeanObject,
    mut v_inst_2939_: *mut leanh::LeanObject,
    mut v_m_2940_: *mut leanh::LeanObject,
    mut v_a_2941_: *mut leanh::LeanObject,
    mut v_fallback_2942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    v_buckets_2943_ = leanh::lean_ctor_get(v_m_2940_, 1);
    v___x_2944_ = leanh::lean_unsigned_to_nat(0);
    v___x_2945_ = lean_array_get_size(v_buckets_2943_);
    v___x_2946_ = lean_nat_dec_lt(v___x_2944_, v___x_2945_);
    if v___x_2946_ == 0 {
        leanh::lean_dec(v_a_2941_);
        leanh::lean_dec_ref(v_inst_2939_);
        leanh::lean_dec_ref(v_inst_2938_);
        leanh::lean_inc(v_fallback_2942_);
        return v_fallback_2942_;
    } else {
        let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
            v_inst_2938_,
            v_inst_2939_,
            v_m_2940_,
            v_a_2941_,
            v_fallback_2942_,
        );
        return v___x_2947_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getD___redArg___boxed(
    mut v_inst_2948_: *mut leanh::LeanObject,
    mut v_inst_2949_: *mut leanh::LeanObject,
    mut v_m_2950_: *mut leanh::LeanObject,
    mut v_a_2951_: *mut leanh::LeanObject,
    mut v_fallback_2952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Std_HashMap_Raw_getD___redArg(
        v_inst_2948_,
        v_inst_2949_,
        v_m_2950_,
        v_a_2951_,
        v_fallback_2952_,
    );
    leanh::lean_dec(v_fallback_2952_);
    leanh::lean_dec_ref(v_m_2950_);
    return v_res_2953_;
}
pub unsafe fn l_Std_HashMap_Raw_getD(
    mut v_00_u03b1_2954_: *mut leanh::LeanObject,
    mut v_00_u03b2_2955_: *mut leanh::LeanObject,
    mut v_inst_2956_: *mut leanh::LeanObject,
    mut v_inst_2957_: *mut leanh::LeanObject,
    mut v_m_2958_: *mut leanh::LeanObject,
    mut v_a_2959_: *mut leanh::LeanObject,
    mut v_fallback_2960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    v_buckets_2961_ = leanh::lean_ctor_get(v_m_2958_, 1);
    v___x_2962_ = leanh::lean_unsigned_to_nat(0);
    v___x_2963_ = lean_array_get_size(v_buckets_2961_);
    v___x_2964_ = lean_nat_dec_lt(v___x_2962_, v___x_2963_);
    if v___x_2964_ == 0 {
        leanh::lean_dec(v_a_2959_);
        leanh::lean_dec_ref(v_inst_2957_);
        leanh::lean_dec_ref(v_inst_2956_);
        leanh::lean_inc(v_fallback_2960_);
        return v_fallback_2960_;
    } else {
        let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
            v_inst_2956_,
            v_inst_2957_,
            v_m_2958_,
            v_a_2959_,
            v_fallback_2960_,
        );
        return v___x_2965_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getD___boxed(
    mut v_00_u03b1_2966_: *mut leanh::LeanObject,
    mut v_00_u03b2_2967_: *mut leanh::LeanObject,
    mut v_inst_2968_: *mut leanh::LeanObject,
    mut v_inst_2969_: *mut leanh::LeanObject,
    mut v_m_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v_fallback_2972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2973_ = l_Std_HashMap_Raw_getD(
        v_00_u03b1_2966_,
        v_00_u03b2_2967_,
        v_inst_2968_,
        v_inst_2969_,
        v_m_2970_,
        v_a_2971_,
        v_fallback_2972_,
    );
    leanh::lean_dec(v_fallback_2972_);
    leanh::lean_dec_ref(v_m_2970_);
    return v_res_2973_;
}
pub unsafe fn l_Std_HashMap_Raw_get_x21___redArg(
    mut v_inst_2974_: *mut leanh::LeanObject,
    mut v_inst_2975_: *mut leanh::LeanObject,
    mut v_inst_2976_: *mut leanh::LeanObject,
    mut v_m_2977_: *mut leanh::LeanObject,
    mut v_a_2978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    v_buckets_2979_ = leanh::lean_ctor_get(v_m_2977_, 1);
    v___x_2980_ = leanh::lean_unsigned_to_nat(0);
    v___x_2981_ = lean_array_get_size(v_buckets_2979_);
    v___x_2982_ = lean_nat_dec_lt(v___x_2980_, v___x_2981_);
    if v___x_2982_ == 0 {
        leanh::lean_dec(v_a_2978_);
        leanh::lean_dec_ref(v_inst_2975_);
        leanh::lean_dec_ref(v_inst_2974_);
        leanh::lean_inc(v_inst_2976_);
        return v_inst_2976_;
    } else {
        let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
            v_inst_2974_,
            v_inst_2975_,
            v_inst_2976_,
            v_m_2977_,
            v_a_2978_,
        );
        return v___x_2983_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_get_x21___redArg___boxed(
    mut v_inst_2984_: *mut leanh::LeanObject,
    mut v_inst_2985_: *mut leanh::LeanObject,
    mut v_inst_2986_: *mut leanh::LeanObject,
    mut v_m_2987_: *mut leanh::LeanObject,
    mut v_a_2988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2989_ = l_Std_HashMap_Raw_get_x21___redArg(
        v_inst_2984_,
        v_inst_2985_,
        v_inst_2986_,
        v_m_2987_,
        v_a_2988_,
    );
    leanh::lean_dec_ref(v_m_2987_);
    leanh::lean_dec(v_inst_2986_);
    return v_res_2989_;
}
pub unsafe fn l_Std_HashMap_Raw_get_x21(
    mut v_00_u03b1_2990_: *mut leanh::LeanObject,
    mut v_00_u03b2_2991_: *mut leanh::LeanObject,
    mut v_inst_2992_: *mut leanh::LeanObject,
    mut v_inst_2993_: *mut leanh::LeanObject,
    mut v_inst_2994_: *mut leanh::LeanObject,
    mut v_m_2995_: *mut leanh::LeanObject,
    mut v_a_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    v_buckets_2997_ = leanh::lean_ctor_get(v_m_2995_, 1);
    v___x_2998_ = leanh::lean_unsigned_to_nat(0);
    v___x_2999_ = lean_array_get_size(v_buckets_2997_);
    v___x_3000_ = lean_nat_dec_lt(v___x_2998_, v___x_2999_);
    if v___x_3000_ == 0 {
        leanh::lean_dec(v_a_2996_);
        leanh::lean_dec_ref(v_inst_2993_);
        leanh::lean_dec_ref(v_inst_2992_);
        leanh::lean_inc(v_inst_2994_);
        return v_inst_2994_;
    } else {
        let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3001_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
            v_inst_2992_,
            v_inst_2993_,
            v_inst_2994_,
            v_m_2995_,
            v_a_2996_,
        );
        return v___x_3001_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_get_x21___boxed(
    mut v_00_u03b1_3002_: *mut leanh::LeanObject,
    mut v_00_u03b2_3003_: *mut leanh::LeanObject,
    mut v_inst_3004_: *mut leanh::LeanObject,
    mut v_inst_3005_: *mut leanh::LeanObject,
    mut v_inst_3006_: *mut leanh::LeanObject,
    mut v_m_3007_: *mut leanh::LeanObject,
    mut v_a_3008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3009_ = l_Std_HashMap_Raw_get_x21(
        v_00_u03b1_3002_,
        v_00_u03b2_3003_,
        v_inst_3004_,
        v_inst_3005_,
        v_inst_3006_,
        v_m_3007_,
        v_a_3008_,
    );
    leanh::lean_dec_ref(v_m_3007_);
    leanh::lean_dec(v_inst_3006_);
    return v_res_3009_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(
    mut v_inst_3010_: *mut leanh::LeanObject,
    mut v_inst_3011_: *mut leanh::LeanObject,
    mut v_m_3012_: *mut leanh::LeanObject,
    mut v_a_3013_: *mut leanh::LeanObject,
    mut v_h_3014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_3010_,
        v_inst_3011_,
        v_m_3012_,
        v_a_3013_,
    );
    return v___x_3015_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(
    mut v_inst_3016_: *mut leanh::LeanObject,
    mut v_inst_3017_: *mut leanh::LeanObject,
    mut v_m_3018_: *mut leanh::LeanObject,
    mut v_a_3019_: *mut leanh::LeanObject,
    mut v_h_3020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(
        v_inst_3016_,
        v_inst_3017_,
        v_m_3018_,
        v_a_3019_,
        v_h_3020_,
    );
    leanh::lean_dec_ref(v_m_3018_);
    return v_res_3021_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(
    mut v_inst_3022_: *mut leanh::LeanObject,
    mut v_inst_3023_: *mut leanh::LeanObject,
    mut v_m_3024_: *mut leanh::LeanObject,
    mut v_a_3025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: u8 = 0;
    v_buckets_3026_ = leanh::lean_ctor_get(v_m_3024_, 1);
    v___x_3027_ = leanh::lean_unsigned_to_nat(0);
    v___x_3028_ = lean_array_get_size(v_buckets_3026_);
    v___x_3029_ = lean_nat_dec_lt(v___x_3027_, v___x_3028_);
    if v___x_3029_ == 0 {
        let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3025_);
        leanh::lean_dec_ref(v_inst_3023_);
        leanh::lean_dec_ref(v_inst_3022_);
        v___x_3030_ = leanh::lean_box(0);
        return v___x_3030_;
    } else {
        let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_inst_3022_,
            v_inst_3023_,
            v_m_3024_,
            v_a_3025_,
        );
        return v___x_3031_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(
    mut v_inst_3032_: *mut leanh::LeanObject,
    mut v_inst_3033_: *mut leanh::LeanObject,
    mut v_m_3034_: *mut leanh::LeanObject,
    mut v_a_3035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3036_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(
        v_inst_3032_,
        v_inst_3033_,
        v_m_3034_,
        v_a_3035_,
    );
    leanh::lean_dec_ref(v_m_3034_);
    return v_res_3036_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(
    mut v_inst_3037_: *mut leanh::LeanObject,
    mut v_inst_3038_: *mut leanh::LeanObject,
    mut v_inst_3039_: *mut leanh::LeanObject,
    mut v_m_3040_: *mut leanh::LeanObject,
    mut v_a_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    v_buckets_3042_ = leanh::lean_ctor_get(v_m_3040_, 1);
    v___x_3043_ = leanh::lean_unsigned_to_nat(0);
    v___x_3044_ = lean_array_get_size(v_buckets_3042_);
    v___x_3045_ = lean_nat_dec_lt(v___x_3043_, v___x_3044_);
    if v___x_3045_ == 0 {
        leanh::lean_dec(v_a_3041_);
        leanh::lean_dec_ref(v_inst_3038_);
        leanh::lean_dec_ref(v_inst_3037_);
        leanh::lean_inc(v_inst_3039_);
        return v_inst_3039_;
    } else {
        let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
            v_inst_3037_,
            v_inst_3038_,
            v_inst_3039_,
            v_m_3040_,
            v_a_3041_,
        );
        return v___x_3046_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(
    mut v_inst_3047_: *mut leanh::LeanObject,
    mut v_inst_3048_: *mut leanh::LeanObject,
    mut v_inst_3049_: *mut leanh::LeanObject,
    mut v_m_3050_: *mut leanh::LeanObject,
    mut v_a_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3052_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(
        v_inst_3047_,
        v_inst_3048_,
        v_inst_3049_,
        v_m_3050_,
        v_a_3051_,
    );
    leanh::lean_dec_ref(v_m_3050_);
    leanh::lean_dec(v_inst_3049_);
    return v_res_3052_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(
    mut v_inst_3053_: *mut leanh::LeanObject,
    mut v_inst_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_3054_, 2);
    leanh::lean_inc_ref_n(v_inst_3053_, 2);
    v___f_3055_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3055_, 0, v_inst_3053_);
    leanh::lean_closure_set(v___f_3055_, 1, v_inst_3054_);
    v___f_3056_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_3056_, 0, v_inst_3053_);
    leanh::lean_closure_set(v___f_3056_, 1, v_inst_3054_);
    v___f_3057_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3057_, 0, v_inst_3053_);
    leanh::lean_closure_set(v___f_3057_, 1, v_inst_3054_);
    v___x_3058_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3058_, 0, v___f_3055_);
    leanh::lean_ctor_set(v___x_3058_, 1, v___f_3056_);
    leanh::lean_ctor_set(v___x_3058_, 2, v___f_3057_);
    return v___x_3058_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem(
    mut v_00_u03b1_3059_: *mut leanh::LeanObject,
    mut v_00_u03b2_3060_: *mut leanh::LeanObject,
    mut v_inst_3061_: *mut leanh::LeanObject,
    mut v_inst_3062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3063_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_3061_, v_inst_3062_);
    return v___x_3063_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x3f___redArg(
    mut v_inst_3064_: *mut leanh::LeanObject,
    mut v_inst_3065_: *mut leanh::LeanObject,
    mut v_m_3066_: *mut leanh::LeanObject,
    mut v_a_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    v_buckets_3068_ = leanh::lean_ctor_get(v_m_3066_, 1);
    v___x_3069_ = leanh::lean_unsigned_to_nat(0);
    v___x_3070_ = lean_array_get_size(v_buckets_3068_);
    v___x_3071_ = lean_nat_dec_lt(v___x_3069_, v___x_3070_);
    if v___x_3071_ == 0 {
        let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3067_);
        leanh::lean_dec_ref(v_inst_3065_);
        leanh::lean_dec_ref(v_inst_3064_);
        v___x_3072_ = leanh::lean_box(0);
        return v___x_3072_;
    } else {
        let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3073_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
            v_inst_3064_,
            v_inst_3065_,
            v_m_3066_,
            v_a_3067_,
        );
        return v___x_3073_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(
    mut v_inst_3074_: *mut leanh::LeanObject,
    mut v_inst_3075_: *mut leanh::LeanObject,
    mut v_m_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3078_ =
        l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_3074_, v_inst_3075_, v_m_3076_, v_a_3077_);
    leanh::lean_dec_ref(v_m_3076_);
    return v_res_3078_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x3f(
    mut v_00_u03b1_3079_: *mut leanh::LeanObject,
    mut v_00_u03b2_3080_: *mut leanh::LeanObject,
    mut v_inst_3081_: *mut leanh::LeanObject,
    mut v_inst_3082_: *mut leanh::LeanObject,
    mut v_m_3083_: *mut leanh::LeanObject,
    mut v_a_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: u8 = 0;
    v_buckets_3085_ = leanh::lean_ctor_get(v_m_3083_, 1);
    v___x_3086_ = leanh::lean_unsigned_to_nat(0);
    v___x_3087_ = lean_array_get_size(v_buckets_3085_);
    v___x_3088_ = lean_nat_dec_lt(v___x_3086_, v___x_3087_);
    if v___x_3088_ == 0 {
        let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3084_);
        leanh::lean_dec_ref(v_inst_3082_);
        leanh::lean_dec_ref(v_inst_3081_);
        v___x_3089_ = leanh::lean_box(0);
        return v___x_3089_;
    } else {
        let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3090_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
            v_inst_3081_,
            v_inst_3082_,
            v_m_3083_,
            v_a_3084_,
        );
        return v___x_3090_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x3f___boxed(
    mut v_00_u03b1_3091_: *mut leanh::LeanObject,
    mut v_00_u03b2_3092_: *mut leanh::LeanObject,
    mut v_inst_3093_: *mut leanh::LeanObject,
    mut v_inst_3094_: *mut leanh::LeanObject,
    mut v_m_3095_: *mut leanh::LeanObject,
    mut v_a_3096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Std_HashMap_Raw_getKey_x3f(
        v_00_u03b1_3091_,
        v_00_u03b2_3092_,
        v_inst_3093_,
        v_inst_3094_,
        v_m_3095_,
        v_a_3096_,
    );
    leanh::lean_dec_ref(v_m_3095_);
    return v_res_3097_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey___redArg(
    mut v_inst_3098_: *mut leanh::LeanObject,
    mut v_inst_3099_: *mut leanh::LeanObject,
    mut v_m_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3098_,
        v_inst_3099_,
        v_m_3100_,
        v_a_3101_,
    );
    return v___x_3102_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey___redArg___boxed(
    mut v_inst_3103_: *mut leanh::LeanObject,
    mut v_inst_3104_: *mut leanh::LeanObject,
    mut v_m_3105_: *mut leanh::LeanObject,
    mut v_a_3106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3107_ =
        l_Std_HashMap_Raw_getKey___redArg(v_inst_3103_, v_inst_3104_, v_m_3105_, v_a_3106_);
    leanh::lean_dec_ref(v_m_3105_);
    return v_res_3107_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey(
    mut v_00_u03b1_3108_: *mut leanh::LeanObject,
    mut v_00_u03b2_3109_: *mut leanh::LeanObject,
    mut v_inst_3110_: *mut leanh::LeanObject,
    mut v_inst_3111_: *mut leanh::LeanObject,
    mut v_m_3112_: *mut leanh::LeanObject,
    mut v_a_3113_: *mut leanh::LeanObject,
    mut v_h_3114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3110_,
        v_inst_3111_,
        v_m_3112_,
        v_a_3113_,
    );
    return v___x_3115_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey___boxed(
    mut v_00_u03b1_3116_: *mut leanh::LeanObject,
    mut v_00_u03b2_3117_: *mut leanh::LeanObject,
    mut v_inst_3118_: *mut leanh::LeanObject,
    mut v_inst_3119_: *mut leanh::LeanObject,
    mut v_m_3120_: *mut leanh::LeanObject,
    mut v_a_3121_: *mut leanh::LeanObject,
    mut v_h_3122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3123_ = l_Std_HashMap_Raw_getKey(
        v_00_u03b1_3116_,
        v_00_u03b2_3117_,
        v_inst_3118_,
        v_inst_3119_,
        v_m_3120_,
        v_a_3121_,
        v_h_3122_,
    );
    leanh::lean_dec_ref(v_m_3120_);
    return v_res_3123_;
}
pub unsafe fn l_Std_HashMap_Raw_getKeyD___redArg(
    mut v_inst_3124_: *mut leanh::LeanObject,
    mut v_inst_3125_: *mut leanh::LeanObject,
    mut v_m_3126_: *mut leanh::LeanObject,
    mut v_a_3127_: *mut leanh::LeanObject,
    mut v_fallback_3128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    v_buckets_3129_ = leanh::lean_ctor_get(v_m_3126_, 1);
    v___x_3130_ = leanh::lean_unsigned_to_nat(0);
    v___x_3131_ = lean_array_get_size(v_buckets_3129_);
    v___x_3132_ = lean_nat_dec_lt(v___x_3130_, v___x_3131_);
    if v___x_3132_ == 0 {
        leanh::lean_dec(v_a_3127_);
        leanh::lean_dec_ref(v_inst_3125_);
        leanh::lean_dec_ref(v_inst_3124_);
        leanh::lean_inc(v_fallback_3128_);
        return v_fallback_3128_;
    } else {
        let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3133_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
            v_inst_3124_,
            v_inst_3125_,
            v_m_3126_,
            v_a_3127_,
            v_fallback_3128_,
        );
        return v___x_3133_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getKeyD___redArg___boxed(
    mut v_inst_3134_: *mut leanh::LeanObject,
    mut v_inst_3135_: *mut leanh::LeanObject,
    mut v_m_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_fallback_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_Std_HashMap_Raw_getKeyD___redArg(
        v_inst_3134_,
        v_inst_3135_,
        v_m_3136_,
        v_a_3137_,
        v_fallback_3138_,
    );
    leanh::lean_dec(v_fallback_3138_);
    leanh::lean_dec_ref(v_m_3136_);
    return v_res_3139_;
}
pub unsafe fn l_Std_HashMap_Raw_getKeyD(
    mut v_00_u03b1_3140_: *mut leanh::LeanObject,
    mut v_00_u03b2_3141_: *mut leanh::LeanObject,
    mut v_inst_3142_: *mut leanh::LeanObject,
    mut v_inst_3143_: *mut leanh::LeanObject,
    mut v_m_3144_: *mut leanh::LeanObject,
    mut v_a_3145_: *mut leanh::LeanObject,
    mut v_fallback_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    v_buckets_3147_ = leanh::lean_ctor_get(v_m_3144_, 1);
    v___x_3148_ = leanh::lean_unsigned_to_nat(0);
    v___x_3149_ = lean_array_get_size(v_buckets_3147_);
    v___x_3150_ = lean_nat_dec_lt(v___x_3148_, v___x_3149_);
    if v___x_3150_ == 0 {
        leanh::lean_dec(v_a_3145_);
        leanh::lean_dec_ref(v_inst_3143_);
        leanh::lean_dec_ref(v_inst_3142_);
        leanh::lean_inc(v_fallback_3146_);
        return v_fallback_3146_;
    } else {
        let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
            v_inst_3142_,
            v_inst_3143_,
            v_m_3144_,
            v_a_3145_,
            v_fallback_3146_,
        );
        return v___x_3151_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getKeyD___boxed(
    mut v_00_u03b1_3152_: *mut leanh::LeanObject,
    mut v_00_u03b2_3153_: *mut leanh::LeanObject,
    mut v_inst_3154_: *mut leanh::LeanObject,
    mut v_inst_3155_: *mut leanh::LeanObject,
    mut v_m_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_fallback_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_Std_HashMap_Raw_getKeyD(
        v_00_u03b1_3152_,
        v_00_u03b2_3153_,
        v_inst_3154_,
        v_inst_3155_,
        v_m_3156_,
        v_a_3157_,
        v_fallback_3158_,
    );
    leanh::lean_dec(v_fallback_3158_);
    leanh::lean_dec_ref(v_m_3156_);
    return v_res_3159_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x21___redArg(
    mut v_inst_3160_: *mut leanh::LeanObject,
    mut v_inst_3161_: *mut leanh::LeanObject,
    mut v_inst_3162_: *mut leanh::LeanObject,
    mut v_m_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    v_buckets_3165_ = leanh::lean_ctor_get(v_m_3163_, 1);
    v___x_3166_ = leanh::lean_unsigned_to_nat(0);
    v___x_3167_ = lean_array_get_size(v_buckets_3165_);
    v___x_3168_ = lean_nat_dec_lt(v___x_3166_, v___x_3167_);
    if v___x_3168_ == 0 {
        leanh::lean_dec(v_a_3164_);
        leanh::lean_dec_ref(v_inst_3161_);
        leanh::lean_dec_ref(v_inst_3160_);
        leanh::lean_inc(v_inst_3162_);
        return v_inst_3162_;
    } else {
        let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3169_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
            v_inst_3160_,
            v_inst_3161_,
            v_inst_3162_,
            v_m_3163_,
            v_a_3164_,
        );
        return v___x_3169_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x21___redArg___boxed(
    mut v_inst_3170_: *mut leanh::LeanObject,
    mut v_inst_3171_: *mut leanh::LeanObject,
    mut v_inst_3172_: *mut leanh::LeanObject,
    mut v_m_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_Std_HashMap_Raw_getKey_x21___redArg(
        v_inst_3170_,
        v_inst_3171_,
        v_inst_3172_,
        v_m_3173_,
        v_a_3174_,
    );
    leanh::lean_dec_ref(v_m_3173_);
    leanh::lean_dec(v_inst_3172_);
    return v_res_3175_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x21(
    mut v_00_u03b1_3176_: *mut leanh::LeanObject,
    mut v_00_u03b2_3177_: *mut leanh::LeanObject,
    mut v_inst_3178_: *mut leanh::LeanObject,
    mut v_inst_3179_: *mut leanh::LeanObject,
    mut v_inst_3180_: *mut leanh::LeanObject,
    mut v_m_3181_: *mut leanh::LeanObject,
    mut v_a_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    v_buckets_3183_ = leanh::lean_ctor_get(v_m_3181_, 1);
    v___x_3184_ = leanh::lean_unsigned_to_nat(0);
    v___x_3185_ = lean_array_get_size(v_buckets_3183_);
    v___x_3186_ = lean_nat_dec_lt(v___x_3184_, v___x_3185_);
    if v___x_3186_ == 0 {
        leanh::lean_dec(v_a_3182_);
        leanh::lean_dec_ref(v_inst_3179_);
        leanh::lean_dec_ref(v_inst_3178_);
        leanh::lean_inc(v_inst_3180_);
        return v_inst_3180_;
    } else {
        let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3187_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
            v_inst_3178_,
            v_inst_3179_,
            v_inst_3180_,
            v_m_3181_,
            v_a_3182_,
        );
        return v___x_3187_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x21___boxed(
    mut v_00_u03b1_3188_: *mut leanh::LeanObject,
    mut v_00_u03b2_3189_: *mut leanh::LeanObject,
    mut v_inst_3190_: *mut leanh::LeanObject,
    mut v_inst_3191_: *mut leanh::LeanObject,
    mut v_inst_3192_: *mut leanh::LeanObject,
    mut v_m_3193_: *mut leanh::LeanObject,
    mut v_a_3194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_Std_HashMap_Raw_getKey_x21(
        v_00_u03b1_3188_,
        v_00_u03b2_3189_,
        v_inst_3190_,
        v_inst_3191_,
        v_inst_3192_,
        v_m_3193_,
        v_a_3194_,
    );
    leanh::lean_dec_ref(v_m_3193_);
    leanh::lean_dec(v_inst_3192_);
    return v_res_3195_;
}
pub unsafe fn l_Std_HashMap_Raw_erase___redArg(
    mut v_inst_3196_: *mut leanh::LeanObject,
    mut v_inst_3197_: *mut leanh::LeanObject,
    mut v_m_3198_: *mut leanh::LeanObject,
    mut v_a_3199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    v_buckets_3200_ = leanh::lean_ctor_get(v_m_3198_, 1);
    v___x_3201_ = leanh::lean_unsigned_to_nat(0);
    v___x_3202_ = lean_array_get_size(v_buckets_3200_);
    v___x_3203_ = lean_nat_dec_lt(v___x_3201_, v___x_3202_);
    if v___x_3203_ == 0 {
        leanh::lean_dec(v_a_3199_);
        leanh::lean_dec_ref(v_inst_3197_);
        leanh::lean_dec_ref(v_inst_3196_);
        return v_m_3198_;
    } else {
        let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3204_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
            v_inst_3196_,
            v_inst_3197_,
            v_m_3198_,
            v_a_3199_,
        );
        return v___x_3204_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_erase(
    mut v_00_u03b1_3205_: *mut leanh::LeanObject,
    mut v_00_u03b2_3206_: *mut leanh::LeanObject,
    mut v_inst_3207_: *mut leanh::LeanObject,
    mut v_inst_3208_: *mut leanh::LeanObject,
    mut v_m_3209_: *mut leanh::LeanObject,
    mut v_a_3210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    v_buckets_3211_ = leanh::lean_ctor_get(v_m_3209_, 1);
    v___x_3212_ = leanh::lean_unsigned_to_nat(0);
    v___x_3213_ = lean_array_get_size(v_buckets_3211_);
    v___x_3214_ = lean_nat_dec_lt(v___x_3212_, v___x_3213_);
    if v___x_3214_ == 0 {
        leanh::lean_dec(v_a_3210_);
        leanh::lean_dec_ref(v_inst_3208_);
        leanh::lean_dec_ref(v_inst_3207_);
        return v_m_3209_;
    } else {
        let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3215_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
            v_inst_3207_,
            v_inst_3208_,
            v_m_3209_,
            v_a_3210_,
        );
        return v___x_3215_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_size___redArg(
    mut v_m_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_3217_ = leanh::lean_ctor_get(v_m_3216_, 0);
    leanh::lean_inc(v_size_3217_);
    return v_size_3217_;
}
pub unsafe fn l_Std_HashMap_Raw_size___redArg___boxed(
    mut v_m_3218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3219_ = l_Std_HashMap_Raw_size___redArg(v_m_3218_);
    leanh::lean_dec_ref(v_m_3218_);
    return v_res_3219_;
}
pub unsafe fn l_Std_HashMap_Raw_size(
    mut v_00_u03b1_3220_: *mut leanh::LeanObject,
    mut v_00_u03b2_3221_: *mut leanh::LeanObject,
    mut v_m_3222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_3223_ = leanh::lean_ctor_get(v_m_3222_, 0);
    leanh::lean_inc(v_size_3223_);
    return v_size_3223_;
}
pub unsafe fn l_Std_HashMap_Raw_size___boxed(
    mut v_00_u03b1_3224_: *mut leanh::LeanObject,
    mut v_00_u03b2_3225_: *mut leanh::LeanObject,
    mut v_m_3226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3227_ = l_Std_HashMap_Raw_size(v_00_u03b1_3224_, v_00_u03b2_3225_, v_m_3226_);
    leanh::lean_dec_ref(v_m_3226_);
    return v_res_3227_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty___redArg(
    mut v_m_3228_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    v_size_3229_ = leanh::lean_ctor_get(v_m_3228_, 0);
    v___x_3230_ = leanh::lean_unsigned_to_nat(0);
    v___x_3231_ = lean_nat_dec_eq(v_size_3229_, v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty___redArg___boxed(
    mut v_m_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3233_: u8 = 0;
    let mut v_r_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3233_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_3232_);
    leanh::lean_dec_ref(v_m_3232_);
    v_r_3234_ = leanh::lean_box((v_res_3233_) as usize);
    return v_r_3234_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty(
    mut v_00_u03b1_3235_: *mut leanh::LeanObject,
    mut v_00_u03b2_3236_: *mut leanh::LeanObject,
    mut v_m_3237_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    v_size_3238_ = leanh::lean_ctor_get(v_m_3237_, 0);
    v___x_3239_ = leanh::lean_unsigned_to_nat(0);
    v___x_3240_ = lean_nat_dec_eq(v_size_3238_, v___x_3239_);
    return v___x_3240_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty___boxed(
    mut v_00_u03b1_3241_: *mut leanh::LeanObject,
    mut v_00_u03b2_3242_: *mut leanh::LeanObject,
    mut v_m_3243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3244_: u8 = 0;
    let mut v_r_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3244_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_3241_, v_00_u03b2_3242_, v_m_3243_);
    leanh::lean_dec_ref(v_m_3243_);
    v_r_3245_ = leanh::lean_box((v_res_3244_) as usize);
    return v_r_3245_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg___lam__0(
    mut v_a_3246_: *mut leanh::LeanObject,
    mut v_b_3247_: *mut leanh::LeanObject,
    mut v_d_3248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3249_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3249_, 0, v_a_3246_);
    leanh::lean_ctor_set(v___x_3249_, 1, v_d_3248_);
    return v___x_3249_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(
    mut v_a_3250_: *mut leanh::LeanObject,
    mut v_b_3251_: *mut leanh::LeanObject,
    mut v_d_3252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3253_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_3250_, v_b_3251_, v_d_3252_);
    leanh::lean_dec(v_b_3251_);
    return v_res_3253_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg___lam__1(
    mut v___x_3254_: *mut leanh::LeanObject,
    mut v___f_3255_: *mut leanh::LeanObject,
    mut v_l_3256_: *mut leanh::LeanObject,
    mut v_acc_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_3254_,
        v___f_3255_,
        v_acc_3257_,
        v_l_3256_,
    );
    return v___x_3258_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg(
    mut v_m_3282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    v___x_3283_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3284_ = leanh::lean_ctor_get(v_m_3282_, 1);
    leanh::lean_inc_ref(v_buckets_3284_);
    leanh::lean_dec_ref(v_m_3282_);
    v___x_3285_ = leanh::lean_box(0);
    v___x_3286_ = lean_array_get_size(v_buckets_3284_);
    v___x_3287_ = leanh::lean_unsigned_to_nat(0);
    v___x_3288_ = lean_nat_dec_lt(v___x_3287_, v___x_3286_);
    if v___x_3288_ == 0 {
        leanh::lean_dec_ref(v_buckets_3284_);
        return v___x_3285_;
    } else {
        let mut v___f_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3290_: usize = 0;
        let mut v___x_3291_: usize = 0;
        let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3289_ = l_Std_HashMap_Raw_keys___redArg___closed__11;
        v___x_3290_ = lean_usize_of_nat(v___x_3286_);
        v___x_3291_ = 0usize;
        v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3283_,
            v___f_3289_,
            v_buckets_3284_,
            v___x_3290_,
            v___x_3291_,
            v___x_3285_,
        );
        return v___x_3292_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_keys(
    mut v_00_u03b1_3293_: *mut leanh::LeanObject,
    mut v_00_u03b2_3294_: *mut leanh::LeanObject,
    mut v_m_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: u8 = 0;
    v___x_3296_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3297_ = leanh::lean_ctor_get(v_m_3295_, 1);
    leanh::lean_inc_ref(v_buckets_3297_);
    leanh::lean_dec_ref(v_m_3295_);
    v___x_3298_ = leanh::lean_box(0);
    v___x_3299_ = lean_array_get_size(v_buckets_3297_);
    v___x_3300_ = leanh::lean_unsigned_to_nat(0);
    v___x_3301_ = lean_nat_dec_lt(v___x_3300_, v___x_3299_);
    if v___x_3301_ == 0 {
        leanh::lean_dec_ref(v_buckets_3297_);
        return v___x_3298_;
    } else {
        let mut v___f_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3303_: usize = 0;
        let mut v___x_3304_: usize = 0;
        let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3302_ = l_Std_HashMap_Raw_keys___redArg___closed__11;
        v___x_3303_ = lean_usize_of_nat(v___x_3299_);
        v___x_3304_ = 0usize;
        v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3296_,
            v___f_3302_,
            v_buckets_3297_,
            v___x_3303_,
            v___x_3304_,
            v___x_3298_,
        );
        return v___x_3305_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_ofList___redArg(
    mut v_inst_3310_: *mut leanh::LeanObject,
    mut v_inst_3311_: *mut leanh::LeanObject,
    mut v_l_3312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    v___x_3313_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3314_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3314_ == 0 {
        leanh::lean_dec(v_l_3312_);
        leanh::lean_dec_ref(v_inst_3311_);
        leanh::lean_dec_ref(v_inst_3310_);
        return v___x_3313_;
    } else {
        let mut v___f_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3315_ = l_Std_HashMap_Raw_ofList___redArg___closed__1;
        v___x_3316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_3315_,
            v_inst_3310_,
            v_inst_3311_,
            v___x_3313_,
            v_l_3312_,
        );
        return v___x_3316_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_ofList(
    mut v_00_u03b1_3317_: *mut leanh::LeanObject,
    mut v_00_u03b2_3318_: *mut leanh::LeanObject,
    mut v_inst_3319_: *mut leanh::LeanObject,
    mut v_inst_3320_: *mut leanh::LeanObject,
    mut v_l_3321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: u8 = 0;
    v___x_3322_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3323_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3323_ == 0 {
        leanh::lean_dec(v_l_3321_);
        leanh::lean_dec_ref(v_inst_3320_);
        leanh::lean_dec_ref(v_inst_3319_);
        return v___x_3322_;
    } else {
        let mut v___f_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3324_ = l_Std_HashMap_Raw_ofList___redArg___closed__1;
        v___x_3325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_3324_,
            v_inst_3319_,
            v_inst_3320_,
            v___x_3322_,
            v_l_3321_,
        );
        return v___x_3325_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_unitOfList___redArg(
    mut v_inst_3326_: *mut leanh::LeanObject,
    mut v_inst_3327_: *mut leanh::LeanObject,
    mut v_l_3328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: u8 = 0;
    v___x_3329_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3330_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3330_ == 0 {
        leanh::lean_dec(v_l_3328_);
        leanh::lean_dec_ref(v_inst_3327_);
        leanh::lean_dec_ref(v_inst_3326_);
        return v___x_3329_;
    } else {
        let mut v___f_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3331_ = l_Std_HashMap_Raw_ofList___redArg___closed__1;
        v___x_3332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_3331_,
            v_inst_3326_,
            v_inst_3327_,
            v___x_3329_,
            v_l_3328_,
        );
        return v___x_3332_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_unitOfList(
    mut v_00_u03b1_3333_: *mut leanh::LeanObject,
    mut v_inst_3334_: *mut leanh::LeanObject,
    mut v_inst_3335_: *mut leanh::LeanObject,
    mut v_l_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    v___x_3337_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3338_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3338_ == 0 {
        leanh::lean_dec(v_l_3336_);
        leanh::lean_dec_ref(v_inst_3335_);
        leanh::lean_dec_ref(v_inst_3334_);
        return v___x_3337_;
    } else {
        let mut v___f_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3339_ = l_Std_HashMap_Raw_ofList___redArg___closed__1;
        v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_3339_,
            v_inst_3334_,
            v_inst_3335_,
            v___x_3337_,
            v_l_3336_,
        );
        return v___x_3340_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_ofArray___redArg(
    mut v_inst_3345_: *mut leanh::LeanObject,
    mut v_inst_3346_: *mut leanh::LeanObject,
    mut v_a_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: u8 = 0;
    v___x_3348_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3349_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3349_ == 0 {
        leanh::lean_dec_ref(v_a_3347_);
        leanh::lean_dec_ref(v_inst_3346_);
        leanh::lean_dec_ref(v_inst_3345_);
        return v___x_3348_;
    } else {
        let mut v___f_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3350_ = l_Std_HashMap_Raw_ofArray___redArg___closed__1;
        v___x_3351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_3350_,
            v_inst_3345_,
            v_inst_3346_,
            v___x_3348_,
            v_a_3347_,
        );
        return v___x_3351_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_ofArray(
    mut v_00_u03b1_3352_: *mut leanh::LeanObject,
    mut v_00_u03b2_3353_: *mut leanh::LeanObject,
    mut v_inst_3354_: *mut leanh::LeanObject,
    mut v_inst_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    v___x_3357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3358_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3358_ == 0 {
        leanh::lean_dec_ref(v_a_3356_);
        leanh::lean_dec_ref(v_inst_3355_);
        leanh::lean_dec_ref(v_inst_3354_);
        return v___x_3357_;
    } else {
        let mut v___f_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3359_ = l_Std_HashMap_Raw_ofArray___redArg___closed__1;
        v___x_3360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v___f_3359_,
            v_inst_3354_,
            v_inst_3355_,
            v___x_3357_,
            v_a_3356_,
        );
        return v___x_3360_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_alter___redArg(
    mut v_inst_3361_: *mut leanh::LeanObject,
    mut v_inst_3362_: *mut leanh::LeanObject,
    mut v_m_3363_: *mut leanh::LeanObject,
    mut v_a_3364_: *mut leanh::LeanObject,
    mut v_f_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: u8 = 0;
    v_buckets_3366_ = leanh::lean_ctor_get(v_m_3363_, 1);
    v___x_3367_ = leanh::lean_unsigned_to_nat(0);
    v___x_3368_ = lean_array_get_size(v_buckets_3366_);
    v___x_3369_ = lean_nat_dec_lt(v___x_3367_, v___x_3368_);
    if v___x_3369_ == 0 {
        let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_3365_);
        leanh::lean_dec(v_a_3364_);
        leanh::lean_dec_ref(v_m_3363_);
        leanh::lean_dec_ref(v_inst_3362_);
        leanh::lean_dec_ref(v_inst_3361_);
        v___x_3370_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3370_;
    } else {
        let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
            v_inst_3361_,
            v_inst_3362_,
            v_m_3363_,
            v_a_3364_,
            v_f_3365_,
        );
        return v___x_3371_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_alter(
    mut v_00_u03b1_3372_: *mut leanh::LeanObject,
    mut v_00_u03b2_3373_: *mut leanh::LeanObject,
    mut v_inst_3374_: *mut leanh::LeanObject,
    mut v_inst_3375_: *mut leanh::LeanObject,
    mut v_inst_3376_: *mut leanh::LeanObject,
    mut v_m_3377_: *mut leanh::LeanObject,
    mut v_a_3378_: *mut leanh::LeanObject,
    mut v_f_3379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    v_buckets_3380_ = leanh::lean_ctor_get(v_m_3377_, 1);
    v___x_3381_ = leanh::lean_unsigned_to_nat(0);
    v___x_3382_ = lean_array_get_size(v_buckets_3380_);
    v___x_3383_ = lean_nat_dec_lt(v___x_3381_, v___x_3382_);
    if v___x_3383_ == 0 {
        let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_3379_);
        leanh::lean_dec(v_a_3378_);
        leanh::lean_dec_ref(v_m_3377_);
        leanh::lean_dec_ref(v_inst_3376_);
        leanh::lean_dec_ref(v_inst_3374_);
        v___x_3384_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3384_;
    } else {
        let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
            v_inst_3374_,
            v_inst_3376_,
            v_m_3377_,
            v_a_3378_,
            v_f_3379_,
        );
        return v___x_3385_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_modify___redArg(
    mut v_inst_3386_: *mut leanh::LeanObject,
    mut v_inst_3387_: *mut leanh::LeanObject,
    mut v_m_3388_: *mut leanh::LeanObject,
    mut v_a_3389_: *mut leanh::LeanObject,
    mut v_f_3390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    v_buckets_3391_ = leanh::lean_ctor_get(v_m_3388_, 1);
    v___x_3392_ = leanh::lean_unsigned_to_nat(0);
    v___x_3393_ = lean_array_get_size(v_buckets_3391_);
    v___x_3394_ = lean_nat_dec_lt(v___x_3392_, v___x_3393_);
    if v___x_3394_ == 0 {
        let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_3390_);
        leanh::lean_dec(v_a_3389_);
        leanh::lean_dec_ref(v_m_3388_);
        leanh::lean_dec_ref(v_inst_3387_);
        leanh::lean_dec_ref(v_inst_3386_);
        v___x_3395_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3395_;
    } else {
        let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3396_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
            v_inst_3386_,
            v_inst_3387_,
            v_m_3388_,
            v_a_3389_,
            v_f_3390_,
        );
        return v___x_3396_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_modify(
    mut v_00_u03b1_3397_: *mut leanh::LeanObject,
    mut v_00_u03b2_3398_: *mut leanh::LeanObject,
    mut v_inst_3399_: *mut leanh::LeanObject,
    mut v_inst_3400_: *mut leanh::LeanObject,
    mut v_inst_3401_: *mut leanh::LeanObject,
    mut v_m_3402_: *mut leanh::LeanObject,
    mut v_a_3403_: *mut leanh::LeanObject,
    mut v_f_3404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: u8 = 0;
    v_buckets_3405_ = leanh::lean_ctor_get(v_m_3402_, 1);
    v___x_3406_ = leanh::lean_unsigned_to_nat(0);
    v___x_3407_ = lean_array_get_size(v_buckets_3405_);
    v___x_3408_ = lean_nat_dec_lt(v___x_3406_, v___x_3407_);
    if v___x_3408_ == 0 {
        let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_3404_);
        leanh::lean_dec(v_a_3403_);
        leanh::lean_dec_ref(v_m_3402_);
        leanh::lean_dec_ref(v_inst_3401_);
        leanh::lean_dec_ref(v_inst_3399_);
        v___x_3409_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3409_;
    } else {
        let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
            v_inst_3399_,
            v_inst_3401_,
            v_m_3402_,
            v_a_3403_,
            v_f_3404_,
        );
        return v___x_3410_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_toList___redArg___lam__0(
    mut v_a_3411_: *mut leanh::LeanObject,
    mut v_b_3412_: *mut leanh::LeanObject,
    mut v_d_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3414_, 0, v_a_3411_);
    leanh::lean_ctor_set(v___x_3414_, 1, v_b_3412_);
    v___x_3415_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3415_, 0, v___x_3414_);
    leanh::lean_ctor_set(v___x_3415_, 1, v_d_3413_);
    return v___x_3415_;
}
pub unsafe fn l_Std_HashMap_Raw_toList___redArg___lam__1(
    mut v___x_3416_: *mut leanh::LeanObject,
    mut v___f_3417_: *mut leanh::LeanObject,
    mut v_l_3418_: *mut leanh::LeanObject,
    mut v_acc_3419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3420_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_3416_,
        v___f_3417_,
        v_acc_3419_,
        v_l_3418_,
    );
    return v___x_3420_;
}
pub unsafe fn l_Std_HashMap_Raw_toList___redArg(
    mut v_m_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    v___x_3426_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3427_ = leanh::lean_ctor_get(v_m_3425_, 1);
    leanh::lean_inc_ref(v_buckets_3427_);
    leanh::lean_dec_ref(v_m_3425_);
    v___x_3428_ = leanh::lean_box(0);
    v___x_3429_ = lean_array_get_size(v_buckets_3427_);
    v___x_3430_ = leanh::lean_unsigned_to_nat(0);
    v___x_3431_ = lean_nat_dec_lt(v___x_3430_, v___x_3429_);
    if v___x_3431_ == 0 {
        leanh::lean_dec_ref(v_buckets_3427_);
        return v___x_3428_;
    } else {
        let mut v___f_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3433_: usize = 0;
        let mut v___x_3434_: usize = 0;
        let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3432_ = l_Std_HashMap_Raw_toList___redArg___closed__1;
        v___x_3433_ = lean_usize_of_nat(v___x_3429_);
        v___x_3434_ = 0usize;
        v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3426_,
            v___f_3432_,
            v_buckets_3427_,
            v___x_3433_,
            v___x_3434_,
            v___x_3428_,
        );
        return v___x_3435_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_toList(
    mut v_00_u03b1_3436_: *mut leanh::LeanObject,
    mut v_00_u03b2_3437_: *mut leanh::LeanObject,
    mut v_m_3438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: u8 = 0;
    v___x_3439_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3440_ = leanh::lean_ctor_get(v_m_3438_, 1);
    leanh::lean_inc_ref(v_buckets_3440_);
    leanh::lean_dec_ref(v_m_3438_);
    v___x_3441_ = leanh::lean_box(0);
    v___x_3442_ = lean_array_get_size(v_buckets_3440_);
    v___x_3443_ = leanh::lean_unsigned_to_nat(0);
    v___x_3444_ = lean_nat_dec_lt(v___x_3443_, v___x_3442_);
    if v___x_3444_ == 0 {
        leanh::lean_dec_ref(v_buckets_3440_);
        return v___x_3441_;
    } else {
        let mut v___f_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3446_: usize = 0;
        let mut v___x_3447_: usize = 0;
        let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3445_ = l_Std_HashMap_Raw_toList___redArg___closed__1;
        v___x_3446_ = lean_usize_of_nat(v___x_3442_);
        v___x_3447_ = 0usize;
        v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3439_,
            v___f_3445_,
            v_buckets_3440_,
            v___x_3446_,
            v___x_3447_,
            v___x_3441_,
        );
        return v___x_3448_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_foldM___redArg___lam__0(
    mut v_inst_3449_: *mut leanh::LeanObject,
    mut v_f_3450_: *mut leanh::LeanObject,
    mut v_acc_3451_: *mut leanh::LeanObject,
    mut v_l_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_3449_,
        v_f_3450_,
        v_acc_3451_,
        v_l_3452_,
    );
    return v___x_3453_;
}
pub unsafe fn l_Std_HashMap_Raw_foldM___redArg(
    mut v_inst_3454_: *mut leanh::LeanObject,
    mut v_f_3455_: *mut leanh::LeanObject,
    mut v_init_3456_: *mut leanh::LeanObject,
    mut v_b_3457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    v_buckets_3458_ = leanh::lean_ctor_get(v_b_3457_, 1);
    leanh::lean_inc_ref(v_buckets_3458_);
    leanh::lean_dec_ref(v_b_3457_);
    v___x_3459_ = leanh::lean_unsigned_to_nat(0);
    v___x_3460_ = lean_array_get_size(v_buckets_3458_);
    v___x_3461_ = lean_nat_dec_lt(v___x_3459_, v___x_3460_);
    if v___x_3461_ == 0 {
        let mut v_toApplicative_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3458_);
        leanh::lean_dec(v_f_3455_);
        v_toApplicative_3462_ = leanh::lean_ctor_get(v_inst_3454_, 0);
        leanh::lean_inc_ref(v_toApplicative_3462_);
        leanh::lean_dec_ref(v_inst_3454_);
        v_toPure_3463_ = leanh::lean_ctor_get(v_toApplicative_3462_, 1);
        leanh::lean_inc(v_toPure_3463_);
        leanh::lean_dec_ref(v_toApplicative_3462_);
        v___x_3464_ =
            leanh::lean_apply_2(v_toPure_3463_, leanh::lean_box(0), v_init_3456_);
        return v___x_3464_;
    } else {
        let mut v___f_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3466_: u8 = 0;
        leanh::lean_inc_ref(v_inst_3454_);
        v___f_3465_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3465_, 0, v_inst_3454_);
        leanh::lean_closure_set(v___f_3465_, 1, v_f_3455_);
        v___x_3466_ = lean_nat_dec_le(v___x_3460_, v___x_3460_);
        if v___x_3466_ == 0 {
            if v___x_3461_ == 0 {
                let mut v_toApplicative_3467_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3465_);
                leanh::lean_dec_ref(v_buckets_3458_);
                v_toApplicative_3467_ = leanh::lean_ctor_get(v_inst_3454_, 0);
                leanh::lean_inc_ref(v_toApplicative_3467_);
                leanh::lean_dec_ref(v_inst_3454_);
                v_toPure_3468_ = leanh::lean_ctor_get(v_toApplicative_3467_, 1);
                leanh::lean_inc(v_toPure_3468_);
                leanh::lean_dec_ref(v_toApplicative_3467_);
                v___x_3469_ = leanh::lean_apply_2(
                    v_toPure_3468_,
                    leanh::lean_box(0),
                    v_init_3456_,
                );
                return v___x_3469_;
            } else {
                let mut v___x_3470_: usize = 0;
                let mut v___x_3471_: usize = 0;
                let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3470_ = 0usize;
                v___x_3471_ = lean_usize_of_nat(v___x_3460_);
                v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3454_,
                    v___f_3465_,
                    v_buckets_3458_,
                    v___x_3470_,
                    v___x_3471_,
                    v_init_3456_,
                );
                return v___x_3472_;
            }
        } else {
            let mut v___x_3473_: usize = 0;
            let mut v___x_3474_: usize = 0;
            let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3473_ = 0usize;
            v___x_3474_ = lean_usize_of_nat(v___x_3460_);
            v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3454_,
                v___f_3465_,
                v_buckets_3458_,
                v___x_3473_,
                v___x_3474_,
                v_init_3456_,
            );
            return v___x_3475_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_foldM(
    mut v_00_u03b1_3476_: *mut leanh::LeanObject,
    mut v_00_u03b2_3477_: *mut leanh::LeanObject,
    mut v_m_3478_: *mut leanh::LeanObject,
    mut v_inst_3479_: *mut leanh::LeanObject,
    mut v_00_u03b3_3480_: *mut leanh::LeanObject,
    mut v_f_3481_: *mut leanh::LeanObject,
    mut v_init_3482_: *mut leanh::LeanObject,
    mut v_b_3483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: u8 = 0;
    v_buckets_3484_ = leanh::lean_ctor_get(v_b_3483_, 1);
    leanh::lean_inc_ref(v_buckets_3484_);
    leanh::lean_dec_ref(v_b_3483_);
    v___x_3485_ = leanh::lean_unsigned_to_nat(0);
    v___x_3486_ = lean_array_get_size(v_buckets_3484_);
    v___x_3487_ = lean_nat_dec_lt(v___x_3485_, v___x_3486_);
    if v___x_3487_ == 0 {
        let mut v_toApplicative_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3484_);
        leanh::lean_dec(v_f_3481_);
        v_toApplicative_3488_ = leanh::lean_ctor_get(v_inst_3479_, 0);
        leanh::lean_inc_ref(v_toApplicative_3488_);
        leanh::lean_dec_ref(v_inst_3479_);
        v_toPure_3489_ = leanh::lean_ctor_get(v_toApplicative_3488_, 1);
        leanh::lean_inc(v_toPure_3489_);
        leanh::lean_dec_ref(v_toApplicative_3488_);
        v___x_3490_ =
            leanh::lean_apply_2(v_toPure_3489_, leanh::lean_box(0), v_init_3482_);
        return v___x_3490_;
    } else {
        let mut v___f_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3492_: u8 = 0;
        leanh::lean_inc_ref(v_inst_3479_);
        v___f_3491_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3491_, 0, v_inst_3479_);
        leanh::lean_closure_set(v___f_3491_, 1, v_f_3481_);
        v___x_3492_ = lean_nat_dec_le(v___x_3486_, v___x_3486_);
        if v___x_3492_ == 0 {
            if v___x_3487_ == 0 {
                let mut v_toApplicative_3493_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3491_);
                leanh::lean_dec_ref(v_buckets_3484_);
                v_toApplicative_3493_ = leanh::lean_ctor_get(v_inst_3479_, 0);
                leanh::lean_inc_ref(v_toApplicative_3493_);
                leanh::lean_dec_ref(v_inst_3479_);
                v_toPure_3494_ = leanh::lean_ctor_get(v_toApplicative_3493_, 1);
                leanh::lean_inc(v_toPure_3494_);
                leanh::lean_dec_ref(v_toApplicative_3493_);
                v___x_3495_ = leanh::lean_apply_2(
                    v_toPure_3494_,
                    leanh::lean_box(0),
                    v_init_3482_,
                );
                return v___x_3495_;
            } else {
                let mut v___x_3496_: usize = 0;
                let mut v___x_3497_: usize = 0;
                let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3496_ = 0usize;
                v___x_3497_ = lean_usize_of_nat(v___x_3486_);
                v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3479_,
                    v___f_3491_,
                    v_buckets_3484_,
                    v___x_3496_,
                    v___x_3497_,
                    v_init_3482_,
                );
                return v___x_3498_;
            }
        } else {
            let mut v___x_3499_: usize = 0;
            let mut v___x_3500_: usize = 0;
            let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3499_ = 0usize;
            v___x_3500_ = lean_usize_of_nat(v___x_3486_);
            v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3479_,
                v___f_3491_,
                v_buckets_3484_,
                v___x_3499_,
                v___x_3500_,
                v_init_3482_,
            );
            return v___x_3501_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_fold___redArg___lam__0(
    mut v_f_3502_: *mut leanh::LeanObject,
    mut v_x1_3503_: *mut leanh::LeanObject,
    mut v_x2_3504_: *mut leanh::LeanObject,
    mut v_x3_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3506_ = leanh::lean_apply_3(v_f_3502_, v_x1_3503_, v_x2_3504_, v_x3_3505_);
    return v___x_3506_;
}
pub unsafe fn l_Std_HashMap_Raw_fold___redArg___lam__1(
    mut v___x_3507_: *mut leanh::LeanObject,
    mut v___f_3508_: *mut leanh::LeanObject,
    mut v_acc_3509_: *mut leanh::LeanObject,
    mut v_l_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3511_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_3507_,
        v___f_3508_,
        v_acc_3509_,
        v_l_3510_,
    );
    return v___x_3511_;
}
pub unsafe fn l_Std_HashMap_Raw_fold___redArg(
    mut v_f_3512_: *mut leanh::LeanObject,
    mut v_init_3513_: *mut leanh::LeanObject,
    mut v_b_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    v___x_3515_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3516_ = leanh::lean_ctor_get(v_b_3514_, 1);
    leanh::lean_inc_ref(v_buckets_3516_);
    leanh::lean_dec_ref(v_b_3514_);
    v___x_3517_ = leanh::lean_unsigned_to_nat(0);
    v___x_3518_ = lean_array_get_size(v_buckets_3516_);
    v___x_3519_ = lean_nat_dec_lt(v___x_3517_, v___x_3518_);
    if v___x_3519_ == 0 {
        leanh::lean_dec_ref(v_buckets_3516_);
        leanh::lean_dec(v_f_3512_);
        return v_init_3513_;
    } else {
        let mut v___f_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3522_: u8 = 0;
        v___f_3520_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3520_, 0, v_f_3512_);
        v___f_3521_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3521_, 0, v___x_3515_);
        leanh::lean_closure_set(v___f_3521_, 1, v___f_3520_);
        v___x_3522_ = lean_nat_dec_le(v___x_3518_, v___x_3518_);
        if v___x_3522_ == 0 {
            if v___x_3519_ == 0 {
                leanh::lean_dec_ref(v___f_3521_);
                leanh::lean_dec_ref(v_buckets_3516_);
                return v_init_3513_;
            } else {
                let mut v___x_3523_: usize = 0;
                let mut v___x_3524_: usize = 0;
                let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3523_ = 0usize;
                v___x_3524_ = lean_usize_of_nat(v___x_3518_);
                v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3515_,
                    v___f_3521_,
                    v_buckets_3516_,
                    v___x_3523_,
                    v___x_3524_,
                    v_init_3513_,
                );
                return v___x_3525_;
            }
        } else {
            let mut v___x_3526_: usize = 0;
            let mut v___x_3527_: usize = 0;
            let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3526_ = 0usize;
            v___x_3527_ = lean_usize_of_nat(v___x_3518_);
            v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3515_,
                v___f_3521_,
                v_buckets_3516_,
                v___x_3526_,
                v___x_3527_,
                v_init_3513_,
            );
            return v___x_3528_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_fold(
    mut v_00_u03b1_3529_: *mut leanh::LeanObject,
    mut v_00_u03b2_3530_: *mut leanh::LeanObject,
    mut v_00_u03b3_3531_: *mut leanh::LeanObject,
    mut v_f_3532_: *mut leanh::LeanObject,
    mut v_init_3533_: *mut leanh::LeanObject,
    mut v_b_3534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    v___x_3535_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3536_ = leanh::lean_ctor_get(v_b_3534_, 1);
    leanh::lean_inc_ref(v_buckets_3536_);
    leanh::lean_dec_ref(v_b_3534_);
    v___x_3537_ = leanh::lean_unsigned_to_nat(0);
    v___x_3538_ = lean_array_get_size(v_buckets_3536_);
    v___x_3539_ = lean_nat_dec_lt(v___x_3537_, v___x_3538_);
    if v___x_3539_ == 0 {
        leanh::lean_dec_ref(v_buckets_3536_);
        leanh::lean_dec(v_f_3532_);
        return v_init_3533_;
    } else {
        let mut v___f_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3542_: u8 = 0;
        v___f_3540_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3540_, 0, v_f_3532_);
        v___f_3541_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3541_, 0, v___x_3535_);
        leanh::lean_closure_set(v___f_3541_, 1, v___f_3540_);
        v___x_3542_ = lean_nat_dec_le(v___x_3538_, v___x_3538_);
        if v___x_3542_ == 0 {
            if v___x_3539_ == 0 {
                leanh::lean_dec_ref(v___f_3541_);
                leanh::lean_dec_ref(v_buckets_3536_);
                return v_init_3533_;
            } else {
                let mut v___x_3543_: usize = 0;
                let mut v___x_3544_: usize = 0;
                let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3543_ = 0usize;
                v___x_3544_ = lean_usize_of_nat(v___x_3538_);
                v___x_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3535_,
                    v___f_3541_,
                    v_buckets_3536_,
                    v___x_3543_,
                    v___x_3544_,
                    v_init_3533_,
                );
                return v___x_3545_;
            }
        } else {
            let mut v___x_3546_: usize = 0;
            let mut v___x_3547_: usize = 0;
            let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3546_ = 0usize;
            v___x_3547_ = lean_usize_of_nat(v___x_3538_);
            v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3535_,
                v___f_3541_,
                v_buckets_3536_,
                v___x_3546_,
                v___x_3547_,
                v_init_3533_,
            );
            return v___x_3548_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_forM___redArg___lam__0(
    mut v_f_3549_: *mut leanh::LeanObject,
    mut v_x_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = leanh::lean_apply_2(v_f_3549_, v___y_3551_, v___y_3552_);
    return v___x_3553_;
}
pub unsafe fn l_Std_HashMap_Raw_forM___redArg___lam__1(
    mut v_inst_3554_: *mut leanh::LeanObject,
    mut v___f_3555_: *mut leanh::LeanObject,
    mut v_x_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = leanh::lean_box(0);
    v___x_3559_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_3554_,
        v___f_3555_,
        v___x_3558_,
        v___y_3557_,
    );
    return v___x_3559_;
}
pub unsafe fn l_Std_HashMap_Raw_forM___redArg(
    mut v_inst_3560_: *mut leanh::LeanObject,
    mut v_f_3561_: *mut leanh::LeanObject,
    mut v_b_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: u8 = 0;
    v_buckets_3563_ = leanh::lean_ctor_get(v_b_3562_, 1);
    leanh::lean_inc_ref(v_buckets_3563_);
    leanh::lean_dec_ref(v_b_3562_);
    v___x_3564_ = leanh::lean_unsigned_to_nat(0);
    v___x_3565_ = lean_array_get_size(v_buckets_3563_);
    v___x_3566_ = leanh::lean_box(0);
    v___x_3567_ = lean_nat_dec_lt(v___x_3564_, v___x_3565_);
    if v___x_3567_ == 0 {
        let mut v_toApplicative_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3563_);
        leanh::lean_dec(v_f_3561_);
        v_toApplicative_3568_ = leanh::lean_ctor_get(v_inst_3560_, 0);
        leanh::lean_inc_ref(v_toApplicative_3568_);
        leanh::lean_dec_ref(v_inst_3560_);
        v_toPure_3569_ = leanh::lean_ctor_get(v_toApplicative_3568_, 1);
        leanh::lean_inc(v_toPure_3569_);
        leanh::lean_dec_ref(v_toApplicative_3568_);
        v___x_3570_ =
            leanh::lean_apply_2(v_toPure_3569_, leanh::lean_box(0), v___x_3566_);
        return v___x_3570_;
    } else {
        let mut v___f_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3573_: u8 = 0;
        v___f_3571_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3571_, 0, v_f_3561_);
        leanh::lean_inc_ref(v_inst_3560_);
        v___f_3572_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3572_, 0, v_inst_3560_);
        leanh::lean_closure_set(v___f_3572_, 1, v___f_3571_);
        v___x_3573_ = lean_nat_dec_le(v___x_3565_, v___x_3565_);
        if v___x_3573_ == 0 {
            if v___x_3567_ == 0 {
                let mut v_toApplicative_3574_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3572_);
                leanh::lean_dec_ref(v_buckets_3563_);
                v_toApplicative_3574_ = leanh::lean_ctor_get(v_inst_3560_, 0);
                leanh::lean_inc_ref(v_toApplicative_3574_);
                leanh::lean_dec_ref(v_inst_3560_);
                v_toPure_3575_ = leanh::lean_ctor_get(v_toApplicative_3574_, 1);
                leanh::lean_inc(v_toPure_3575_);
                leanh::lean_dec_ref(v_toApplicative_3574_);
                v___x_3576_ = leanh::lean_apply_2(
                    v_toPure_3575_,
                    leanh::lean_box(0),
                    v___x_3566_,
                );
                return v___x_3576_;
            } else {
                let mut v___x_3577_: usize = 0;
                let mut v___x_3578_: usize = 0;
                let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3577_ = 0usize;
                v___x_3578_ = lean_usize_of_nat(v___x_3565_);
                v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3560_,
                    v___f_3572_,
                    v_buckets_3563_,
                    v___x_3577_,
                    v___x_3578_,
                    v___x_3566_,
                );
                return v___x_3579_;
            }
        } else {
            let mut v___x_3580_: usize = 0;
            let mut v___x_3581_: usize = 0;
            let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3580_ = 0usize;
            v___x_3581_ = lean_usize_of_nat(v___x_3565_);
            v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3560_,
                v___f_3572_,
                v_buckets_3563_,
                v___x_3580_,
                v___x_3581_,
                v___x_3566_,
            );
            return v___x_3582_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_forM(
    mut v_00_u03b1_3583_: *mut leanh::LeanObject,
    mut v_00_u03b2_3584_: *mut leanh::LeanObject,
    mut v_m_3585_: *mut leanh::LeanObject,
    mut v_inst_3586_: *mut leanh::LeanObject,
    mut v_f_3587_: *mut leanh::LeanObject,
    mut v_b_3588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    v_buckets_3589_ = leanh::lean_ctor_get(v_b_3588_, 1);
    leanh::lean_inc_ref(v_buckets_3589_);
    leanh::lean_dec_ref(v_b_3588_);
    v___x_3590_ = leanh::lean_unsigned_to_nat(0);
    v___x_3591_ = lean_array_get_size(v_buckets_3589_);
    v___x_3592_ = leanh::lean_box(0);
    v___x_3593_ = lean_nat_dec_lt(v___x_3590_, v___x_3591_);
    if v___x_3593_ == 0 {
        let mut v_toApplicative_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3589_);
        leanh::lean_dec(v_f_3587_);
        v_toApplicative_3594_ = leanh::lean_ctor_get(v_inst_3586_, 0);
        leanh::lean_inc_ref(v_toApplicative_3594_);
        leanh::lean_dec_ref(v_inst_3586_);
        v_toPure_3595_ = leanh::lean_ctor_get(v_toApplicative_3594_, 1);
        leanh::lean_inc(v_toPure_3595_);
        leanh::lean_dec_ref(v_toApplicative_3594_);
        v___x_3596_ =
            leanh::lean_apply_2(v_toPure_3595_, leanh::lean_box(0), v___x_3592_);
        return v___x_3596_;
    } else {
        let mut v___f_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3599_: u8 = 0;
        v___f_3597_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3597_, 0, v_f_3587_);
        leanh::lean_inc_ref(v_inst_3586_);
        v___f_3598_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3598_, 0, v_inst_3586_);
        leanh::lean_closure_set(v___f_3598_, 1, v___f_3597_);
        v___x_3599_ = lean_nat_dec_le(v___x_3591_, v___x_3591_);
        if v___x_3599_ == 0 {
            if v___x_3593_ == 0 {
                let mut v_toApplicative_3600_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3598_);
                leanh::lean_dec_ref(v_buckets_3589_);
                v_toApplicative_3600_ = leanh::lean_ctor_get(v_inst_3586_, 0);
                leanh::lean_inc_ref(v_toApplicative_3600_);
                leanh::lean_dec_ref(v_inst_3586_);
                v_toPure_3601_ = leanh::lean_ctor_get(v_toApplicative_3600_, 1);
                leanh::lean_inc(v_toPure_3601_);
                leanh::lean_dec_ref(v_toApplicative_3600_);
                v___x_3602_ = leanh::lean_apply_2(
                    v_toPure_3601_,
                    leanh::lean_box(0),
                    v___x_3592_,
                );
                return v___x_3602_;
            } else {
                let mut v___x_3603_: usize = 0;
                let mut v___x_3604_: usize = 0;
                let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3603_ = 0usize;
                v___x_3604_ = lean_usize_of_nat(v___x_3591_);
                v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3586_,
                    v___f_3598_,
                    v_buckets_3589_,
                    v___x_3603_,
                    v___x_3604_,
                    v___x_3592_,
                );
                return v___x_3605_;
            }
        } else {
            let mut v___x_3606_: usize = 0;
            let mut v___x_3607_: usize = 0;
            let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3606_ = 0usize;
            v___x_3607_ = lean_usize_of_nat(v___x_3591_);
            v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3586_,
                v___f_3598_,
                v_buckets_3589_,
                v___x_3606_,
                v___x_3607_,
                v___x_3592_,
            );
            return v___x_3608_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_forIn___redArg___lam__0(
    mut v_inst_3609_: *mut leanh::LeanObject,
    mut v_f_3610_: *mut leanh::LeanObject,
    mut v_a_3611_: *mut leanh::LeanObject,
    mut v_x_3612_: *mut leanh::LeanObject,
    mut v___y_3613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_inst_3609_, v_f_3610_, v_a_3611_, v___y_3613_);
    return v___x_3614_;
}
pub unsafe fn l_Std_HashMap_Raw_forIn___redArg(
    mut v_inst_3615_: *mut leanh::LeanObject,
    mut v_f_3616_: *mut leanh::LeanObject,
    mut v_init_3617_: *mut leanh::LeanObject,
    mut v_b_3618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3621_: usize = 0;
    let mut v___x_3622_: usize = 0;
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3619_ = leanh::lean_ctor_get(v_b_3618_, 1);
    leanh::lean_inc_ref(v_buckets_3619_);
    leanh::lean_dec_ref(v_b_3618_);
    leanh::lean_inc_ref(v_inst_3615_);
    v___f_3620_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3620_, 0, v_inst_3615_);
    leanh::lean_closure_set(v___f_3620_, 1, v_f_3616_);
    v_sz_3621_ = lean_array_size(v_buckets_3619_);
    v___x_3622_ = 0usize;
    v___x_3623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3615_,
        v_buckets_3619_,
        v___f_3620_,
        v_sz_3621_,
        v___x_3622_,
        v_init_3617_,
    );
    return v___x_3623_;
}
pub unsafe fn l_Std_HashMap_Raw_forIn(
    mut v_00_u03b1_3624_: *mut leanh::LeanObject,
    mut v_00_u03b2_3625_: *mut leanh::LeanObject,
    mut v_m_3626_: *mut leanh::LeanObject,
    mut v_inst_3627_: *mut leanh::LeanObject,
    mut v_00_u03b3_3628_: *mut leanh::LeanObject,
    mut v_f_3629_: *mut leanh::LeanObject,
    mut v_init_3630_: *mut leanh::LeanObject,
    mut v_b_3631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3634_: usize = 0;
    let mut v___x_3635_: usize = 0;
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3632_ = leanh::lean_ctor_get(v_b_3631_, 1);
    leanh::lean_inc_ref(v_buckets_3632_);
    leanh::lean_dec_ref(v_b_3631_);
    leanh::lean_inc_ref(v_inst_3627_);
    v___f_3633_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3633_, 0, v_inst_3627_);
    leanh::lean_closure_set(v___f_3633_, 1, v_f_3629_);
    v_sz_3634_ = lean_array_size(v_buckets_3632_);
    v___x_3635_ = 0usize;
    v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3627_,
        v_buckets_3632_,
        v___f_3633_,
        v_sz_3634_,
        v___x_3635_,
        v_init_3630_,
    );
    return v___x_3636_;
}
pub unsafe fn l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(
    mut v_f_3637_: *mut leanh::LeanObject,
    mut v_x_3638_: *mut leanh::LeanObject,
    mut v___y_3639_: *mut leanh::LeanObject,
    mut v___y_3640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3641_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3641_, 0, v___y_3639_);
    leanh::lean_ctor_set(v___x_3641_, 1, v___y_3640_);
    v___x_3642_ = leanh::lean_apply_1(v_f_3637_, v___x_3641_);
    return v___x_3642_;
}
pub unsafe fn l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(
    mut v_inst_3643_: *mut leanh::LeanObject,
    mut v_m_3644_: *mut leanh::LeanObject,
    mut v_f_3645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    v_buckets_3646_ = leanh::lean_ctor_get(v_m_3644_, 1);
    leanh::lean_inc_ref(v_buckets_3646_);
    leanh::lean_dec_ref(v_m_3644_);
    v___x_3647_ = leanh::lean_unsigned_to_nat(0);
    v___x_3648_ = lean_array_get_size(v_buckets_3646_);
    v___x_3649_ = leanh::lean_box(0);
    v___x_3650_ = lean_nat_dec_lt(v___x_3647_, v___x_3648_);
    if v___x_3650_ == 0 {
        let mut v_toApplicative_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3646_);
        leanh::lean_dec(v_f_3645_);
        v_toApplicative_3651_ = leanh::lean_ctor_get(v_inst_3643_, 0);
        leanh::lean_inc_ref(v_toApplicative_3651_);
        leanh::lean_dec_ref(v_inst_3643_);
        v_toPure_3652_ = leanh::lean_ctor_get(v_toApplicative_3651_, 1);
        leanh::lean_inc(v_toPure_3652_);
        leanh::lean_dec_ref(v_toApplicative_3651_);
        v___x_3653_ =
            leanh::lean_apply_2(v_toPure_3652_, leanh::lean_box(0), v___x_3649_);
        return v___x_3653_;
    } else {
        let mut v___f_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3656_: u8 = 0;
        v___f_3654_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3654_, 0, v_f_3645_);
        leanh::lean_inc_ref(v_inst_3643_);
        v___f_3655_ = leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3655_, 0, v_inst_3643_);
        leanh::lean_closure_set(v___f_3655_, 1, v___f_3654_);
        v___x_3656_ = lean_nat_dec_le(v___x_3648_, v___x_3648_);
        if v___x_3656_ == 0 {
            if v___x_3650_ == 0 {
                let mut v_toApplicative_3657_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3655_);
                leanh::lean_dec_ref(v_buckets_3646_);
                v_toApplicative_3657_ = leanh::lean_ctor_get(v_inst_3643_, 0);
                leanh::lean_inc_ref(v_toApplicative_3657_);
                leanh::lean_dec_ref(v_inst_3643_);
                v_toPure_3658_ = leanh::lean_ctor_get(v_toApplicative_3657_, 1);
                leanh::lean_inc(v_toPure_3658_);
                leanh::lean_dec_ref(v_toApplicative_3657_);
                v___x_3659_ = leanh::lean_apply_2(
                    v_toPure_3658_,
                    leanh::lean_box(0),
                    v___x_3649_,
                );
                return v___x_3659_;
            } else {
                let mut v___x_3660_: usize = 0;
                let mut v___x_3661_: usize = 0;
                let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3660_ = 0usize;
                v___x_3661_ = lean_usize_of_nat(v___x_3648_);
                v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3643_,
                    v___f_3655_,
                    v_buckets_3646_,
                    v___x_3660_,
                    v___x_3661_,
                    v___x_3649_,
                );
                return v___x_3662_;
            }
        } else {
            let mut v___x_3663_: usize = 0;
            let mut v___x_3664_: usize = 0;
            let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3663_ = 0usize;
            v___x_3664_ = lean_usize_of_nat(v___x_3648_);
            v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3643_,
                v___f_3655_,
                v_buckets_3646_,
                v___x_3663_,
                v___x_3664_,
                v___x_3649_,
            );
            return v___x_3665_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_instForMProdOfMonad___redArg(
    mut v_inst_3666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3667_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3667_, 0, v_inst_3666_);
    return v___f_3667_;
}
pub unsafe fn l_Std_HashMap_Raw_instForMProdOfMonad(
    mut v_00_u03b1_3668_: *mut leanh::LeanObject,
    mut v_00_u03b2_3669_: *mut leanh::LeanObject,
    mut v_m_3670_: *mut leanh::LeanObject,
    mut v_inst_3671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3672_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3672_, 0, v_inst_3671_);
    return v___f_3672_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(
    mut v_f_3673_: *mut leanh::LeanObject,
    mut v_a_3674_: *mut leanh::LeanObject,
    mut v_b_3675_: *mut leanh::LeanObject,
    mut v_acc_3676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3677_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3677_, 0, v_a_3674_);
    leanh::lean_ctor_set(v___x_3677_, 1, v_b_3675_);
    v___x_3678_ = leanh::lean_apply_2(v_f_3673_, v___x_3677_, v_acc_3676_);
    return v___x_3678_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(
    mut v_inst_3679_: *mut leanh::LeanObject,
    mut v___f_3680_: *mut leanh::LeanObject,
    mut v_a_3681_: *mut leanh::LeanObject,
    mut v_x_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3684_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_inst_3679_, v___f_3680_, v_a_3681_, v___y_3683_);
    return v___x_3684_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(
    mut v_inst_3685_: *mut leanh::LeanObject,
    mut v_00_u03b2_3686_: *mut leanh::LeanObject,
    mut v_m_3687_: *mut leanh::LeanObject,
    mut v_init_3688_: *mut leanh::LeanObject,
    mut v_f_3689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3693_: usize = 0;
    let mut v___x_3694_: usize = 0;
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3690_ = leanh::lean_ctor_get(v_m_3687_, 1);
    leanh::lean_inc_ref(v_buckets_3690_);
    leanh::lean_dec_ref(v_m_3687_);
    v___f_3691_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3691_, 0, v_f_3689_);
    leanh::lean_inc_ref(v_inst_3685_);
    v___f_3692_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3692_, 0, v_inst_3685_);
    leanh::lean_closure_set(v___f_3692_, 1, v___f_3691_);
    v_sz_3693_ = lean_array_size(v_buckets_3690_);
    v___x_3694_ = 0usize;
    v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3685_,
        v_buckets_3690_,
        v___f_3692_,
        v_sz_3693_,
        v___x_3694_,
        v_init_3688_,
    );
    return v___x_3695_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad___redArg(
    mut v_inst_3696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3697_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3697_, 0, v_inst_3696_);
    return v___f_3697_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad(
    mut v_00_u03b1_3698_: *mut leanh::LeanObject,
    mut v_00_u03b2_3699_: *mut leanh::LeanObject,
    mut v_m_3700_: *mut leanh::LeanObject,
    mut v_inst_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3702_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3702_, 0, v_inst_3701_);
    return v___f_3702_;
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___lam__0(
    mut v_p_3703_: *mut leanh::LeanObject,
    mut v___x_3704_: *mut leanh::LeanObject,
    mut v___x_3705_: *mut leanh::LeanObject,
    mut v_a_3706_: *mut leanh::LeanObject,
    mut v_b_3707_: *mut leanh::LeanObject,
    mut v_acc_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    v___x_3709_ = leanh::lean_apply_2(v_p_3703_, v_a_3706_, v_b_3707_);
    v___x_3710_ = (leanh::lean_unbox(v___x_3709_) as u8);
    if v___x_3710_ == 0 {
        let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_3705_);
        v___x_3711_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3711_, 0, v___x_3709_);
        v___x_3712_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3712_, 0, v___x_3711_);
        leanh::lean_ctor_set(v___x_3712_, 1, v___x_3704_);
        v___x_3713_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3713_, 0, v___x_3712_);
        return v___x_3713_;
    } else {
        let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3714_, 0, v___x_3705_);
        return v___x_3714_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___lam__0___boxed(
    mut v_p_3715_: *mut leanh::LeanObject,
    mut v___x_3716_: *mut leanh::LeanObject,
    mut v___x_3717_: *mut leanh::LeanObject,
    mut v_a_3718_: *mut leanh::LeanObject,
    mut v_b_3719_: *mut leanh::LeanObject,
    mut v_acc_3720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3721_ = l_Std_HashMap_Raw_all___redArg___lam__0(
        v_p_3715_,
        v___x_3716_,
        v___x_3717_,
        v_a_3718_,
        v_b_3719_,
        v_acc_3720_,
    );
    leanh::lean_dec_ref(v_acc_3720_);
    return v_res_3721_;
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___lam__1(
    mut v___x_3722_: *mut leanh::LeanObject,
    mut v___f_3723_: *mut leanh::LeanObject,
    mut v_a_3724_: *mut leanh::LeanObject,
    mut v_x_3725_: *mut leanh::LeanObject,
    mut v___y_3726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3727_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3722_, v___f_3723_, v_a_3724_, v___y_3726_);
    return v___x_3727_;
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg(
    mut v_m_3731_: *mut leanh::LeanObject,
    mut v_p_3732_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3739_: usize = 0;
    let mut v___x_3740_: usize = 0;
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3733_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3734_ = leanh::lean_ctor_get(v_m_3731_, 1);
    leanh::lean_inc_ref(v_buckets_3734_);
    leanh::lean_dec_ref(v_m_3731_);
    v___x_3735_ = leanh::lean_box(0);
    v___x_3736_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3737_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3737_, 0, v_p_3732_);
    leanh::lean_closure_set(v___f_3737_, 1, v___x_3735_);
    leanh::lean_closure_set(v___f_3737_, 2, v___x_3736_);
    v___f_3738_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3738_, 0, v___x_3733_);
    leanh::lean_closure_set(v___f_3738_, 1, v___f_3737_);
    v_sz_3739_ = lean_array_size(v_buckets_3734_);
    v___x_3740_ = 0usize;
    v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3733_,
        v_buckets_3734_,
        v___f_3738_,
        v_sz_3739_,
        v___x_3740_,
        v___x_3736_,
    );
    v_fst_3742_ = leanh::lean_ctor_get(v___x_3741_, 0);
    leanh::lean_inc(v_fst_3742_);
    leanh::lean_dec(v___x_3741_);
    if leanh::lean_obj_tag(v_fst_3742_) == 0 {
        let mut v___x_3743_: u8 = 0;
        v___x_3743_ = 1;
        return v___x_3743_;
    } else {
        let mut v_val_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3745_: u8 = 0;
        v_val_3744_ = leanh::lean_ctor_get(v_fst_3742_, 0);
        leanh::lean_inc(v_val_3744_);
        leanh::lean_dec_ref_known(v_fst_3742_, 1);
        v___x_3745_ = (leanh::lean_unbox(v_val_3744_) as u8);
        leanh::lean_dec(v_val_3744_);
        return v___x_3745_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___boxed(
    mut v_m_3746_: *mut leanh::LeanObject,
    mut v_p_3747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3748_: u8 = 0;
    let mut v_r_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3748_ = l_Std_HashMap_Raw_all___redArg(v_m_3746_, v_p_3747_);
    v_r_3749_ = leanh::lean_box((v_res_3748_) as usize);
    return v_r_3749_;
}
pub unsafe fn l_Std_HashMap_Raw_all(
    mut v_00_u03b1_3750_: *mut leanh::LeanObject,
    mut v_00_u03b2_3751_: *mut leanh::LeanObject,
    mut v_m_3752_: *mut leanh::LeanObject,
    mut v_p_3753_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3760_: usize = 0;
    let mut v___x_3761_: usize = 0;
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3755_ = leanh::lean_ctor_get(v_m_3752_, 1);
    leanh::lean_inc_ref(v_buckets_3755_);
    leanh::lean_dec_ref(v_m_3752_);
    v___x_3756_ = leanh::lean_box(0);
    v___x_3757_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3758_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3758_, 0, v_p_3753_);
    leanh::lean_closure_set(v___f_3758_, 1, v___x_3756_);
    leanh::lean_closure_set(v___f_3758_, 2, v___x_3757_);
    v___f_3759_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3759_, 0, v___x_3754_);
    leanh::lean_closure_set(v___f_3759_, 1, v___f_3758_);
    v_sz_3760_ = lean_array_size(v_buckets_3755_);
    v___x_3761_ = 0usize;
    v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3754_,
        v_buckets_3755_,
        v___f_3759_,
        v_sz_3760_,
        v___x_3761_,
        v___x_3757_,
    );
    v_fst_3763_ = leanh::lean_ctor_get(v___x_3762_, 0);
    leanh::lean_inc(v_fst_3763_);
    leanh::lean_dec(v___x_3762_);
    if leanh::lean_obj_tag(v_fst_3763_) == 0 {
        let mut v___x_3764_: u8 = 0;
        v___x_3764_ = 1;
        return v___x_3764_;
    } else {
        let mut v_val_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3766_: u8 = 0;
        v_val_3765_ = leanh::lean_ctor_get(v_fst_3763_, 0);
        leanh::lean_inc(v_val_3765_);
        leanh::lean_dec_ref_known(v_fst_3763_, 1);
        v___x_3766_ = (leanh::lean_unbox(v_val_3765_) as u8);
        leanh::lean_dec(v_val_3765_);
        return v___x_3766_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_all___boxed(
    mut v_00_u03b1_3767_: *mut leanh::LeanObject,
    mut v_00_u03b2_3768_: *mut leanh::LeanObject,
    mut v_m_3769_: *mut leanh::LeanObject,
    mut v_p_3770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3771_: u8 = 0;
    let mut v_r_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l_Std_HashMap_Raw_all(v_00_u03b1_3767_, v_00_u03b2_3768_, v_m_3769_, v_p_3770_);
    v_r_3772_ = leanh::lean_box((v_res_3771_) as usize);
    return v_r_3772_;
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg___lam__0(
    mut v_p_3773_: *mut leanh::LeanObject,
    mut v___x_3774_: *mut leanh::LeanObject,
    mut v___x_3775_: *mut leanh::LeanObject,
    mut v_a_3776_: *mut leanh::LeanObject,
    mut v_b_3777_: *mut leanh::LeanObject,
    mut v_acc_3778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: u8 = 0;
    v___x_3779_ = leanh::lean_apply_2(v_p_3773_, v_a_3776_, v_b_3777_);
    v___x_3780_ = (leanh::lean_unbox(v___x_3779_) as u8);
    if v___x_3780_ == 0 {
        let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3781_, 0, v___x_3774_);
        return v___x_3781_;
    } else {
        let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_3774_);
        v___x_3782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3782_, 0, v___x_3779_);
        v___x_3783_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3783_, 0, v___x_3782_);
        leanh::lean_ctor_set(v___x_3783_, 1, v___x_3775_);
        v___x_3784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3784_, 0, v___x_3783_);
        return v___x_3784_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg___lam__0___boxed(
    mut v_p_3785_: *mut leanh::LeanObject,
    mut v___x_3786_: *mut leanh::LeanObject,
    mut v___x_3787_: *mut leanh::LeanObject,
    mut v_a_3788_: *mut leanh::LeanObject,
    mut v_b_3789_: *mut leanh::LeanObject,
    mut v_acc_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Std_HashMap_Raw_any___redArg___lam__0(
        v_p_3785_,
        v___x_3786_,
        v___x_3787_,
        v_a_3788_,
        v_b_3789_,
        v_acc_3790_,
    );
    leanh::lean_dec_ref(v_acc_3790_);
    return v_res_3791_;
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg(
    mut v_m_3792_: *mut leanh::LeanObject,
    mut v_p_3793_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3800_: usize = 0;
    let mut v___x_3801_: usize = 0;
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3795_ = leanh::lean_ctor_get(v_m_3792_, 1);
    leanh::lean_inc_ref(v_buckets_3795_);
    leanh::lean_dec_ref(v_m_3792_);
    v___x_3796_ = leanh::lean_box(0);
    v___x_3797_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3798_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3798_, 0, v_p_3793_);
    leanh::lean_closure_set(v___f_3798_, 1, v___x_3797_);
    leanh::lean_closure_set(v___f_3798_, 2, v___x_3796_);
    v___f_3799_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3799_, 0, v___x_3794_);
    leanh::lean_closure_set(v___f_3799_, 1, v___f_3798_);
    v_sz_3800_ = lean_array_size(v_buckets_3795_);
    v___x_3801_ = 0usize;
    v___x_3802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3794_,
        v_buckets_3795_,
        v___f_3799_,
        v_sz_3800_,
        v___x_3801_,
        v___x_3797_,
    );
    v_fst_3803_ = leanh::lean_ctor_get(v___x_3802_, 0);
    leanh::lean_inc(v_fst_3803_);
    leanh::lean_dec(v___x_3802_);
    if leanh::lean_obj_tag(v_fst_3803_) == 0 {
        let mut v___x_3804_: u8 = 0;
        v___x_3804_ = 0;
        return v___x_3804_;
    } else {
        let mut v_val_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3806_: u8 = 0;
        v_val_3805_ = leanh::lean_ctor_get(v_fst_3803_, 0);
        leanh::lean_inc(v_val_3805_);
        leanh::lean_dec_ref_known(v_fst_3803_, 1);
        v___x_3806_ = (leanh::lean_unbox(v_val_3805_) as u8);
        leanh::lean_dec(v_val_3805_);
        return v___x_3806_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg___boxed(
    mut v_m_3807_: *mut leanh::LeanObject,
    mut v_p_3808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3809_: u8 = 0;
    let mut v_r_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3809_ = l_Std_HashMap_Raw_any___redArg(v_m_3807_, v_p_3808_);
    v_r_3810_ = leanh::lean_box((v_res_3809_) as usize);
    return v_r_3810_;
}
pub unsafe fn l_Std_HashMap_Raw_any(
    mut v_00_u03b1_3811_: *mut leanh::LeanObject,
    mut v_00_u03b2_3812_: *mut leanh::LeanObject,
    mut v_m_3813_: *mut leanh::LeanObject,
    mut v_p_3814_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3821_: usize = 0;
    let mut v___x_3822_: usize = 0;
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3815_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3816_ = leanh::lean_ctor_get(v_m_3813_, 1);
    leanh::lean_inc_ref(v_buckets_3816_);
    leanh::lean_dec_ref(v_m_3813_);
    v___x_3817_ = leanh::lean_box(0);
    v___x_3818_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3819_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3819_, 0, v_p_3814_);
    leanh::lean_closure_set(v___f_3819_, 1, v___x_3818_);
    leanh::lean_closure_set(v___f_3819_, 2, v___x_3817_);
    v___f_3820_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3820_, 0, v___x_3815_);
    leanh::lean_closure_set(v___f_3820_, 1, v___f_3819_);
    v_sz_3821_ = lean_array_size(v_buckets_3816_);
    v___x_3822_ = 0usize;
    v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3815_,
        v_buckets_3816_,
        v___f_3820_,
        v_sz_3821_,
        v___x_3822_,
        v___x_3818_,
    );
    v_fst_3824_ = leanh::lean_ctor_get(v___x_3823_, 0);
    leanh::lean_inc(v_fst_3824_);
    leanh::lean_dec(v___x_3823_);
    if leanh::lean_obj_tag(v_fst_3824_) == 0 {
        let mut v___x_3825_: u8 = 0;
        v___x_3825_ = 0;
        return v___x_3825_;
    } else {
        let mut v_val_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3827_: u8 = 0;
        v_val_3826_ = leanh::lean_ctor_get(v_fst_3824_, 0);
        leanh::lean_inc(v_val_3826_);
        leanh::lean_dec_ref_known(v_fst_3824_, 1);
        v___x_3827_ = (leanh::lean_unbox(v_val_3826_) as u8);
        leanh::lean_dec(v_val_3826_);
        return v___x_3827_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_any___boxed(
    mut v_00_u03b1_3828_: *mut leanh::LeanObject,
    mut v_00_u03b2_3829_: *mut leanh::LeanObject,
    mut v_m_3830_: *mut leanh::LeanObject,
    mut v_p_3831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3832_: u8 = 0;
    let mut v_r_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3832_ = l_Std_HashMap_Raw_any(v_00_u03b1_3828_, v_00_u03b2_3829_, v_m_3830_, v_p_3831_);
    v_r_3833_ = leanh::lean_box((v_res_3832_) as usize);
    return v_r_3833_;
}
pub unsafe fn l_Std_HashMap_Raw_union___redArg___lam__0(
    mut v_inst_3834_: *mut leanh::LeanObject,
    mut v_inst_3835_: *mut leanh::LeanObject,
    mut v_a_3836_: *mut leanh::LeanObject,
    mut v_b_3837_: *mut leanh::LeanObject,
    mut v_acc_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_3839_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_3834_,
        v_inst_3835_,
        v_acc_3838_,
        v_a_3836_,
        v_b_3837_,
    );
    v___x_3840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3840_, 0, v_r_3839_);
    return v___x_3840_;
}
pub unsafe fn l_Std_HashMap_Raw_union___redArg___lam__1(
    mut v___x_3841_: *mut leanh::LeanObject,
    mut v___f_3842_: *mut leanh::LeanObject,
    mut v_a_3843_: *mut leanh::LeanObject,
    mut v_x_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3846_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3841_, v___f_3842_, v_a_3843_, v___y_3845_);
    return v___x_3846_;
}
pub unsafe fn l_Std_HashMap_Raw_union___redArg(
    mut v_inst_3849_: *mut leanh::LeanObject,
    mut v_inst_3850_: *mut leanh::LeanObject,
    mut v_m_u2081_3851_: *mut leanh::LeanObject,
    mut v_m_u2082_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: u8 = 0;
    v_size_3853_ = leanh::lean_ctor_get(v_m_u2081_3851_, 0);
    v_buckets_3854_ = leanh::lean_ctor_get(v_m_u2081_3851_, 1);
    v___x_3855_ = leanh::lean_unsigned_to_nat(0);
    v___x_3856_ = lean_array_get_size(v_buckets_3854_);
    v___x_3857_ = lean_nat_dec_lt(v___x_3855_, v___x_3856_);
    if v___x_3857_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_3851_);
        leanh::lean_dec_ref(v_inst_3850_);
        leanh::lean_dec_ref(v_inst_3849_);
        return v_m_u2082_3852_;
    } else {
        let mut v_size_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3861_: u8 = 0;
        v_size_3858_ = leanh::lean_ctor_get(v_m_u2082_3852_, 0);
        v_buckets_3859_ = leanh::lean_ctor_get(v_m_u2082_3852_, 1);
        v___x_3860_ = lean_array_get_size(v_buckets_3859_);
        v___x_3861_ = lean_nat_dec_lt(v___x_3855_, v___x_3860_);
        if v___x_3861_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_3852_);
            leanh::lean_dec_ref(v_inst_3850_);
            leanh::lean_dec_ref(v_inst_3849_);
            return v_m_u2081_3851_;
        } else {
            let mut v___x_3862_: u8 = 0;
            v___x_3862_ = lean_nat_dec_le(v_size_3853_, v_size_3858_);
            if v___x_3862_ == 0 {
                let mut v___f_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___f_3863_ = l_Std_HashMap_Raw_union___redArg___closed__0;
                v___x_3864_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
                    v___f_3863_,
                    v_inst_3849_,
                    v_inst_3850_,
                    v_m_u2081_3851_,
                    v_m_u2082_3852_,
                );
                return v___x_3864_;
            } else {
                let mut v___f_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_3868_: usize = 0;
                let mut v___x_3869_: usize = 0;
                let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_buckets_3854_);
                leanh::lean_dec_ref(v_m_u2081_3851_);
                v___f_3865_ = leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_3865_, 0, v_inst_3849_);
                leanh::lean_closure_set(v___f_3865_, 1, v_inst_3850_);
                v___x_3866_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
                v___f_3867_ = leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_3867_, 0, v___x_3866_);
                leanh::lean_closure_set(v___f_3867_, 1, v___f_3865_);
                v_sz_3868_ = lean_array_size(v_buckets_3854_);
                v___x_3869_ = 0usize;
                v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3866_,
                    v_buckets_3854_,
                    v___f_3867_,
                    v_sz_3868_,
                    v___x_3869_,
                    v_m_u2082_3852_,
                );
                return v___x_3870_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_union(
    mut v_00_u03b1_3871_: *mut leanh::LeanObject,
    mut v_00_u03b2_3872_: *mut leanh::LeanObject,
    mut v_inst_3873_: *mut leanh::LeanObject,
    mut v_inst_3874_: *mut leanh::LeanObject,
    mut v_m_u2081_3875_: *mut leanh::LeanObject,
    mut v_m_u2082_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    v_size_3877_ = leanh::lean_ctor_get(v_m_u2081_3875_, 0);
    v_buckets_3878_ = leanh::lean_ctor_get(v_m_u2081_3875_, 1);
    v___x_3879_ = leanh::lean_unsigned_to_nat(0);
    v___x_3880_ = lean_array_get_size(v_buckets_3878_);
    v___x_3881_ = lean_nat_dec_lt(v___x_3879_, v___x_3880_);
    if v___x_3881_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_3875_);
        leanh::lean_dec_ref(v_inst_3874_);
        leanh::lean_dec_ref(v_inst_3873_);
        return v_m_u2082_3876_;
    } else {
        let mut v_size_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3885_: u8 = 0;
        v_size_3882_ = leanh::lean_ctor_get(v_m_u2082_3876_, 0);
        v_buckets_3883_ = leanh::lean_ctor_get(v_m_u2082_3876_, 1);
        v___x_3884_ = lean_array_get_size(v_buckets_3883_);
        v___x_3885_ = lean_nat_dec_lt(v___x_3879_, v___x_3884_);
        if v___x_3885_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_3876_);
            leanh::lean_dec_ref(v_inst_3874_);
            leanh::lean_dec_ref(v_inst_3873_);
            return v_m_u2081_3875_;
        } else {
            let mut v___x_3886_: u8 = 0;
            v___x_3886_ = lean_nat_dec_le(v_size_3877_, v_size_3882_);
            if v___x_3886_ == 0 {
                let mut v___f_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___f_3887_ = l_Std_HashMap_Raw_union___redArg___closed__0;
                v___x_3888_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
                    v___f_3887_,
                    v_inst_3873_,
                    v_inst_3874_,
                    v_m_u2081_3875_,
                    v_m_u2082_3876_,
                );
                return v___x_3888_;
            } else {
                let mut v___f_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_3892_: usize = 0;
                let mut v___x_3893_: usize = 0;
                let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_buckets_3878_);
                leanh::lean_dec_ref(v_m_u2081_3875_);
                v___f_3889_ = leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_3889_, 0, v_inst_3873_);
                leanh::lean_closure_set(v___f_3889_, 1, v_inst_3874_);
                v___x_3890_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
                v___f_3891_ = leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_3891_, 0, v___x_3890_);
                leanh::lean_closure_set(v___f_3891_, 1, v___f_3889_);
                v_sz_3892_ = lean_array_size(v_buckets_3878_);
                v___x_3893_ = 0usize;
                v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3890_,
                    v_buckets_3878_,
                    v___f_3891_,
                    v_sz_3892_,
                    v___x_3893_,
                    v_m_u2082_3876_,
                );
                return v___x_3894_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_inter___redArg(
    mut v_inst_3895_: *mut leanh::LeanObject,
    mut v_inst_3896_: *mut leanh::LeanObject,
    mut v_m_u2081_3897_: *mut leanh::LeanObject,
    mut v_m_u2082_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    v_buckets_3899_ = leanh::lean_ctor_get(v_m_u2081_3897_, 1);
    v___x_3900_ = leanh::lean_unsigned_to_nat(0);
    v___x_3901_ = lean_array_get_size(v_buckets_3899_);
    v___x_3902_ = lean_nat_dec_lt(v___x_3900_, v___x_3901_);
    if v___x_3902_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_3897_);
        leanh::lean_dec_ref(v_inst_3896_);
        leanh::lean_dec_ref(v_inst_3895_);
        return v_m_u2082_3898_;
    } else {
        let mut v_buckets_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3905_: u8 = 0;
        v_buckets_3903_ = leanh::lean_ctor_get(v_m_u2082_3898_, 1);
        v___x_3904_ = lean_array_get_size(v_buckets_3903_);
        v___x_3905_ = lean_nat_dec_lt(v___x_3900_, v___x_3904_);
        if v___x_3905_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_3898_);
            leanh::lean_dec_ref(v_inst_3896_);
            leanh::lean_dec_ref(v_inst_3895_);
            return v_m_u2081_3897_;
        } else {
            let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3906_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
                v_inst_3895_,
                v_inst_3896_,
                v_m_u2081_3897_,
                v_m_u2082_3898_,
            );
            return v___x_3906_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_inter(
    mut v_00_u03b1_3907_: *mut leanh::LeanObject,
    mut v_00_u03b2_3908_: *mut leanh::LeanObject,
    mut v_inst_3909_: *mut leanh::LeanObject,
    mut v_inst_3910_: *mut leanh::LeanObject,
    mut v_m_u2081_3911_: *mut leanh::LeanObject,
    mut v_m_u2082_3912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    v_buckets_3913_ = leanh::lean_ctor_get(v_m_u2081_3911_, 1);
    v___x_3914_ = leanh::lean_unsigned_to_nat(0);
    v___x_3915_ = lean_array_get_size(v_buckets_3913_);
    v___x_3916_ = lean_nat_dec_lt(v___x_3914_, v___x_3915_);
    if v___x_3916_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_3911_);
        leanh::lean_dec_ref(v_inst_3910_);
        leanh::lean_dec_ref(v_inst_3909_);
        return v_m_u2082_3912_;
    } else {
        let mut v_buckets_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3919_: u8 = 0;
        v_buckets_3917_ = leanh::lean_ctor_get(v_m_u2082_3912_, 1);
        v___x_3918_ = lean_array_get_size(v_buckets_3917_);
        v___x_3919_ = lean_nat_dec_lt(v___x_3914_, v___x_3918_);
        if v___x_3919_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_3912_);
            leanh::lean_dec_ref(v_inst_3910_);
            leanh::lean_dec_ref(v_inst_3909_);
            return v_m_u2081_3911_;
        } else {
            let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3920_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
                v_inst_3909_,
                v_inst_3910_,
                v_m_u2081_3911_,
                v_m_u2082_3912_,
            );
            return v___x_3920_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_diff___redArg___lam__0(
    mut v_inst_3921_: *mut leanh::LeanObject,
    mut v_inst_3922_: *mut leanh::LeanObject,
    mut v_m_u2082_3923_: *mut leanh::LeanObject,
    mut v___x_3924_: u8,
    mut v_k_3925_: *mut leanh::LeanObject,
    mut v_x_3926_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3927_: u8 = 0;
    v___x_3927_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_3921_,
        v_inst_3922_,
        v_m_u2082_3923_,
        v_k_3925_,
    );
    if v___x_3927_ == 0 {
        return v___x_3924_;
    } else {
        let mut v___x_3928_: u8 = 0;
        v___x_3928_ = 0;
        return v___x_3928_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(
    mut v_inst_3929_: *mut leanh::LeanObject,
    mut v_inst_3930_: *mut leanh::LeanObject,
    mut v_m_u2082_3931_: *mut leanh::LeanObject,
    mut v___x_3932_: *mut leanh::LeanObject,
    mut v_k_3933_: *mut leanh::LeanObject,
    mut v_x_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_91__boxed_3935_: u8 = 0;
    let mut v_res_3936_: u8 = 0;
    let mut v_r_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_91__boxed_3935_ = (leanh::lean_unbox(v___x_3932_) as u8);
    v_res_3936_ = l_Std_HashMap_Raw_diff___redArg___lam__0(
        v_inst_3929_,
        v_inst_3930_,
        v_m_u2082_3931_,
        v___x_91__boxed_3935_,
        v_k_3933_,
        v_x_3934_,
    );
    leanh::lean_dec(v_x_3934_);
    leanh::lean_dec_ref(v_m_u2082_3931_);
    v_r_3937_ = leanh::lean_box((v_res_3936_) as usize);
    return v_r_3937_;
}
pub unsafe fn l_Std_HashMap_Raw_diff___redArg(
    mut v_inst_3938_: *mut leanh::LeanObject,
    mut v_inst_3939_: *mut leanh::LeanObject,
    mut v_m_u2081_3940_: *mut leanh::LeanObject,
    mut v_m_u2082_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: u8 = 0;
    v_size_3942_ = leanh::lean_ctor_get(v_m_u2081_3940_, 0);
    v_buckets_3943_ = leanh::lean_ctor_get(v_m_u2081_3940_, 1);
    v___x_3944_ = leanh::lean_unsigned_to_nat(0);
    v___x_3945_ = lean_array_get_size(v_buckets_3943_);
    v___x_3946_ = lean_nat_dec_lt(v___x_3944_, v___x_3945_);
    if v___x_3946_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_3940_);
        leanh::lean_dec_ref(v_inst_3939_);
        leanh::lean_dec_ref(v_inst_3938_);
        return v_m_u2082_3941_;
    } else {
        let mut v_size_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3950_: u8 = 0;
        v_size_3947_ = leanh::lean_ctor_get(v_m_u2082_3941_, 0);
        v_buckets_3948_ = leanh::lean_ctor_get(v_m_u2082_3941_, 1);
        v___x_3949_ = lean_array_get_size(v_buckets_3948_);
        v___x_3950_ = lean_nat_dec_lt(v___x_3944_, v___x_3949_);
        if v___x_3950_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_3941_);
            leanh::lean_dec_ref(v_inst_3939_);
            leanh::lean_dec_ref(v_inst_3938_);
            return v_m_u2081_3940_;
        } else {
            let mut v___x_3951_: u8 = 0;
            v___x_3951_ = lean_nat_dec_le(v_size_3942_, v_size_3947_);
            if v___x_3951_ == 0 {
                let mut v___f_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___f_3952_ = l_Std_HashMap_Raw_union___redArg___closed__0;
                v___x_3953_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
                    v___f_3952_,
                    v_inst_3938_,
                    v_inst_3939_,
                    v_m_u2081_3940_,
                    v_m_u2082_3941_,
                );
                return v___x_3953_;
            } else {
                let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3954_ = leanh::lean_box((v___x_3951_) as usize);
                v___f_3955_ = leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_3955_, 0, v_inst_3938_);
                leanh::lean_closure_set(v___f_3955_, 1, v_inst_3939_);
                leanh::lean_closure_set(v___f_3955_, 2, v_m_u2082_3941_);
                leanh::lean_closure_set(v___f_3955_, 3, v___x_3954_);
                v___x_3956_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3955_, v_m_u2081_3940_);
                return v___x_3956_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_diff(
    mut v_00_u03b1_3957_: *mut leanh::LeanObject,
    mut v_00_u03b2_3958_: *mut leanh::LeanObject,
    mut v_inst_3959_: *mut leanh::LeanObject,
    mut v_inst_3960_: *mut leanh::LeanObject,
    mut v_m_u2081_3961_: *mut leanh::LeanObject,
    mut v_m_u2082_3962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    v_size_3963_ = leanh::lean_ctor_get(v_m_u2081_3961_, 0);
    v_buckets_3964_ = leanh::lean_ctor_get(v_m_u2081_3961_, 1);
    v___x_3965_ = leanh::lean_unsigned_to_nat(0);
    v___x_3966_ = lean_array_get_size(v_buckets_3964_);
    v___x_3967_ = lean_nat_dec_lt(v___x_3965_, v___x_3966_);
    if v___x_3967_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_3961_);
        leanh::lean_dec_ref(v_inst_3960_);
        leanh::lean_dec_ref(v_inst_3959_);
        return v_m_u2082_3962_;
    } else {
        let mut v_size_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3971_: u8 = 0;
        v_size_3968_ = leanh::lean_ctor_get(v_m_u2082_3962_, 0);
        v_buckets_3969_ = leanh::lean_ctor_get(v_m_u2082_3962_, 1);
        v___x_3970_ = lean_array_get_size(v_buckets_3969_);
        v___x_3971_ = lean_nat_dec_lt(v___x_3965_, v___x_3970_);
        if v___x_3971_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_3962_);
            leanh::lean_dec_ref(v_inst_3960_);
            leanh::lean_dec_ref(v_inst_3959_);
            return v_m_u2081_3961_;
        } else {
            let mut v___x_3972_: u8 = 0;
            v___x_3972_ = lean_nat_dec_le(v_size_3963_, v_size_3968_);
            if v___x_3972_ == 0 {
                let mut v___f_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___f_3973_ = l_Std_HashMap_Raw_union___redArg___closed__0;
                v___x_3974_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
                    v___f_3973_,
                    v_inst_3959_,
                    v_inst_3960_,
                    v_m_u2081_3961_,
                    v_m_u2082_3962_,
                );
                return v___x_3974_;
            } else {
                let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3975_ = leanh::lean_box((v___x_3972_) as usize);
                v___f_3976_ = leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_3976_, 0, v_inst_3959_);
                leanh::lean_closure_set(v___f_3976_, 1, v_inst_3960_);
                leanh::lean_closure_set(v___f_3976_, 2, v_m_u2082_3962_);
                leanh::lean_closure_set(v___f_3976_, 3, v___x_3975_);
                v___x_3977_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3976_, v_m_u2081_3961_);
                return v___x_3977_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(
    mut v_inst_3978_: *mut leanh::LeanObject,
    mut v_inst_3979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3980_ =
        leanh::lean_alloc_closure(l_Std_HashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_3980_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3980_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3980_, 2, v_inst_3978_);
    leanh::lean_closure_set(v___x_3980_, 3, v_inst_3979_);
    return v___x_3980_;
}
pub unsafe fn l_Std_HashMap_Raw_instUnionOfBEqOfHashable(
    mut v_00_u03b1_3981_: *mut leanh::LeanObject,
    mut v_00_u03b2_3982_: *mut leanh::LeanObject,
    mut v_inst_3983_: *mut leanh::LeanObject,
    mut v_inst_3984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3985_ =
        leanh::lean_alloc_closure(l_Std_HashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_3985_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3985_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3985_, 2, v_inst_3983_);
    leanh::lean_closure_set(v___x_3985_, 3, v_inst_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(
    mut v_inst_3986_: *mut leanh::LeanObject,
    mut v_inst_3987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ =
        leanh::lean_alloc_closure(l_Std_HashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_3988_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3988_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3988_, 2, v_inst_3986_);
    leanh::lean_closure_set(v___x_3988_, 3, v_inst_3987_);
    return v___x_3988_;
}
pub unsafe fn l_Std_HashMap_Raw_instInterOfBEqOfHashable(
    mut v_00_u03b1_3989_: *mut leanh::LeanObject,
    mut v_00_u03b2_3990_: *mut leanh::LeanObject,
    mut v_inst_3991_: *mut leanh::LeanObject,
    mut v_inst_3992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3993_ =
        leanh::lean_alloc_closure(l_Std_HashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_3993_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3993_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3993_, 2, v_inst_3991_);
    leanh::lean_closure_set(v___x_3993_, 3, v_inst_3992_);
    return v___x_3993_;
}
pub unsafe fn l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(
    mut v_inst_3994_: *mut leanh::LeanObject,
    mut v_inst_3995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ =
        leanh::lean_alloc_closure(l_Std_HashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_3996_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3996_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3996_, 2, v_inst_3994_);
    leanh::lean_closure_set(v___x_3996_, 3, v_inst_3995_);
    return v___x_3996_;
}
pub unsafe fn l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(
    mut v_00_u03b1_3997_: *mut leanh::LeanObject,
    mut v_00_u03b2_3998_: *mut leanh::LeanObject,
    mut v_inst_3999_: *mut leanh::LeanObject,
    mut v_inst_4000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4001_ =
        leanh::lean_alloc_closure(l_Std_HashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4001_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4001_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4001_, 2, v_inst_3999_);
    leanh::lean_closure_set(v___x_4001_, 3, v_inst_4000_);
    return v___x_4001_;
}
pub unsafe fn l_Std_HashMap_Raw_beq___redArg(
    mut v_inst_4002_: *mut leanh::LeanObject,
    mut v_inst_4003_: *mut leanh::LeanObject,
    mut v_inst_4004_: *mut leanh::LeanObject,
    mut v_m_u2081_4005_: *mut leanh::LeanObject,
    mut v_m_u2082_4006_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4007_: u8 = 0;
    v___x_4007_ = l_Std_DHashMap_Raw_Const_beq___redArg(
        v_inst_4002_,
        v_inst_4003_,
        v_inst_4004_,
        v_m_u2081_4005_,
        v_m_u2082_4006_,
    );
    return v___x_4007_;
}
pub unsafe fn l_Std_HashMap_Raw_beq___redArg___boxed(
    mut v_inst_4008_: *mut leanh::LeanObject,
    mut v_inst_4009_: *mut leanh::LeanObject,
    mut v_inst_4010_: *mut leanh::LeanObject,
    mut v_m_u2081_4011_: *mut leanh::LeanObject,
    mut v_m_u2082_4012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4013_: u8 = 0;
    let mut v_r_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4013_ = l_Std_HashMap_Raw_beq___redArg(
        v_inst_4008_,
        v_inst_4009_,
        v_inst_4010_,
        v_m_u2081_4011_,
        v_m_u2082_4012_,
    );
    v_r_4014_ = leanh::lean_box((v_res_4013_) as usize);
    return v_r_4014_;
}
pub unsafe fn l_Std_HashMap_Raw_beq(
    mut v_00_u03b1_4015_: *mut leanh::LeanObject,
    mut v_00_u03b2_4016_: *mut leanh::LeanObject,
    mut v_inst_4017_: *mut leanh::LeanObject,
    mut v_inst_4018_: *mut leanh::LeanObject,
    mut v_inst_4019_: *mut leanh::LeanObject,
    mut v_m_u2081_4020_: *mut leanh::LeanObject,
    mut v_m_u2082_4021_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4022_: u8 = 0;
    v___x_4022_ = l_Std_DHashMap_Raw_Const_beq___redArg(
        v_inst_4017_,
        v_inst_4018_,
        v_inst_4019_,
        v_m_u2081_4020_,
        v_m_u2082_4021_,
    );
    return v___x_4022_;
}
pub unsafe fn l_Std_HashMap_Raw_beq___boxed(
    mut v_00_u03b1_4023_: *mut leanh::LeanObject,
    mut v_00_u03b2_4024_: *mut leanh::LeanObject,
    mut v_inst_4025_: *mut leanh::LeanObject,
    mut v_inst_4026_: *mut leanh::LeanObject,
    mut v_inst_4027_: *mut leanh::LeanObject,
    mut v_m_u2081_4028_: *mut leanh::LeanObject,
    mut v_m_u2082_4029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4030_: u8 = 0;
    let mut v_r_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4030_ = l_Std_HashMap_Raw_beq(
        v_00_u03b1_4023_,
        v_00_u03b2_4024_,
        v_inst_4025_,
        v_inst_4026_,
        v_inst_4027_,
        v_m_u2081_4028_,
        v_m_u2082_4029_,
    );
    v_r_4031_ = leanh::lean_box((v_res_4030_) as usize);
    return v_r_4031_;
}
pub unsafe fn l_Std_HashMap_Raw_instBEqOfHashable___redArg(
    mut v_inst_4032_: *mut leanh::LeanObject,
    mut v_inst_4033_: *mut leanh::LeanObject,
    mut v_inst_4034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___x_4035_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4035_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4035_, 2, v_inst_4032_);
    leanh::lean_closure_set(v___x_4035_, 3, v_inst_4033_);
    leanh::lean_closure_set(v___x_4035_, 4, v_inst_4034_);
    return v___x_4035_;
}
pub unsafe fn l_Std_HashMap_Raw_instBEqOfHashable(
    mut v_00_u03b1_4036_: *mut leanh::LeanObject,
    mut v_00_u03b2_4037_: *mut leanh::LeanObject,
    mut v_inst_4038_: *mut leanh::LeanObject,
    mut v_inst_4039_: *mut leanh::LeanObject,
    mut v_inst_4040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___x_4041_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4041_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4041_, 2, v_inst_4038_);
    leanh::lean_closure_set(v___x_4041_, 3, v_inst_4039_);
    leanh::lean_closure_set(v___x_4041_, 4, v_inst_4040_);
    return v___x_4041_;
}
pub unsafe fn l_Std_HashMap_Raw_filterMap___redArg(
    mut v_f_4042_: *mut leanh::LeanObject,
    mut v_m_4043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    v_buckets_4044_ = leanh::lean_ctor_get(v_m_4043_, 1);
    v___x_4045_ = leanh::lean_unsigned_to_nat(0);
    v___x_4046_ = lean_array_get_size(v_buckets_4044_);
    v___x_4047_ = lean_nat_dec_lt(v___x_4045_, v___x_4046_);
    if v___x_4047_ == 0 {
        let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4043_);
        leanh::lean_dec_ref(v_f_4042_);
        v___x_4048_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4048_;
    } else {
        let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4049_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4042_, v_m_4043_);
        return v___x_4049_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_filterMap(
    mut v_00_u03b1_4050_: *mut leanh::LeanObject,
    mut v_00_u03b2_4051_: *mut leanh::LeanObject,
    mut v_00_u03b3_4052_: *mut leanh::LeanObject,
    mut v_f_4053_: *mut leanh::LeanObject,
    mut v_m_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u8 = 0;
    v_buckets_4055_ = leanh::lean_ctor_get(v_m_4054_, 1);
    v___x_4056_ = leanh::lean_unsigned_to_nat(0);
    v___x_4057_ = lean_array_get_size(v_buckets_4055_);
    v___x_4058_ = lean_nat_dec_lt(v___x_4056_, v___x_4057_);
    if v___x_4058_ == 0 {
        let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4054_);
        leanh::lean_dec_ref(v_f_4053_);
        v___x_4059_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4059_;
    } else {
        let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4060_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4053_, v_m_4054_);
        return v___x_4060_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_map___redArg(
    mut v_f_4061_: *mut leanh::LeanObject,
    mut v_m_4062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    v_buckets_4063_ = leanh::lean_ctor_get(v_m_4062_, 1);
    v___x_4064_ = leanh::lean_unsigned_to_nat(0);
    v___x_4065_ = lean_array_get_size(v_buckets_4063_);
    v___x_4066_ = lean_nat_dec_lt(v___x_4064_, v___x_4065_);
    if v___x_4066_ == 0 {
        let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4062_);
        leanh::lean_dec(v_f_4061_);
        v___x_4067_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4067_;
    } else {
        let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4068_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4061_, v_m_4062_);
        return v___x_4068_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_map(
    mut v_00_u03b1_4069_: *mut leanh::LeanObject,
    mut v_00_u03b2_4070_: *mut leanh::LeanObject,
    mut v_00_u03b3_4071_: *mut leanh::LeanObject,
    mut v_f_4072_: *mut leanh::LeanObject,
    mut v_m_4073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    v_buckets_4074_ = leanh::lean_ctor_get(v_m_4073_, 1);
    v___x_4075_ = leanh::lean_unsigned_to_nat(0);
    v___x_4076_ = lean_array_get_size(v_buckets_4074_);
    v___x_4077_ = lean_nat_dec_lt(v___x_4075_, v___x_4076_);
    if v___x_4077_ == 0 {
        let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4073_);
        leanh::lean_dec(v_f_4072_);
        v___x_4078_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4078_;
    } else {
        let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4079_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4072_, v_m_4073_);
        return v___x_4079_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_filter___redArg(
    mut v_f_4080_: *mut leanh::LeanObject,
    mut v_m_4081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    v_buckets_4082_ = leanh::lean_ctor_get(v_m_4081_, 1);
    v___x_4083_ = leanh::lean_unsigned_to_nat(0);
    v___x_4084_ = lean_array_get_size(v_buckets_4082_);
    v___x_4085_ = lean_nat_dec_lt(v___x_4083_, v___x_4084_);
    if v___x_4085_ == 0 {
        let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4081_);
        leanh::lean_dec_ref(v_f_4080_);
        v___x_4086_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4086_;
    } else {
        let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4087_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4080_, v_m_4081_);
        return v___x_4087_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_filter(
    mut v_00_u03b1_4088_: *mut leanh::LeanObject,
    mut v_00_u03b2_4089_: *mut leanh::LeanObject,
    mut v_f_4090_: *mut leanh::LeanObject,
    mut v_m_4091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    v_buckets_4092_ = leanh::lean_ctor_get(v_m_4091_, 1);
    v___x_4093_ = leanh::lean_unsigned_to_nat(0);
    v___x_4094_ = lean_array_get_size(v_buckets_4092_);
    v___x_4095_ = lean_nat_dec_lt(v___x_4093_, v___x_4094_);
    if v___x_4095_ == 0 {
        let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4091_);
        leanh::lean_dec_ref(v_f_4090_);
        v___x_4096_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4096_;
    } else {
        let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4097_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4090_, v_m_4091_);
        return v___x_4097_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_toArray___redArg___lam__0(
    mut v_x1_4098_: *mut leanh::LeanObject,
    mut v_x2_4099_: *mut leanh::LeanObject,
    mut v_x3_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4101_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4101_, 0, v_x2_4099_);
    leanh::lean_ctor_set(v___x_4101_, 1, v_x3_4100_);
    v___x_4102_ = lean_array_push(v_x1_4098_, v___x_4101_);
    return v___x_4102_;
}
pub unsafe fn l_Std_HashMap_Raw_toArray___redArg___lam__1(
    mut v___x_4103_: *mut leanh::LeanObject,
    mut v___f_4104_: *mut leanh::LeanObject,
    mut v_acc_4105_: *mut leanh::LeanObject,
    mut v_l_4106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4103_,
        v___f_4104_,
        v_acc_4105_,
        v_l_4106_,
    );
    return v___x_4107_;
}
pub unsafe fn l_Std_HashMap_Raw_toArray___redArg(
    mut v_m_4112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    v_size_4113_ = leanh::lean_ctor_get(v_m_4112_, 0);
    leanh::lean_inc(v_size_4113_);
    v_buckets_4114_ = leanh::lean_ctor_get(v_m_4112_, 1);
    leanh::lean_inc_ref(v_buckets_4114_);
    leanh::lean_dec_ref(v_m_4112_);
    v___x_4115_ = lean_mk_empty_array_with_capacity(v_size_4113_);
    leanh::lean_dec(v_size_4113_);
    v___x_4116_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4117_ = leanh::lean_unsigned_to_nat(0);
    v___x_4118_ = lean_array_get_size(v_buckets_4114_);
    v___x_4119_ = lean_nat_dec_lt(v___x_4117_, v___x_4118_);
    if v___x_4119_ == 0 {
        leanh::lean_dec_ref(v_buckets_4114_);
        return v___x_4115_;
    } else {
        let mut v___f_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4121_: u8 = 0;
        v___f_4120_ = l_Std_HashMap_Raw_toArray___redArg___closed__1;
        v___x_4121_ = lean_nat_dec_le(v___x_4118_, v___x_4118_);
        if v___x_4121_ == 0 {
            if v___x_4119_ == 0 {
                leanh::lean_dec_ref(v_buckets_4114_);
                return v___x_4115_;
            } else {
                let mut v___x_4122_: usize = 0;
                let mut v___x_4123_: usize = 0;
                let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4122_ = 0usize;
                v___x_4123_ = lean_usize_of_nat(v___x_4118_);
                v___x_4124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4116_,
                    v___f_4120_,
                    v_buckets_4114_,
                    v___x_4122_,
                    v___x_4123_,
                    v___x_4115_,
                );
                return v___x_4124_;
            }
        } else {
            let mut v___x_4125_: usize = 0;
            let mut v___x_4126_: usize = 0;
            let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4125_ = 0usize;
            v___x_4126_ = lean_usize_of_nat(v___x_4118_);
            v___x_4127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4116_,
                v___f_4120_,
                v_buckets_4114_,
                v___x_4125_,
                v___x_4126_,
                v___x_4115_,
            );
            return v___x_4127_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_toArray(
    mut v_00_u03b1_4128_: *mut leanh::LeanObject,
    mut v_00_u03b2_4129_: *mut leanh::LeanObject,
    mut v_m_4130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    v_size_4131_ = leanh::lean_ctor_get(v_m_4130_, 0);
    leanh::lean_inc(v_size_4131_);
    v_buckets_4132_ = leanh::lean_ctor_get(v_m_4130_, 1);
    leanh::lean_inc_ref(v_buckets_4132_);
    leanh::lean_dec_ref(v_m_4130_);
    v___x_4133_ = lean_mk_empty_array_with_capacity(v_size_4131_);
    leanh::lean_dec(v_size_4131_);
    v___x_4134_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4135_ = leanh::lean_unsigned_to_nat(0);
    v___x_4136_ = lean_array_get_size(v_buckets_4132_);
    v___x_4137_ = lean_nat_dec_lt(v___x_4135_, v___x_4136_);
    if v___x_4137_ == 0 {
        leanh::lean_dec_ref(v_buckets_4132_);
        return v___x_4133_;
    } else {
        let mut v___f_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4139_: u8 = 0;
        v___f_4138_ = l_Std_HashMap_Raw_toArray___redArg___closed__1;
        v___x_4139_ = lean_nat_dec_le(v___x_4136_, v___x_4136_);
        if v___x_4139_ == 0 {
            if v___x_4137_ == 0 {
                leanh::lean_dec_ref(v_buckets_4132_);
                return v___x_4133_;
            } else {
                let mut v___x_4140_: usize = 0;
                let mut v___x_4141_: usize = 0;
                let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4140_ = 0usize;
                v___x_4141_ = lean_usize_of_nat(v___x_4136_);
                v___x_4142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4134_,
                    v___f_4138_,
                    v_buckets_4132_,
                    v___x_4140_,
                    v___x_4141_,
                    v___x_4133_,
                );
                return v___x_4142_;
            }
        } else {
            let mut v___x_4143_: usize = 0;
            let mut v___x_4144_: usize = 0;
            let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4143_ = 0usize;
            v___x_4144_ = lean_usize_of_nat(v___x_4136_);
            v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4134_,
                v___f_4138_,
                v_buckets_4132_,
                v___x_4143_,
                v___x_4144_,
                v___x_4133_,
            );
            return v___x_4145_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_keysArray___redArg___lam__0(
    mut v_x1_4146_: *mut leanh::LeanObject,
    mut v_x2_4147_: *mut leanh::LeanObject,
    mut v_x3_4148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = lean_array_push(v_x1_4146_, v_x2_4147_);
    return v___x_4149_;
}
pub unsafe fn l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(
    mut v_x1_4150_: *mut leanh::LeanObject,
    mut v_x2_4151_: *mut leanh::LeanObject,
    mut v_x3_4152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4153_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_4150_, v_x2_4151_, v_x3_4152_);
    leanh::lean_dec(v_x3_4152_);
    return v_res_4153_;
}
pub unsafe fn l_Std_HashMap_Raw_keysArray___redArg___lam__1(
    mut v___x_4154_: *mut leanh::LeanObject,
    mut v___f_4155_: *mut leanh::LeanObject,
    mut v_acc_4156_: *mut leanh::LeanObject,
    mut v_l_4157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4158_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4154_,
        v___f_4155_,
        v_acc_4156_,
        v_l_4157_,
    );
    return v___x_4158_;
}
pub unsafe fn l_Std_HashMap_Raw_keysArray___redArg(
    mut v_m_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    v_size_4164_ = leanh::lean_ctor_get(v_m_4163_, 0);
    leanh::lean_inc(v_size_4164_);
    v_buckets_4165_ = leanh::lean_ctor_get(v_m_4163_, 1);
    leanh::lean_inc_ref(v_buckets_4165_);
    leanh::lean_dec_ref(v_m_4163_);
    v___x_4166_ = lean_mk_empty_array_with_capacity(v_size_4164_);
    leanh::lean_dec(v_size_4164_);
    v___x_4167_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4168_ = leanh::lean_unsigned_to_nat(0);
    v___x_4169_ = lean_array_get_size(v_buckets_4165_);
    v___x_4170_ = lean_nat_dec_lt(v___x_4168_, v___x_4169_);
    if v___x_4170_ == 0 {
        leanh::lean_dec_ref(v_buckets_4165_);
        return v___x_4166_;
    } else {
        let mut v___f_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4172_: u8 = 0;
        v___f_4171_ = l_Std_HashMap_Raw_keysArray___redArg___closed__1;
        v___x_4172_ = lean_nat_dec_le(v___x_4169_, v___x_4169_);
        if v___x_4172_ == 0 {
            if v___x_4170_ == 0 {
                leanh::lean_dec_ref(v_buckets_4165_);
                return v___x_4166_;
            } else {
                let mut v___x_4173_: usize = 0;
                let mut v___x_4174_: usize = 0;
                let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4173_ = 0usize;
                v___x_4174_ = lean_usize_of_nat(v___x_4169_);
                v___x_4175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4167_,
                    v___f_4171_,
                    v_buckets_4165_,
                    v___x_4173_,
                    v___x_4174_,
                    v___x_4166_,
                );
                return v___x_4175_;
            }
        } else {
            let mut v___x_4176_: usize = 0;
            let mut v___x_4177_: usize = 0;
            let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4176_ = 0usize;
            v___x_4177_ = lean_usize_of_nat(v___x_4169_);
            v___x_4178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4167_,
                v___f_4171_,
                v_buckets_4165_,
                v___x_4176_,
                v___x_4177_,
                v___x_4166_,
            );
            return v___x_4178_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_keysArray(
    mut v_00_u03b1_4179_: *mut leanh::LeanObject,
    mut v_00_u03b2_4180_: *mut leanh::LeanObject,
    mut v_m_4181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: u8 = 0;
    v_size_4182_ = leanh::lean_ctor_get(v_m_4181_, 0);
    leanh::lean_inc(v_size_4182_);
    v_buckets_4183_ = leanh::lean_ctor_get(v_m_4181_, 1);
    leanh::lean_inc_ref(v_buckets_4183_);
    leanh::lean_dec_ref(v_m_4181_);
    v___x_4184_ = lean_mk_empty_array_with_capacity(v_size_4182_);
    leanh::lean_dec(v_size_4182_);
    v___x_4185_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4186_ = leanh::lean_unsigned_to_nat(0);
    v___x_4187_ = lean_array_get_size(v_buckets_4183_);
    v___x_4188_ = lean_nat_dec_lt(v___x_4186_, v___x_4187_);
    if v___x_4188_ == 0 {
        leanh::lean_dec_ref(v_buckets_4183_);
        return v___x_4184_;
    } else {
        let mut v___f_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4190_: u8 = 0;
        v___f_4189_ = l_Std_HashMap_Raw_keysArray___redArg___closed__1;
        v___x_4190_ = lean_nat_dec_le(v___x_4187_, v___x_4187_);
        if v___x_4190_ == 0 {
            if v___x_4188_ == 0 {
                leanh::lean_dec_ref(v_buckets_4183_);
                return v___x_4184_;
            } else {
                let mut v___x_4191_: usize = 0;
                let mut v___x_4192_: usize = 0;
                let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4191_ = 0usize;
                v___x_4192_ = lean_usize_of_nat(v___x_4187_);
                v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4185_,
                    v___f_4189_,
                    v_buckets_4183_,
                    v___x_4191_,
                    v___x_4192_,
                    v___x_4184_,
                );
                return v___x_4193_;
            }
        } else {
            let mut v___x_4194_: usize = 0;
            let mut v___x_4195_: usize = 0;
            let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4194_ = 0usize;
            v___x_4195_ = lean_usize_of_nat(v___x_4187_);
            v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4185_,
                v___f_4189_,
                v_buckets_4183_,
                v___x_4194_,
                v___x_4195_,
                v___x_4184_,
            );
            return v___x_4196_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_values___redArg___lam__0(
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_b_4198_: *mut leanh::LeanObject,
    mut v_d_4199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4200_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4200_, 0, v_b_4198_);
    leanh::lean_ctor_set(v___x_4200_, 1, v_d_4199_);
    return v___x_4200_;
}
pub unsafe fn l_Std_HashMap_Raw_values___redArg___lam__0___boxed(
    mut v_a_4201_: *mut leanh::LeanObject,
    mut v_b_4202_: *mut leanh::LeanObject,
    mut v_d_4203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_4201_, v_b_4202_, v_d_4203_);
    leanh::lean_dec(v_a_4201_);
    return v_res_4204_;
}
pub unsafe fn l_Std_HashMap_Raw_values___redArg(
    mut v_m_4209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: u8 = 0;
    v___x_4210_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_4211_ = leanh::lean_ctor_get(v_m_4209_, 1);
    leanh::lean_inc_ref(v_buckets_4211_);
    leanh::lean_dec_ref(v_m_4209_);
    v___x_4212_ = leanh::lean_box(0);
    v___x_4213_ = lean_array_get_size(v_buckets_4211_);
    v___x_4214_ = leanh::lean_unsigned_to_nat(0);
    v___x_4215_ = lean_nat_dec_lt(v___x_4214_, v___x_4213_);
    if v___x_4215_ == 0 {
        leanh::lean_dec_ref(v_buckets_4211_);
        return v___x_4212_;
    } else {
        let mut v___f_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4217_: usize = 0;
        let mut v___x_4218_: usize = 0;
        let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4216_ = l_Std_HashMap_Raw_values___redArg___closed__1;
        v___x_4217_ = lean_usize_of_nat(v___x_4213_);
        v___x_4218_ = 0usize;
        v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4210_,
            v___f_4216_,
            v_buckets_4211_,
            v___x_4217_,
            v___x_4218_,
            v___x_4212_,
        );
        return v___x_4219_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_values(
    mut v_00_u03b1_4220_: *mut leanh::LeanObject,
    mut v_00_u03b2_4221_: *mut leanh::LeanObject,
    mut v_m_4222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    v___x_4223_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_4224_ = leanh::lean_ctor_get(v_m_4222_, 1);
    leanh::lean_inc_ref(v_buckets_4224_);
    leanh::lean_dec_ref(v_m_4222_);
    v___x_4225_ = leanh::lean_box(0);
    v___x_4226_ = lean_array_get_size(v_buckets_4224_);
    v___x_4227_ = leanh::lean_unsigned_to_nat(0);
    v___x_4228_ = lean_nat_dec_lt(v___x_4227_, v___x_4226_);
    if v___x_4228_ == 0 {
        leanh::lean_dec_ref(v_buckets_4224_);
        return v___x_4225_;
    } else {
        let mut v___f_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4230_: usize = 0;
        let mut v___x_4231_: usize = 0;
        let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4229_ = l_Std_HashMap_Raw_values___redArg___closed__1;
        v___x_4230_ = lean_usize_of_nat(v___x_4226_);
        v___x_4231_ = 0usize;
        v___x_4232_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4223_,
            v___f_4229_,
            v_buckets_4224_,
            v___x_4230_,
            v___x_4231_,
            v___x_4225_,
        );
        return v___x_4232_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_valuesArray___redArg___lam__0(
    mut v_x1_4233_: *mut leanh::LeanObject,
    mut v_x2_4234_: *mut leanh::LeanObject,
    mut v_x3_4235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4236_ = lean_array_push(v_x1_4233_, v_x3_4235_);
    return v___x_4236_;
}
pub unsafe fn l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(
    mut v_x1_4237_: *mut leanh::LeanObject,
    mut v_x2_4238_: *mut leanh::LeanObject,
    mut v_x3_4239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4240_ =
        l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_4237_, v_x2_4238_, v_x3_4239_);
    leanh::lean_dec(v_x2_4238_);
    return v_res_4240_;
}
pub unsafe fn l_Std_HashMap_Raw_valuesArray___redArg(
    mut v_m_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    v_size_4246_ = leanh::lean_ctor_get(v_m_4245_, 0);
    leanh::lean_inc(v_size_4246_);
    v_buckets_4247_ = leanh::lean_ctor_get(v_m_4245_, 1);
    leanh::lean_inc_ref(v_buckets_4247_);
    leanh::lean_dec_ref(v_m_4245_);
    v___x_4248_ = lean_mk_empty_array_with_capacity(v_size_4246_);
    leanh::lean_dec(v_size_4246_);
    v___x_4249_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4250_ = leanh::lean_unsigned_to_nat(0);
    v___x_4251_ = lean_array_get_size(v_buckets_4247_);
    v___x_4252_ = lean_nat_dec_lt(v___x_4250_, v___x_4251_);
    if v___x_4252_ == 0 {
        leanh::lean_dec_ref(v_buckets_4247_);
        return v___x_4248_;
    } else {
        let mut v___f_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4254_: u8 = 0;
        v___f_4253_ = l_Std_HashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4254_ = lean_nat_dec_le(v___x_4251_, v___x_4251_);
        if v___x_4254_ == 0 {
            if v___x_4252_ == 0 {
                leanh::lean_dec_ref(v_buckets_4247_);
                return v___x_4248_;
            } else {
                let mut v___x_4255_: usize = 0;
                let mut v___x_4256_: usize = 0;
                let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4255_ = 0usize;
                v___x_4256_ = lean_usize_of_nat(v___x_4251_);
                v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4249_,
                    v___f_4253_,
                    v_buckets_4247_,
                    v___x_4255_,
                    v___x_4256_,
                    v___x_4248_,
                );
                return v___x_4257_;
            }
        } else {
            let mut v___x_4258_: usize = 0;
            let mut v___x_4259_: usize = 0;
            let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4258_ = 0usize;
            v___x_4259_ = lean_usize_of_nat(v___x_4251_);
            v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4249_,
                v___f_4253_,
                v_buckets_4247_,
                v___x_4258_,
                v___x_4259_,
                v___x_4248_,
            );
            return v___x_4260_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_valuesArray(
    mut v_00_u03b1_4261_: *mut leanh::LeanObject,
    mut v_00_u03b2_4262_: *mut leanh::LeanObject,
    mut v_m_4263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: u8 = 0;
    v_size_4264_ = leanh::lean_ctor_get(v_m_4263_, 0);
    leanh::lean_inc(v_size_4264_);
    v_buckets_4265_ = leanh::lean_ctor_get(v_m_4263_, 1);
    leanh::lean_inc_ref(v_buckets_4265_);
    leanh::lean_dec_ref(v_m_4263_);
    v___x_4266_ = lean_mk_empty_array_with_capacity(v_size_4264_);
    leanh::lean_dec(v_size_4264_);
    v___x_4267_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4268_ = leanh::lean_unsigned_to_nat(0);
    v___x_4269_ = lean_array_get_size(v_buckets_4265_);
    v___x_4270_ = lean_nat_dec_lt(v___x_4268_, v___x_4269_);
    if v___x_4270_ == 0 {
        leanh::lean_dec_ref(v_buckets_4265_);
        return v___x_4266_;
    } else {
        let mut v___f_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: u8 = 0;
        v___f_4271_ = l_Std_HashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4272_ = lean_nat_dec_le(v___x_4269_, v___x_4269_);
        if v___x_4272_ == 0 {
            if v___x_4270_ == 0 {
                leanh::lean_dec_ref(v_buckets_4265_);
                return v___x_4266_;
            } else {
                let mut v___x_4273_: usize = 0;
                let mut v___x_4274_: usize = 0;
                let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4273_ = 0usize;
                v___x_4274_ = lean_usize_of_nat(v___x_4269_);
                v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4267_,
                    v___f_4271_,
                    v_buckets_4265_,
                    v___x_4273_,
                    v___x_4274_,
                    v___x_4266_,
                );
                return v___x_4275_;
            }
        } else {
            let mut v___x_4276_: usize = 0;
            let mut v___x_4277_: usize = 0;
            let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4276_ = 0usize;
            v___x_4277_ = lean_usize_of_nat(v___x_4269_);
            v___x_4278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4267_,
                v___f_4271_,
                v_buckets_4265_,
                v___x_4276_,
                v___x_4277_,
                v___x_4266_,
            );
            return v___x_4278_;
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_insertMany___redArg(
    mut v_inst_4279_: *mut leanh::LeanObject,
    mut v_inst_4280_: *mut leanh::LeanObject,
    mut v_inst_4281_: *mut leanh::LeanObject,
    mut v_m_4282_: *mut leanh::LeanObject,
    mut v_l_4283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    v_buckets_4284_ = leanh::lean_ctor_get(v_m_4282_, 1);
    v___x_4285_ = leanh::lean_unsigned_to_nat(0);
    v___x_4286_ = lean_array_get_size(v_buckets_4284_);
    v___x_4287_ = lean_nat_dec_lt(v___x_4285_, v___x_4286_);
    if v___x_4287_ == 0 {
        leanh::lean_dec(v_l_4283_);
        leanh::lean_dec(v_inst_4281_);
        leanh::lean_dec_ref(v_inst_4280_);
        leanh::lean_dec_ref(v_inst_4279_);
        return v_m_4282_;
    } else {
        let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v_inst_4281_,
            v_inst_4279_,
            v_inst_4280_,
            v_m_4282_,
            v_l_4283_,
        );
        return v___x_4288_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_insertMany(
    mut v_00_u03b1_4289_: *mut leanh::LeanObject,
    mut v_00_u03b2_4290_: *mut leanh::LeanObject,
    mut v_inst_4291_: *mut leanh::LeanObject,
    mut v_inst_4292_: *mut leanh::LeanObject,
    mut v_00_u03c1_4293_: *mut leanh::LeanObject,
    mut v_inst_4294_: *mut leanh::LeanObject,
    mut v_m_4295_: *mut leanh::LeanObject,
    mut v_l_4296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    v_buckets_4297_ = leanh::lean_ctor_get(v_m_4295_, 1);
    v___x_4298_ = leanh::lean_unsigned_to_nat(0);
    v___x_4299_ = lean_array_get_size(v_buckets_4297_);
    v___x_4300_ = lean_nat_dec_lt(v___x_4298_, v___x_4299_);
    if v___x_4300_ == 0 {
        leanh::lean_dec(v_l_4296_);
        leanh::lean_dec(v_inst_4294_);
        leanh::lean_dec_ref(v_inst_4292_);
        leanh::lean_dec_ref(v_inst_4291_);
        return v_m_4295_;
    } else {
        let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
            v_inst_4294_,
            v_inst_4291_,
            v_inst_4292_,
            v_m_4295_,
            v_l_4296_,
        );
        return v___x_4301_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(
    mut v_inst_4302_: *mut leanh::LeanObject,
    mut v_inst_4303_: *mut leanh::LeanObject,
    mut v_inst_4304_: *mut leanh::LeanObject,
    mut v_m_4305_: *mut leanh::LeanObject,
    mut v_l_4306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    v_buckets_4307_ = leanh::lean_ctor_get(v_m_4305_, 1);
    v___x_4308_ = leanh::lean_unsigned_to_nat(0);
    v___x_4309_ = lean_array_get_size(v_buckets_4307_);
    v___x_4310_ = lean_nat_dec_lt(v___x_4308_, v___x_4309_);
    if v___x_4310_ == 0 {
        leanh::lean_dec(v_l_4306_);
        leanh::lean_dec(v_inst_4304_);
        leanh::lean_dec_ref(v_inst_4303_);
        leanh::lean_dec_ref(v_inst_4302_);
        return v_m_4305_;
    } else {
        let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v_inst_4304_,
            v_inst_4302_,
            v_inst_4303_,
            v_m_4305_,
            v_l_4306_,
        );
        return v___x_4311_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_insertManyIfNewUnit(
    mut v_00_u03b1_4312_: *mut leanh::LeanObject,
    mut v_inst_4313_: *mut leanh::LeanObject,
    mut v_inst_4314_: *mut leanh::LeanObject,
    mut v_00_u03c1_4315_: *mut leanh::LeanObject,
    mut v_inst_4316_: *mut leanh::LeanObject,
    mut v_m_4317_: *mut leanh::LeanObject,
    mut v_l_4318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: u8 = 0;
    v_buckets_4319_ = leanh::lean_ctor_get(v_m_4317_, 1);
    v___x_4320_ = leanh::lean_unsigned_to_nat(0);
    v___x_4321_ = lean_array_get_size(v_buckets_4319_);
    v___x_4322_ = lean_nat_dec_lt(v___x_4320_, v___x_4321_);
    if v___x_4322_ == 0 {
        leanh::lean_dec(v_l_4318_);
        leanh::lean_dec(v_inst_4316_);
        leanh::lean_dec_ref(v_inst_4314_);
        leanh::lean_dec_ref(v_inst_4313_);
        return v_m_4317_;
    } else {
        let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v_inst_4316_,
            v_inst_4313_,
            v_inst_4314_,
            v_m_4317_,
            v_l_4318_,
        );
        return v___x_4323_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_unitOfArray___redArg(
    mut v_inst_4324_: *mut leanh::LeanObject,
    mut v_inst_4325_: *mut leanh::LeanObject,
    mut v_l_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: u8 = 0;
    v___x_4327_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_4328_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_4328_ == 0 {
        leanh::lean_dec_ref(v_l_4326_);
        leanh::lean_dec_ref(v_inst_4325_);
        leanh::lean_dec_ref(v_inst_4324_);
        return v___x_4327_;
    } else {
        let mut v___f_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4329_ = l_Std_HashMap_Raw_ofArray___redArg___closed__1;
        v___x_4330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_4329_,
            v_inst_4324_,
            v_inst_4325_,
            v___x_4327_,
            v_l_4326_,
        );
        return v___x_4330_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_unitOfArray(
    mut v_00_u03b1_4331_: *mut leanh::LeanObject,
    mut v_inst_4332_: *mut leanh::LeanObject,
    mut v_inst_4333_: *mut leanh::LeanObject,
    mut v_l_4334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: u8 = 0;
    v___x_4335_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_4336_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_4336_ == 0 {
        leanh::lean_dec_ref(v_l_4334_);
        leanh::lean_dec_ref(v_inst_4333_);
        leanh::lean_dec_ref(v_inst_4332_);
        return v___x_4335_;
    } else {
        let mut v___f_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4337_ = l_Std_HashMap_Raw_ofArray___redArg___closed__1;
        v___x_4338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
            v___f_4337_,
            v_inst_4332_,
            v_inst_4333_,
            v___x_4335_,
            v_l_4334_,
        );
        return v___x_4338_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_Internal_numBuckets___redArg(
    mut v_m_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4340_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_4339_);
    return v___x_4340_;
}
pub unsafe fn l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(
    mut v_m_4341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_4341_);
    leanh::lean_dec_ref(v_m_4341_);
    return v_res_4342_;
}
pub unsafe fn l_Std_HashMap_Raw_Internal_numBuckets(
    mut v_00_u03b1_4343_: *mut leanh::LeanObject,
    mut v_00_u03b2_4344_: *mut leanh::LeanObject,
    mut v_m_4345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_4345_);
    return v___x_4346_;
}
pub unsafe fn l_Std_HashMap_Raw_Internal_numBuckets___boxed(
    mut v_00_u03b1_4347_: *mut leanh::LeanObject,
    mut v_00_u03b2_4348_: *mut leanh::LeanObject,
    mut v_m_4349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4350_ =
        l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_4347_, v_00_u03b2_4348_, v_m_4349_);
    leanh::lean_dec_ref(v_m_4349_);
    return v_res_4350_;
}
pub unsafe fn l_Std_HashMap_Raw_instRepr___redArg___lam__2(
    mut v___x_4354_: *mut leanh::LeanObject,
    mut v___f_4355_: *mut leanh::LeanObject,
    mut v_m_4356_: *mut leanh::LeanObject,
    mut v_prec_4357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___f_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: usize = 0;
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v_unused_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4358_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
                v_buckets_4359_ = leanh::lean_ctor_get(v_m_4356_, 1);
                v_isSharedCheck_4379_ = (!leanh::lean_is_exclusive(v_m_4356_)) as u8;
                if v_isSharedCheck_4379_ == 0 {
                    v_unused_4380_ = leanh::lean_ctor_get(v_m_4356_, 0);
                    leanh::lean_dec(v_unused_4380_);
                    v___x_4361_ = v_m_4356_;
                    v_isShared_4362_ = v_isSharedCheck_4379_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4359_);
                    leanh::lean_dec(v_m_4356_);
                    v___x_4361_ = leanh::lean_box(0);
                    v_isShared_4362_ = v_isSharedCheck_4379_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4363_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1;
                v___x_4371_ = leanh::lean_box(0);
                v___x_4372_ = lean_array_get_size(v_buckets_4359_);
                v___x_4373_ = leanh::lean_unsigned_to_nat(0);
                v___x_4374_ = lean_nat_dec_lt(v___x_4373_, v___x_4372_);
                if v___x_4374_ == 0 {
                    leanh::lean_dec_ref(v_buckets_4359_);
                    leanh::lean_dec_ref(v___f_4355_);
                    v___y_4365_ = v___x_4371_;
                    state = 2;
                    continue;
                } else {
                    v___f_4375_ = leanh::lean_alloc_closure(
                        l_Std_HashMap_Raw_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_4375_, 0, v___x_4358_);
                    leanh::lean_closure_set(v___f_4375_, 1, v___f_4355_);
                    v___x_4376_ = lean_usize_of_nat(v___x_4372_);
                    v___x_4377_ = 0usize;
                    v___x_4378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_4358_,
                        v___f_4375_,
                        v_buckets_4359_,
                        v___x_4376_,
                        v___x_4377_,
                        v___x_4371_,
                    );
                    v___y_4365_ = v___x_4378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4366_ = l_List_repr___redArg(v___x_4354_, v___y_4365_);
                if v_isShared_4362_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4361_, 5);
                    leanh::lean_ctor_set(v___x_4361_, 1, v___x_4366_);
                    leanh::lean_ctor_set(v___x_4361_, 0, v___x_4363_);
                    v___x_4368_ = v___x_4361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4363_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 1, v___x_4366_);
                    v___x_4368_ = v_reuseFailAlloc_4370_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4369_ = l_Repr_addAppParen(v___x_4368_, v_prec_4357_);
                return v___x_4369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(
    mut v___x_4381_: *mut leanh::LeanObject,
    mut v___f_4382_: *mut leanh::LeanObject,
    mut v_m_4383_: *mut leanh::LeanObject,
    mut v_prec_4384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4385_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(
        v___x_4381_,
        v___f_4382_,
        v_m_4383_,
        v_prec_4384_,
    );
    leanh::lean_dec(v_prec_4384_);
    return v_res_4385_;
}
pub unsafe fn l_Std_HashMap_Raw_instRepr___redArg(
    mut v_inst_4386_: *mut leanh::LeanObject,
    mut v_inst_4387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4388_ = l_Std_HashMap_Raw_toList___redArg___closed__0;
    v___f_4389_ = leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4389_, 0, v_inst_4387_);
    v___x_4390_ =
        leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4390_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4390_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4390_, 2, v_inst_4386_);
    leanh::lean_closure_set(v___x_4390_, 3, v___f_4389_);
    v___f_4391_ = leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4391_, 0, v___x_4390_);
    leanh::lean_closure_set(v___f_4391_, 1, v___f_4388_);
    return v___f_4391_;
}
pub unsafe fn l_Std_HashMap_Raw_instRepr(
    mut v_00_u03b1_4392_: *mut leanh::LeanObject,
    mut v_00_u03b2_4393_: *mut leanh::LeanObject,
    mut v_inst_4394_: *mut leanh::LeanObject,
    mut v_inst_4395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4396_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_4394_, v_inst_4395_);
    return v___x_4396_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_Raw(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashMap_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_Raw(builtin);
}