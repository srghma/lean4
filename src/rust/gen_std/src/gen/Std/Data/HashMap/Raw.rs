// Lean compiler output
// Module: Std.Data.HashMap.Raw
// Imports: Std.Data.DHashMap.Raw
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
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashMap_Raw_instEmptyCollection___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashMap_Raw_term___x7em___00__closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [72, 97, 115, 104, 77, 97, 112, 0],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__3_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            7102038059608022050 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            8317422437539803697 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_HashMap_Raw_term___x7em___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            11341035097657881147 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__9_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_HashMap_Raw_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__11_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_term___x7em___00__closed__13_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_term___x7em___00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_HashMap_Raw_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,7102038059608022050 as *mut crate::leanh::LeanObject] };
static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw_term___x7em___00__closed__2_value) as *mut crate::leanh::LeanObject,8317422437539803697 as *mut crate::leanh::LeanObject] };
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,14692178904334265170 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1: u8 = 0;
pub static l_Std_HashMap_Raw_keys___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_Raw_keys___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__10_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_Raw_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keys___redArg___closed__11_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_Raw_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_keys___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofList___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_ofList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofList___redArg___closed__1_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_ofList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_ofList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_ofArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_ofArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
        core::ptr::addr_of!(l_Std_HashMap_Raw_ofArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_ofArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_ofArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_Raw_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_toList___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_Raw_toList___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_toList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_toList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_all___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
static mut l_Std_HashMap_Raw_all___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_all___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_union___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_union___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_union___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_toArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashMap_Raw_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_toArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashMap_Raw_toArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keysArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashMap_Raw_keysArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keysArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_keysArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashMap_Raw_keysArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_keysArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_keysArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_values___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_Raw_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_Raw_values___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_values___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_values___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_Raw_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_Raw_values___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_Raw_values___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_values___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashMap_Raw_valuesArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value:
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
    m_fun: l_Std_HashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashMap_Raw_keys___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_valuesArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value:
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
        83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 46, 82, 97, 119, 46, 111, 102, 76, 105,
        115, 116, 32, 0,
    ],
};
static mut l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity___redArg(
    mut v_capacity_2199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2201_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2202_ = lean_nat_mul(v_capacity_2199_, v___x_2201_);
    v___x_2203_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2204_ = lean_nat_div(v___x_2202_, v___x_2203_);
    crate::leanh::lean_dec(v___x_2202_);
    v___x_2205_ = l_Nat_nextPowerOfTwo(v___x_2204_);
    crate::leanh::lean_dec(v___x_2204_);
    v___x_2206_ = crate::leanh::lean_box(0);
    v___x_2207_ = lean_mk_array(v___x_2205_, v___x_2206_);
    v___x_2208_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2208_, 0, v___x_2200_);
    crate::leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity___redArg___boxed(
    mut v_capacity_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2210_ = l_Std_HashMap_Raw_emptyWithCapacity___redArg(v_capacity_2209_);
    crate::leanh::lean_dec(v_capacity_2209_);
    return v_res_2210_;
}
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity(
    mut v_00_u03b1_2211_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2212_: *mut crate::leanh::LeanObject,
    mut v_capacity_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2215_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2216_ = lean_nat_mul(v_capacity_2213_, v___x_2215_);
    v___x_2217_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2218_ = lean_nat_div(v___x_2216_, v___x_2217_);
    crate::leanh::lean_dec(v___x_2216_);
    v___x_2219_ = l_Nat_nextPowerOfTwo(v___x_2218_);
    crate::leanh::lean_dec(v___x_2218_);
    v___x_2220_ = crate::leanh::lean_box(0);
    v___x_2221_ = lean_mk_array(v___x_2219_, v___x_2220_);
    v___x_2222_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2214_);
    crate::leanh::lean_ctor_set(v___x_2222_, 1, v___x_2221_);
    return v___x_2222_;
}
pub unsafe fn l_Std_HashMap_Raw_emptyWithCapacity___boxed(
    mut v_00_u03b1_2223_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2224_: *mut crate::leanh::LeanObject,
    mut v_capacity_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2226_ =
        l_Std_HashMap_Raw_emptyWithCapacity(v_00_u03b1_2223_, v_00_u03b2_2224_, v_capacity_2225_);
    crate::leanh::lean_dec(v_capacity_2225_);
    return v_res_2226_;
}
pub unsafe fn _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2227_ = crate::leanh::lean_box(0);
    v___x_2228_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2229_ = lean_mk_array(v___x_2228_, v___x_2227_);
    return v___x_2229_;
}
pub unsafe fn _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2231_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2232_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    crate::leanh::lean_ctor_set(v___x_2232_, 1, v___x_2230_);
    return v___x_2232_;
}
pub unsafe fn l_Std_HashMap_Raw_instEmptyCollection(
    mut v_00_u03b1_2233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2235_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2235_;
}
pub unsafe fn l_Std_HashMap_Raw_instInhabited(
    mut v_00_u03b1_2236_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2238_;
}
pub unsafe fn _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2279_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5;
    v___x_2280_ = l_String_toRawSubstring_x27(v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(
    mut v_x_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
    mut v_a_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    v___x_2305_ = l_Std_HashMap_Raw_term___x7em___00__closed__4;
    crate::leanh::lean_inc(v_x_2302_);
    v___x_2306_ = l_Lean_Syntax_isOfKind(v_x_2302_, v___x_2305_);
    if v___x_2306_ == 0 {
        let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2302_);
        v___x_2307_ = crate::leanh::lean_box(1);
        v___x_2308_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
        crate::leanh::lean_ctor_set(v___x_2308_, 1, v_a_2304_);
        return v___x_2308_;
    } else {
        let mut v_quotContext_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2316_: u8 = 0;
        let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2309_ = crate::leanh::lean_ctor_get(v_a_2303_, 1);
        v_currMacroScope_2310_ = crate::leanh::lean_ctor_get(v_a_2303_, 2);
        v_ref_2311_ = crate::leanh::lean_ctor_get(v_a_2303_, 5);
        v___x_2312_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2313_ = l_Lean_Syntax_getArg(v_x_2302_, v___x_2312_);
        v___x_2314_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2315_ = l_Lean_Syntax_getArg(v_x_2302_, v___x_2314_);
        crate::leanh::lean_dec(v_x_2302_);
        v___x_2316_ = 0;
        v___x_2317_ = l_Lean_SourceInfo_fromRef(v_ref_2311_, v___x_2316_);
        v___x_2318_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4;
        v___x_2319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once), _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
        v___x_2320_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_2310_);
        crate::leanh::lean_inc(v_quotContext_2309_);
        v___x_2321_ =
            l_Lean_addMacroScope(v_quotContext_2309_, v___x_2320_, v_currMacroScope_2310_);
        v___x_2322_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12;
        crate::leanh::lean_inc_n(v___x_2317_, 2);
        v___x_2323_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2317_);
        crate::leanh::lean_ctor_set(v___x_2323_, 1, v___x_2319_);
        crate::leanh::lean_ctor_set(v___x_2323_, 2, v___x_2321_);
        crate::leanh::lean_ctor_set(v___x_2323_, 3, v___x_2322_);
        v___x_2324_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14;
        v___x_2325_ = l_Lean_Syntax_node2(v___x_2317_, v___x_2324_, v___x_2313_, v___x_2315_);
        v___x_2326_ = l_Lean_Syntax_node2(v___x_2317_, v___x_2318_, v___x_2323_, v___x_2325_);
        v___x_2327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2327_, 0, v___x_2326_);
        crate::leanh::lean_ctor_set(v___x_2327_, 1, v_a_2304_);
        return v___x_2327_;
    }
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(
    mut v_x_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(v_x_2328_, v_a_2329_, v_a_2330_);
    crate::leanh::lean_dec_ref(v_a_2329_);
    return v_res_2331_;
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(
    mut v_x_2335_: *mut crate::leanh::LeanObject,
    mut v_a_2336_: *mut crate::leanh::LeanObject,
    mut v_a_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    v___x_2338_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4;
    crate::leanh::lean_inc(v_x_2335_);
    v___x_2339_ = l_Lean_Syntax_isOfKind(v_x_2335_, v___x_2338_);
    if v___x_2339_ == 0 {
        let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2335_);
        v___x_2340_ = crate::leanh::lean_box(0);
        v___x_2341_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2341_, 0, v___x_2340_);
        crate::leanh::lean_ctor_set(v___x_2341_, 1, v_a_2337_);
        return v___x_2341_;
    } else {
        let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2345_: u8 = 0;
        v___x_2342_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2343_ = l_Lean_Syntax_getArg(v_x_2335_, v___x_2342_);
        v___x_2344_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_2343_);
        v___x_2345_ = l_Lean_Syntax_isOfKind(v___x_2343_, v___x_2344_);
        if v___x_2345_ == 0 {
            let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2343_);
            crate::leanh::lean_dec(v_x_2335_);
            v___x_2346_ = crate::leanh::lean_box(0);
            v___x_2347_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2347_, 0, v___x_2346_);
            crate::leanh::lean_ctor_set(v___x_2347_, 1, v_a_2337_);
            return v___x_2347_;
        } else {
            let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2351_: u8 = 0;
            v___x_2348_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2349_ = l_Lean_Syntax_getArg(v_x_2335_, v___x_2348_);
            crate::leanh::lean_dec(v_x_2335_);
            v___x_2350_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_2349_);
            v___x_2351_ = l_Lean_Syntax_matchesNull(v___x_2349_, v___x_2350_);
            if v___x_2351_ == 0 {
                let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2349_);
                crate::leanh::lean_dec(v___x_2343_);
                v___x_2352_ = crate::leanh::lean_box(0);
                v___x_2353_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2353_, 0, v___x_2352_);
                crate::leanh::lean_ctor_set(v___x_2353_, 1, v_a_2337_);
                return v___x_2353_;
            } else {
                let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2357_: u8 = 0;
                let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2354_ = l_Lean_Syntax_getArg(v___x_2349_, v___x_2342_);
                v___x_2355_ = l_Lean_Syntax_getArg(v___x_2349_, v___x_2348_);
                crate::leanh::lean_dec(v___x_2349_);
                v_ref_2356_ = l_Lean_replaceRef(v___x_2343_, v_a_2336_);
                crate::leanh::lean_dec(v___x_2343_);
                v___x_2357_ = 0;
                v___x_2358_ = l_Lean_SourceInfo_fromRef(v_ref_2356_, v___x_2357_);
                crate::leanh::lean_dec(v_ref_2356_);
                v___x_2359_ = l_Std_HashMap_Raw_term___x7em___00__closed__4;
                v___x_2360_ = l_Std_HashMap_Raw_term___x7em___00__closed__7;
                crate::leanh::lean_inc(v___x_2358_);
                v___x_2361_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2361_, 0, v___x_2358_);
                crate::leanh::lean_ctor_set(v___x_2361_, 1, v___x_2360_);
                v___x_2362_ = l_Lean_Syntax_node3(
                    v___x_2358_,
                    v___x_2359_,
                    v___x_2354_,
                    v___x_2361_,
                    v___x_2355_,
                );
                v___x_2363_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2363_, 0, v___x_2362_);
                crate::leanh::lean_ctor_set(v___x_2363_, 1, v_a_2337_);
                return v___x_2363_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(
    mut v_x_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
    mut v_a_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2367_ =
        l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(
            v_x_2364_, v_a_2365_, v_a_2366_,
        );
    crate::leanh::lean_dec(v_a_2365_);
    return v_res_2367_;
}
pub unsafe fn l_Std_HashMap_Raw_insert___redArg(
    mut v_beq_2368_: *mut crate::leanh::LeanObject,
    mut v_inst_2369_: *mut crate::leanh::LeanObject,
    mut v_m_2370_: *mut crate::leanh::LeanObject,
    mut v_a_2371_: *mut crate::leanh::LeanObject,
    mut v_b_2372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: u8 = 0;
    v_buckets_2373_ = crate::leanh::lean_ctor_get(v_m_2370_, 1);
    v___x_2374_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2375_ = lean_array_get_size(v_buckets_2373_);
    v___x_2376_ = lean_nat_dec_lt(v___x_2374_, v___x_2375_);
    if v___x_2376_ == 0 {
        crate::leanh::lean_dec(v_b_2372_);
        crate::leanh::lean_dec(v_a_2371_);
        crate::leanh::lean_dec_ref(v_inst_2369_);
        crate::leanh::lean_dec_ref(v_beq_2368_);
        return v_m_2370_;
    } else {
        let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2378_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2379_: *mut crate::leanh::LeanObject,
    mut v_beq_2380_: *mut crate::leanh::LeanObject,
    mut v_inst_2381_: *mut crate::leanh::LeanObject,
    mut v_m_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v_b_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    v_buckets_2385_ = crate::leanh::lean_ctor_get(v_m_2382_, 1);
    v___x_2386_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2387_ = lean_array_get_size(v_buckets_2385_);
    v___x_2388_ = lean_nat_dec_lt(v___x_2386_, v___x_2387_);
    if v___x_2388_ == 0 {
        crate::leanh::lean_dec(v_b_2384_);
        crate::leanh::lean_dec(v_a_2383_);
        crate::leanh::lean_dec_ref(v_inst_2381_);
        crate::leanh::lean_dec_ref(v_beq_2380_);
        return v_m_2382_;
    } else {
        let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2390_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2391_ = lean_array_get_size(v___x_2390_);
    return v___x_2391_;
}
pub unsafe fn _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1()
-> u8 {
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    v___x_2392_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0,
    );
    v___x_2393_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2394_ = lean_nat_dec_lt(v___x_2393_, v___x_2392_);
    return v___x_2394_;
}
pub unsafe fn l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2395_: *mut crate::leanh::LeanObject,
    mut v_inst_2396_: *mut crate::leanh::LeanObject,
    mut v_x_2397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    v_fst_2398_ = crate::leanh::lean_ctor_get(v_x_2397_, 0);
    crate::leanh::lean_inc(v_fst_2398_);
    v_snd_2399_ = crate::leanh::lean_ctor_get(v_x_2397_, 1);
    crate::leanh::lean_inc(v_snd_2399_);
    crate::leanh::lean_dec_ref(v_x_2397_);
    v___x_2400_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_2401_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2401_ == 0 {
        crate::leanh::lean_dec(v_snd_2399_);
        crate::leanh::lean_dec(v_fst_2398_);
        crate::leanh::lean_dec_ref(v_inst_2396_);
        crate::leanh::lean_dec_ref(v_inst_2395_);
        return v___x_2400_;
    } else {
        let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2403_: *mut crate::leanh::LeanObject,
    mut v_inst_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2405_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2405_, 0, v_inst_2403_);
    crate::leanh::lean_closure_set(v___f_2405_, 1, v_inst_2404_);
    return v___f_2405_;
}
pub unsafe fn l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(
    mut v_00_u03b1_2406_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2407_: *mut crate::leanh::LeanObject,
    mut v_inst_2408_: *mut crate::leanh::LeanObject,
    mut v_inst_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2410_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2410_, 0, v_inst_2408_);
    crate::leanh::lean_closure_set(v___f_2410_, 1, v_inst_2409_);
    return v___f_2410_;
}
pub unsafe fn l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2411_: *mut crate::leanh::LeanObject,
    mut v_inst_2412_: *mut crate::leanh::LeanObject,
    mut v_x_2413_: *mut crate::leanh::LeanObject,
    mut v_s_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    v_fst_2415_ = crate::leanh::lean_ctor_get(v_x_2413_, 0);
    crate::leanh::lean_inc(v_fst_2415_);
    v_snd_2416_ = crate::leanh::lean_ctor_get(v_x_2413_, 1);
    crate::leanh::lean_inc(v_snd_2416_);
    crate::leanh::lean_dec_ref(v_x_2413_);
    v_buckets_2417_ = crate::leanh::lean_ctor_get(v_s_2414_, 1);
    v___x_2418_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2419_ = lean_array_get_size(v_buckets_2417_);
    v___x_2420_ = lean_nat_dec_lt(v___x_2418_, v___x_2419_);
    if v___x_2420_ == 0 {
        crate::leanh::lean_dec(v_snd_2416_);
        crate::leanh::lean_dec(v_fst_2415_);
        crate::leanh::lean_dec_ref(v_inst_2412_);
        crate::leanh::lean_dec_ref(v_inst_2411_);
        return v_s_2414_;
    } else {
        let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2422_: *mut crate::leanh::LeanObject,
    mut v_inst_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2424_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2424_, 0, v_inst_2422_);
    crate::leanh::lean_closure_set(v___f_2424_, 1, v_inst_2423_);
    return v___f_2424_;
}
pub unsafe fn l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(
    mut v_00_u03b1_2425_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2426_: *mut crate::leanh::LeanObject,
    mut v_inst_2427_: *mut crate::leanh::LeanObject,
    mut v_inst_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2429_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2429_, 0, v_inst_2427_);
    crate::leanh::lean_closure_set(v___f_2429_, 1, v_inst_2428_);
    return v___f_2429_;
}
pub unsafe fn l_Std_HashMap_Raw_insertIfNew___redArg(
    mut v_inst_2430_: *mut crate::leanh::LeanObject,
    mut v_inst_2431_: *mut crate::leanh::LeanObject,
    mut v_m_2432_: *mut crate::leanh::LeanObject,
    mut v_a_2433_: *mut crate::leanh::LeanObject,
    mut v_b_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    v_buckets_2435_ = crate::leanh::lean_ctor_get(v_m_2432_, 1);
    v___x_2436_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2437_ = lean_array_get_size(v_buckets_2435_);
    v___x_2438_ = lean_nat_dec_lt(v___x_2436_, v___x_2437_);
    if v___x_2438_ == 0 {
        crate::leanh::lean_dec(v_b_2434_);
        crate::leanh::lean_dec(v_a_2433_);
        crate::leanh::lean_dec_ref(v_inst_2431_);
        crate::leanh::lean_dec_ref(v_inst_2430_);
        return v_m_2432_;
    } else {
        let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2440_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2441_: *mut crate::leanh::LeanObject,
    mut v_inst_2442_: *mut crate::leanh::LeanObject,
    mut v_inst_2443_: *mut crate::leanh::LeanObject,
    mut v_m_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
    mut v_b_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    v_buckets_2447_ = crate::leanh::lean_ctor_get(v_m_2444_, 1);
    v___x_2448_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2449_ = lean_array_get_size(v_buckets_2447_);
    v___x_2450_ = lean_nat_dec_lt(v___x_2448_, v___x_2449_);
    if v___x_2450_ == 0 {
        crate::leanh::lean_dec(v_b_2446_);
        crate::leanh::lean_dec(v_a_2445_);
        crate::leanh::lean_dec_ref(v_inst_2443_);
        crate::leanh::lean_dec_ref(v_inst_2442_);
        return v_m_2444_;
    } else {
        let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2452_: *mut crate::leanh::LeanObject,
    mut v_inst_2453_: *mut crate::leanh::LeanObject,
    mut v_m_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_b_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: u8 = 0;
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v_val_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2513_: u8 = 0;
    let mut v_unused_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2457_ = crate::leanh::lean_ctor_get(v_m_2454_, 0);
                v_buckets_2458_ = crate::leanh::lean_ctor_get(v_m_2454_, 1);
                v___x_2459_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2460_ = lean_array_get_size(v_buckets_2458_);
                v___x_2461_ = lean_nat_dec_lt(v___x_2459_, v___x_2460_);
                if v___x_2461_ == 0 {
                    crate::leanh::lean_dec(v_b_2456_);
                    crate::leanh::lean_dec(v_a_2455_);
                    crate::leanh::lean_dec_ref(v_inst_2453_);
                    crate::leanh::lean_dec_ref(v_inst_2452_);
                    v___x_2462_ = crate::leanh::lean_box((v___x_2461_) as usize);
                    v___x_2463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2462_);
                    crate::leanh::lean_ctor_set(v___x_2463_, 1, v_m_2454_);
                    return v___x_2463_;
                } else {
                    crate::leanh::lean_inc_ref(v_buckets_2458_);
                    crate::leanh::lean_inc(v_size_2457_);
                    v_isSharedCheck_2513_ = (!crate::leanh::lean_is_exclusive(v_m_2454_)) as u8;
                    if v_isSharedCheck_2513_ == 0 {
                        v_unused_2514_ = crate::leanh::lean_ctor_get(v_m_2454_, 1);
                        crate::leanh::lean_dec(v_unused_2514_);
                        v_unused_2515_ = crate::leanh::lean_ctor_get(v_m_2454_, 0);
                        crate::leanh::lean_dec(v_unused_2515_);
                        v___x_2465_ = v_m_2454_;
                        v_isShared_2466_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2454_);
                        v___x_2465_ = crate::leanh::lean_box(0);
                        v_isShared_2466_ = v_isSharedCheck_2513_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_2453_);
                crate::leanh::lean_inc_n(v_a_2455_, 2);
                v___x_2467_ = crate::leanh::lean_apply_1(v_inst_2453_, v_a_2455_);
                v___x_2468_ = 32u64;
                v___x_2469_ = crate::leanh::lean_unbox_uint64(v___x_2467_);
                v___x_2470_ = lean_uint64_shift_right(v___x_2469_, v___x_2468_);
                v___x_2471_ = crate::leanh::lean_unbox_uint64(v___x_2467_);
                crate::leanh::lean_dec_ref(v___x_2467_);
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
                crate::leanh::lean_inc(v_bkt_2481_);
                crate::leanh::lean_inc_ref(v_inst_2452_);
                v___x_2482_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2452_,
                    v_a_2455_,
                    v_bkt_2481_,
                );
                if v___x_2482_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2452_);
                    v___x_2483_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2484_ = lean_nat_add(v_size_2457_, v___x_2483_);
                    crate::leanh::lean_dec(v_size_2457_);
                    crate::leanh::lean_inc(v_bkt_2481_);
                    v___x_2485_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2485_, 0, v_a_2455_);
                    crate::leanh::lean_ctor_set(v___x_2485_, 1, v_b_2456_);
                    crate::leanh::lean_ctor_set(v___x_2485_, 2, v_bkt_2481_);
                    v_buckets_x27_2486_ =
                        lean_array_uset(v_buckets_2458_, v___x_2480_, v___x_2485_);
                    v___x_2487_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2488_ = lean_nat_mul(v_size_x27_2484_, v___x_2487_);
                    v___x_2489_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2490_ = lean_nat_div(v___x_2488_, v___x_2489_);
                    crate::leanh::lean_dec(v___x_2488_);
                    v___x_2491_ = lean_array_get_size(v_buckets_x27_2486_);
                    v___x_2492_ = lean_nat_dec_le(v___x_2490_, v___x_2491_);
                    crate::leanh::lean_dec(v___x_2490_);
                    if v___x_2492_ == 0 {
                        v_val_2493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2453_,
                            v_buckets_x27_2486_,
                        );
                        if v_isShared_2466_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2465_, 1, v_val_2493_);
                            crate::leanh::lean_ctor_set(v___x_2465_, 0, v_size_x27_2484_);
                            v___x_2495_ = v___x_2465_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2498_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2498_,
                                0,
                                v_size_x27_2484_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_val_2493_);
                            v___x_2495_ = v_reuseFailAlloc_2498_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2453_);
                        if v_isShared_2466_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2465_, 1, v_buckets_x27_2486_);
                            crate::leanh::lean_ctor_set(v___x_2465_, 0, v_size_x27_2484_);
                            v___x_2500_ = v___x_2465_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2503_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2503_,
                                0,
                                v_size_x27_2484_,
                            );
                            crate::leanh::lean_ctor_set(
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
                    crate::leanh::lean_inc(v_bkt_2481_);
                    crate::leanh::lean_dec_ref(v_inst_2453_);
                    v___x_2504_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_2465_, 1, v___x_2507_);
                        v___x_2509_ = v___x_2465_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_size_2457_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2507_);
                        v___x_2509_ = v_reuseFailAlloc_2512_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2496_ = crate::leanh::lean_box((v___x_2482_) as usize);
                v___x_2497_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2497_, 0, v___x_2496_);
                crate::leanh::lean_ctor_set(v___x_2497_, 1, v___x_2495_);
                return v___x_2497_;
            }
            3 => {
                v___x_2501_ = crate::leanh::lean_box((v___x_2482_) as usize);
                v___x_2502_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2502_, 0, v___x_2501_);
                crate::leanh::lean_ctor_set(v___x_2502_, 1, v___x_2500_);
                return v___x_2502_;
            }
            4 => {
                v___x_2510_ = crate::leanh::lean_box((v___x_2482_) as usize);
                v___x_2511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2510_);
                crate::leanh::lean_ctor_set(v___x_2511_, 1, v___x_2509_);
                return v___x_2511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_containsThenInsert(
    mut v_00_u03b1_2516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2517_: *mut crate::leanh::LeanObject,
    mut v_inst_2518_: *mut crate::leanh::LeanObject,
    mut v_inst_2519_: *mut crate::leanh::LeanObject,
    mut v_m_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
    mut v_b_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    let mut v_val_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_unused_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2523_ = crate::leanh::lean_ctor_get(v_m_2520_, 0);
                v_buckets_2524_ = crate::leanh::lean_ctor_get(v_m_2520_, 1);
                v___x_2525_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2526_ = lean_array_get_size(v_buckets_2524_);
                v___x_2527_ = lean_nat_dec_lt(v___x_2525_, v___x_2526_);
                if v___x_2527_ == 0 {
                    crate::leanh::lean_dec(v_b_2522_);
                    crate::leanh::lean_dec(v_a_2521_);
                    crate::leanh::lean_dec_ref(v_inst_2519_);
                    crate::leanh::lean_dec_ref(v_inst_2518_);
                    v___x_2528_ = crate::leanh::lean_box((v___x_2527_) as usize);
                    v___x_2529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2528_);
                    crate::leanh::lean_ctor_set(v___x_2529_, 1, v_m_2520_);
                    return v___x_2529_;
                } else {
                    crate::leanh::lean_inc_ref(v_buckets_2524_);
                    crate::leanh::lean_inc(v_size_2523_);
                    v_isSharedCheck_2579_ = (!crate::leanh::lean_is_exclusive(v_m_2520_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v_unused_2580_ = crate::leanh::lean_ctor_get(v_m_2520_, 1);
                        crate::leanh::lean_dec(v_unused_2580_);
                        v_unused_2581_ = crate::leanh::lean_ctor_get(v_m_2520_, 0);
                        crate::leanh::lean_dec(v_unused_2581_);
                        v___x_2531_ = v_m_2520_;
                        v_isShared_2532_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2520_);
                        v___x_2531_ = crate::leanh::lean_box(0);
                        v_isShared_2532_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_2519_);
                crate::leanh::lean_inc_n(v_a_2521_, 2);
                v___x_2533_ = crate::leanh::lean_apply_1(v_inst_2519_, v_a_2521_);
                v___x_2534_ = 32u64;
                v___x_2535_ = crate::leanh::lean_unbox_uint64(v___x_2533_);
                v___x_2536_ = lean_uint64_shift_right(v___x_2535_, v___x_2534_);
                v___x_2537_ = crate::leanh::lean_unbox_uint64(v___x_2533_);
                crate::leanh::lean_dec_ref(v___x_2533_);
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
                crate::leanh::lean_inc(v_bkt_2547_);
                crate::leanh::lean_inc_ref(v_inst_2518_);
                v___x_2548_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2518_,
                    v_a_2521_,
                    v_bkt_2547_,
                );
                if v___x_2548_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2518_);
                    v___x_2549_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2550_ = lean_nat_add(v_size_2523_, v___x_2549_);
                    crate::leanh::lean_dec(v_size_2523_);
                    crate::leanh::lean_inc(v_bkt_2547_);
                    v___x_2551_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2551_, 0, v_a_2521_);
                    crate::leanh::lean_ctor_set(v___x_2551_, 1, v_b_2522_);
                    crate::leanh::lean_ctor_set(v___x_2551_, 2, v_bkt_2547_);
                    v_buckets_x27_2552_ =
                        lean_array_uset(v_buckets_2524_, v___x_2546_, v___x_2551_);
                    v___x_2553_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2554_ = lean_nat_mul(v_size_x27_2550_, v___x_2553_);
                    v___x_2555_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2556_ = lean_nat_div(v___x_2554_, v___x_2555_);
                    crate::leanh::lean_dec(v___x_2554_);
                    v___x_2557_ = lean_array_get_size(v_buckets_x27_2552_);
                    v___x_2558_ = lean_nat_dec_le(v___x_2556_, v___x_2557_);
                    crate::leanh::lean_dec(v___x_2556_);
                    if v___x_2558_ == 0 {
                        v_val_2559_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2519_,
                            v_buckets_x27_2552_,
                        );
                        if v_isShared_2532_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2531_, 1, v_val_2559_);
                            crate::leanh::lean_ctor_set(v___x_2531_, 0, v_size_x27_2550_);
                            v___x_2561_ = v___x_2531_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2564_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2564_,
                                0,
                                v_size_x27_2550_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_val_2559_);
                            v___x_2561_ = v_reuseFailAlloc_2564_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2519_);
                        if v_isShared_2532_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2531_, 1, v_buckets_x27_2552_);
                            crate::leanh::lean_ctor_set(v___x_2531_, 0, v_size_x27_2550_);
                            v___x_2566_ = v___x_2531_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2569_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2569_,
                                0,
                                v_size_x27_2550_,
                            );
                            crate::leanh::lean_ctor_set(
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
                    crate::leanh::lean_inc(v_bkt_2547_);
                    crate::leanh::lean_dec_ref(v_inst_2519_);
                    v___x_2570_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_2531_, 1, v___x_2573_);
                        v___x_2575_ = v___x_2531_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2578_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_size_2523_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2573_);
                        v___x_2575_ = v_reuseFailAlloc_2578_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2562_ = crate::leanh::lean_box((v___x_2548_) as usize);
                v___x_2563_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2563_, 0, v___x_2562_);
                crate::leanh::lean_ctor_set(v___x_2563_, 1, v___x_2561_);
                return v___x_2563_;
            }
            3 => {
                v___x_2567_ = crate::leanh::lean_box((v___x_2548_) as usize);
                v___x_2568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                crate::leanh::lean_ctor_set(v___x_2568_, 1, v___x_2566_);
                return v___x_2568_;
            }
            4 => {
                v___x_2576_ = crate::leanh::lean_box((v___x_2548_) as usize);
                v___x_2577_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2577_, 0, v___x_2576_);
                crate::leanh::lean_ctor_set(v___x_2577_, 1, v___x_2575_);
                return v___x_2577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(
    mut v_inst_2582_: *mut crate::leanh::LeanObject,
    mut v_inst_2583_: *mut crate::leanh::LeanObject,
    mut v_m_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
    mut v_b_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v_val_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_unused_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2587_ = crate::leanh::lean_ctor_get(v_m_2584_, 0);
                v_buckets_2588_ = crate::leanh::lean_ctor_get(v_m_2584_, 1);
                v___x_2589_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2590_ = lean_array_get_size(v_buckets_2588_);
                v___x_2591_ = lean_nat_dec_lt(v___x_2589_, v___x_2590_);
                if v___x_2591_ == 0 {
                    crate::leanh::lean_dec(v_b_2586_);
                    crate::leanh::lean_dec(v_a_2585_);
                    crate::leanh::lean_dec_ref(v_inst_2583_);
                    crate::leanh::lean_dec_ref(v_inst_2582_);
                    v___x_2592_ = crate::leanh::lean_box((v___x_2591_) as usize);
                    v___x_2593_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2593_, 0, v___x_2592_);
                    crate::leanh::lean_ctor_set(v___x_2593_, 1, v_m_2584_);
                    return v___x_2593_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_2583_);
                    crate::leanh::lean_inc_n(v_a_2585_, 2);
                    v___x_2594_ = crate::leanh::lean_apply_1(v_inst_2583_, v_a_2585_);
                    v___x_2595_ = 32u64;
                    v___x_2596_ = crate::leanh::lean_unbox_uint64(v___x_2594_);
                    v___x_2597_ = lean_uint64_shift_right(v___x_2596_, v___x_2595_);
                    v___x_2598_ = crate::leanh::lean_unbox_uint64(v___x_2594_);
                    crate::leanh::lean_dec_ref(v___x_2594_);
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
                    crate::leanh::lean_inc(v_bkt_2608_);
                    v___x_2609_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_2582_,
                        v_a_2585_,
                        v_bkt_2608_,
                    );
                    if v___x_2609_ == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_2588_);
                        crate::leanh::lean_inc(v_size_2587_);
                        v_isSharedCheck_2634_ = (!crate::leanh::lean_is_exclusive(v_m_2584_)) as u8;
                        if v_isSharedCheck_2634_ == 0 {
                            v_unused_2635_ = crate::leanh::lean_ctor_get(v_m_2584_, 1);
                            crate::leanh::lean_dec(v_unused_2635_);
                            v_unused_2636_ = crate::leanh::lean_ctor_get(v_m_2584_, 0);
                            crate::leanh::lean_dec(v_unused_2636_);
                            v___x_2611_ = v_m_2584_;
                            v_isShared_2612_ = v_isSharedCheck_2634_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_2584_);
                            v___x_2611_ = crate::leanh::lean_box(0);
                            v_isShared_2612_ = v_isSharedCheck_2634_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_2586_);
                        crate::leanh::lean_dec(v_a_2585_);
                        crate::leanh::lean_dec_ref(v_inst_2583_);
                        v___x_2637_ = crate::leanh::lean_box((v___x_2609_) as usize);
                        v___x_2638_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2637_);
                        crate::leanh::lean_ctor_set(v___x_2638_, 1, v_m_2584_);
                        return v___x_2638_;
                    }
                }
            }
            1 => {
                v___x_2613_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2614_ = lean_nat_add(v_size_2587_, v___x_2613_);
                crate::leanh::lean_dec(v_size_2587_);
                crate::leanh::lean_inc(v_bkt_2608_);
                v___x_2615_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2615_, 0, v_a_2585_);
                crate::leanh::lean_ctor_set(v___x_2615_, 1, v_b_2586_);
                crate::leanh::lean_ctor_set(v___x_2615_, 2, v_bkt_2608_);
                v_buckets_x27_2616_ = lean_array_uset(v_buckets_2588_, v___x_2607_, v___x_2615_);
                v___x_2617_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2618_ = lean_nat_mul(v_size_x27_2614_, v___x_2617_);
                v___x_2619_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2620_ = lean_nat_div(v___x_2618_, v___x_2619_);
                crate::leanh::lean_dec(v___x_2618_);
                v___x_2621_ = lean_array_get_size(v_buckets_x27_2616_);
                v___x_2622_ = lean_nat_dec_le(v___x_2620_, v___x_2621_);
                crate::leanh::lean_dec(v___x_2620_);
                if v___x_2622_ == 0 {
                    v_val_2623_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2583_,
                        v_buckets_x27_2616_,
                    );
                    if v_isShared_2612_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2611_, 1, v_val_2623_);
                        crate::leanh::lean_ctor_set(v___x_2611_, 0, v_size_x27_2614_);
                        v___x_2625_ = v___x_2611_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2628_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_size_x27_2614_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_val_2623_);
                        v___x_2625_ = v_reuseFailAlloc_2628_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2583_);
                    if v_isShared_2612_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2611_, 1, v_buckets_x27_2616_);
                        crate::leanh::lean_ctor_set(v___x_2611_, 0, v_size_x27_2614_);
                        v___x_2630_ = v___x_2611_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_size_x27_2614_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_buckets_x27_2616_);
                        v___x_2630_ = v_reuseFailAlloc_2633_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2626_ = crate::leanh::lean_box((v___x_2609_) as usize);
                v___x_2627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2627_, 0, v___x_2626_);
                crate::leanh::lean_ctor_set(v___x_2627_, 1, v___x_2625_);
                return v___x_2627_;
            }
            3 => {
                v___x_2631_ = crate::leanh::lean_box((v___x_2609_) as usize);
                v___x_2632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2631_);
                crate::leanh::lean_ctor_set(v___x_2632_, 1, v___x_2630_);
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_containsThenInsertIfNew(
    mut v_00_u03b1_2639_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2640_: *mut crate::leanh::LeanObject,
    mut v_inst_2641_: *mut crate::leanh::LeanObject,
    mut v_inst_2642_: *mut crate::leanh::LeanObject,
    mut v_m_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
    mut v_b_2645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v_val_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_unused_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2646_ = crate::leanh::lean_ctor_get(v_m_2643_, 0);
                v_buckets_2647_ = crate::leanh::lean_ctor_get(v_m_2643_, 1);
                v___x_2648_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2649_ = lean_array_get_size(v_buckets_2647_);
                v___x_2650_ = lean_nat_dec_lt(v___x_2648_, v___x_2649_);
                if v___x_2650_ == 0 {
                    crate::leanh::lean_dec(v_b_2645_);
                    crate::leanh::lean_dec(v_a_2644_);
                    crate::leanh::lean_dec_ref(v_inst_2642_);
                    crate::leanh::lean_dec_ref(v_inst_2641_);
                    v___x_2651_ = crate::leanh::lean_box((v___x_2650_) as usize);
                    v___x_2652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2652_, 0, v___x_2651_);
                    crate::leanh::lean_ctor_set(v___x_2652_, 1, v_m_2643_);
                    return v___x_2652_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_2642_);
                    crate::leanh::lean_inc_n(v_a_2644_, 2);
                    v___x_2653_ = crate::leanh::lean_apply_1(v_inst_2642_, v_a_2644_);
                    v___x_2654_ = 32u64;
                    v___x_2655_ = crate::leanh::lean_unbox_uint64(v___x_2653_);
                    v___x_2656_ = lean_uint64_shift_right(v___x_2655_, v___x_2654_);
                    v___x_2657_ = crate::leanh::lean_unbox_uint64(v___x_2653_);
                    crate::leanh::lean_dec_ref(v___x_2653_);
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
                    crate::leanh::lean_inc(v_bkt_2667_);
                    v___x_2668_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_2641_,
                        v_a_2644_,
                        v_bkt_2667_,
                    );
                    if v___x_2668_ == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_2647_);
                        crate::leanh::lean_inc(v_size_2646_);
                        v_isSharedCheck_2693_ = (!crate::leanh::lean_is_exclusive(v_m_2643_)) as u8;
                        if v_isSharedCheck_2693_ == 0 {
                            v_unused_2694_ = crate::leanh::lean_ctor_get(v_m_2643_, 1);
                            crate::leanh::lean_dec(v_unused_2694_);
                            v_unused_2695_ = crate::leanh::lean_ctor_get(v_m_2643_, 0);
                            crate::leanh::lean_dec(v_unused_2695_);
                            v___x_2670_ = v_m_2643_;
                            v_isShared_2671_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_2643_);
                            v___x_2670_ = crate::leanh::lean_box(0);
                            v_isShared_2671_ = v_isSharedCheck_2693_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_2645_);
                        crate::leanh::lean_dec(v_a_2644_);
                        crate::leanh::lean_dec_ref(v_inst_2642_);
                        v___x_2696_ = crate::leanh::lean_box((v___x_2668_) as usize);
                        v___x_2697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2697_, 0, v___x_2696_);
                        crate::leanh::lean_ctor_set(v___x_2697_, 1, v_m_2643_);
                        return v___x_2697_;
                    }
                }
            }
            1 => {
                v___x_2672_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2673_ = lean_nat_add(v_size_2646_, v___x_2672_);
                crate::leanh::lean_dec(v_size_2646_);
                crate::leanh::lean_inc(v_bkt_2667_);
                v___x_2674_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2674_, 0, v_a_2644_);
                crate::leanh::lean_ctor_set(v___x_2674_, 1, v_b_2645_);
                crate::leanh::lean_ctor_set(v___x_2674_, 2, v_bkt_2667_);
                v_buckets_x27_2675_ = lean_array_uset(v_buckets_2647_, v___x_2666_, v___x_2674_);
                v___x_2676_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2677_ = lean_nat_mul(v_size_x27_2673_, v___x_2676_);
                v___x_2678_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2679_ = lean_nat_div(v___x_2677_, v___x_2678_);
                crate::leanh::lean_dec(v___x_2677_);
                v___x_2680_ = lean_array_get_size(v_buckets_x27_2675_);
                v___x_2681_ = lean_nat_dec_le(v___x_2679_, v___x_2680_);
                crate::leanh::lean_dec(v___x_2679_);
                if v___x_2681_ == 0 {
                    v_val_2682_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2642_,
                        v_buckets_x27_2675_,
                    );
                    if v_isShared_2671_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2670_, 1, v_val_2682_);
                        crate::leanh::lean_ctor_set(v___x_2670_, 0, v_size_x27_2673_);
                        v___x_2684_ = v___x_2670_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_size_x27_2673_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_val_2682_);
                        v___x_2684_ = v_reuseFailAlloc_2687_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2642_);
                    if v_isShared_2671_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2670_, 1, v_buckets_x27_2675_);
                        crate::leanh::lean_ctor_set(v___x_2670_, 0, v_size_x27_2673_);
                        v___x_2689_ = v___x_2670_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_size_x27_2673_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_buckets_x27_2675_);
                        v___x_2689_ = v_reuseFailAlloc_2692_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2685_ = crate::leanh::lean_box((v___x_2668_) as usize);
                v___x_2686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2686_, 0, v___x_2685_);
                crate::leanh::lean_ctor_set(v___x_2686_, 1, v___x_2684_);
                return v___x_2686_;
            }
            3 => {
                v___x_2690_ = crate::leanh::lean_box((v___x_2668_) as usize);
                v___x_2691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                crate::leanh::lean_ctor_set(v___x_2691_, 1, v___x_2689_);
                return v___x_2691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(
    mut v_inst_2698_: *mut crate::leanh::LeanObject,
    mut v_inst_2699_: *mut crate::leanh::LeanObject,
    mut v_m_2700_: *mut crate::leanh::LeanObject,
    mut v_a_2701_: *mut crate::leanh::LeanObject,
    mut v_b_2702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: u8 = 0;
    let mut v_val_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_unused_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2703_ = crate::leanh::lean_ctor_get(v_m_2700_, 0);
                v_buckets_2704_ = crate::leanh::lean_ctor_get(v_m_2700_, 1);
                v___x_2705_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2706_ = lean_array_get_size(v_buckets_2704_);
                v___x_2707_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
                if v___x_2707_ == 0 {
                    crate::leanh::lean_dec(v_b_2702_);
                    crate::leanh::lean_dec(v_a_2701_);
                    crate::leanh::lean_dec_ref(v_inst_2699_);
                    crate::leanh::lean_dec_ref(v_inst_2698_);
                    v___x_2708_ = crate::leanh::lean_box(0);
                    v___x_2709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2709_, 0, v___x_2708_);
                    crate::leanh::lean_ctor_set(v___x_2709_, 1, v_m_2700_);
                    return v___x_2709_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_2699_);
                    crate::leanh::lean_inc_n(v_a_2701_, 2);
                    v___x_2710_ = crate::leanh::lean_apply_1(v_inst_2699_, v_a_2701_);
                    v___x_2711_ = 32u64;
                    v___x_2712_ = crate::leanh::lean_unbox_uint64(v___x_2710_);
                    v___x_2713_ = lean_uint64_shift_right(v___x_2712_, v___x_2711_);
                    v___x_2714_ = crate::leanh::lean_unbox_uint64(v___x_2710_);
                    crate::leanh::lean_dec_ref(v___x_2710_);
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
                    crate::leanh::lean_inc(v_bkt_2724_);
                    v___x_2725_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_2698_,
                        v_a_2701_,
                        v_bkt_2724_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2725_) == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_2704_);
                        crate::leanh::lean_inc(v_size_2703_);
                        v_isSharedCheck_2748_ = (!crate::leanh::lean_is_exclusive(v_m_2700_)) as u8;
                        if v_isSharedCheck_2748_ == 0 {
                            v_unused_2749_ = crate::leanh::lean_ctor_get(v_m_2700_, 1);
                            crate::leanh::lean_dec(v_unused_2749_);
                            v_unused_2750_ = crate::leanh::lean_ctor_get(v_m_2700_, 0);
                            crate::leanh::lean_dec(v_unused_2750_);
                            v___x_2727_ = v_m_2700_;
                            v_isShared_2728_ = v_isSharedCheck_2748_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_2700_);
                            v___x_2727_ = crate::leanh::lean_box(0);
                            v_isShared_2728_ = v_isSharedCheck_2748_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_2702_);
                        crate::leanh::lean_dec(v_a_2701_);
                        crate::leanh::lean_dec_ref(v_inst_2699_);
                        v___x_2751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2751_, 0, v___x_2725_);
                        crate::leanh::lean_ctor_set(v___x_2751_, 1, v_m_2700_);
                        return v___x_2751_;
                    }
                }
            }
            1 => {
                v___x_2729_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2730_ = lean_nat_add(v_size_2703_, v___x_2729_);
                crate::leanh::lean_dec(v_size_2703_);
                crate::leanh::lean_inc(v_bkt_2724_);
                v___x_2731_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2731_, 0, v_a_2701_);
                crate::leanh::lean_ctor_set(v___x_2731_, 1, v_b_2702_);
                crate::leanh::lean_ctor_set(v___x_2731_, 2, v_bkt_2724_);
                v_buckets_x27_2732_ = lean_array_uset(v_buckets_2704_, v___x_2723_, v___x_2731_);
                v___x_2733_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2734_ = lean_nat_mul(v_size_x27_2730_, v___x_2733_);
                v___x_2735_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2736_ = lean_nat_div(v___x_2734_, v___x_2735_);
                crate::leanh::lean_dec(v___x_2734_);
                v___x_2737_ = lean_array_get_size(v_buckets_x27_2732_);
                v___x_2738_ = lean_nat_dec_le(v___x_2736_, v___x_2737_);
                crate::leanh::lean_dec(v___x_2736_);
                if v___x_2738_ == 0 {
                    v_val_2739_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2699_,
                        v_buckets_x27_2732_,
                    );
                    if v_isShared_2728_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2727_, 1, v_val_2739_);
                        crate::leanh::lean_ctor_set(v___x_2727_, 0, v_size_x27_2730_);
                        v___x_2741_ = v___x_2727_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2743_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_size_x27_2730_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_val_2739_);
                        v___x_2741_ = v_reuseFailAlloc_2743_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2699_);
                    if v_isShared_2728_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2727_, 1, v_buckets_x27_2732_);
                        crate::leanh::lean_ctor_set(v___x_2727_, 0, v_size_x27_2730_);
                        v___x_2745_ = v___x_2727_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2747_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_size_x27_2730_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_buckets_x27_2732_);
                        v___x_2745_ = v_reuseFailAlloc_2747_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2742_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2742_, 0, v___x_2725_);
                crate::leanh::lean_ctor_set(v___x_2742_, 1, v___x_2741_);
                return v___x_2742_;
            }
            3 => {
                v___x_2746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2746_, 0, v___x_2725_);
                crate::leanh::lean_ctor_set(v___x_2746_, 1, v___x_2745_);
                return v___x_2746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2752_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2753_: *mut crate::leanh::LeanObject,
    mut v_inst_2754_: *mut crate::leanh::LeanObject,
    mut v_inst_2755_: *mut crate::leanh::LeanObject,
    mut v_m_2756_: *mut crate::leanh::LeanObject,
    mut v_a_2757_: *mut crate::leanh::LeanObject,
    mut v_b_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v_val_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_unused_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2759_ = crate::leanh::lean_ctor_get(v_m_2756_, 0);
                v_buckets_2760_ = crate::leanh::lean_ctor_get(v_m_2756_, 1);
                v___x_2761_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2762_ = lean_array_get_size(v_buckets_2760_);
                v___x_2763_ = lean_nat_dec_lt(v___x_2761_, v___x_2762_);
                if v___x_2763_ == 0 {
                    crate::leanh::lean_dec(v_b_2758_);
                    crate::leanh::lean_dec(v_a_2757_);
                    crate::leanh::lean_dec_ref(v_inst_2755_);
                    crate::leanh::lean_dec_ref(v_inst_2754_);
                    v___x_2764_ = crate::leanh::lean_box(0);
                    v___x_2765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2765_, 0, v___x_2764_);
                    crate::leanh::lean_ctor_set(v___x_2765_, 1, v_m_2756_);
                    return v___x_2765_;
                } else {
                    crate::leanh::lean_inc_ref(v_inst_2755_);
                    crate::leanh::lean_inc_n(v_a_2757_, 2);
                    v___x_2766_ = crate::leanh::lean_apply_1(v_inst_2755_, v_a_2757_);
                    v___x_2767_ = 32u64;
                    v___x_2768_ = crate::leanh::lean_unbox_uint64(v___x_2766_);
                    v___x_2769_ = lean_uint64_shift_right(v___x_2768_, v___x_2767_);
                    v___x_2770_ = crate::leanh::lean_unbox_uint64(v___x_2766_);
                    crate::leanh::lean_dec_ref(v___x_2766_);
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
                    crate::leanh::lean_inc(v_bkt_2780_);
                    v___x_2781_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_2754_,
                        v_a_2757_,
                        v_bkt_2780_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2781_) == 0 {
                        crate::leanh::lean_inc_ref(v_buckets_2760_);
                        crate::leanh::lean_inc(v_size_2759_);
                        v_isSharedCheck_2804_ = (!crate::leanh::lean_is_exclusive(v_m_2756_)) as u8;
                        if v_isSharedCheck_2804_ == 0 {
                            v_unused_2805_ = crate::leanh::lean_ctor_get(v_m_2756_, 1);
                            crate::leanh::lean_dec(v_unused_2805_);
                            v_unused_2806_ = crate::leanh::lean_ctor_get(v_m_2756_, 0);
                            crate::leanh::lean_dec(v_unused_2806_);
                            v___x_2783_ = v_m_2756_;
                            v_isShared_2784_ = v_isSharedCheck_2804_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_m_2756_);
                            v___x_2783_ = crate::leanh::lean_box(0);
                            v_isShared_2784_ = v_isSharedCheck_2804_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_2758_);
                        crate::leanh::lean_dec(v_a_2757_);
                        crate::leanh::lean_dec_ref(v_inst_2755_);
                        v___x_2807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2807_, 0, v___x_2781_);
                        crate::leanh::lean_ctor_set(v___x_2807_, 1, v_m_2756_);
                        return v___x_2807_;
                    }
                }
            }
            1 => {
                v___x_2785_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2786_ = lean_nat_add(v_size_2759_, v___x_2785_);
                crate::leanh::lean_dec(v_size_2759_);
                crate::leanh::lean_inc(v_bkt_2780_);
                v___x_2787_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2787_, 0, v_a_2757_);
                crate::leanh::lean_ctor_set(v___x_2787_, 1, v_b_2758_);
                crate::leanh::lean_ctor_set(v___x_2787_, 2, v_bkt_2780_);
                v_buckets_x27_2788_ = lean_array_uset(v_buckets_2760_, v___x_2779_, v___x_2787_);
                v___x_2789_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2790_ = lean_nat_mul(v_size_x27_2786_, v___x_2789_);
                v___x_2791_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2792_ = lean_nat_div(v___x_2790_, v___x_2791_);
                crate::leanh::lean_dec(v___x_2790_);
                v___x_2793_ = lean_array_get_size(v_buckets_x27_2788_);
                v___x_2794_ = lean_nat_dec_le(v___x_2792_, v___x_2793_);
                crate::leanh::lean_dec(v___x_2792_);
                if v___x_2794_ == 0 {
                    v_val_2795_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2755_,
                        v_buckets_x27_2788_,
                    );
                    if v_isShared_2784_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2783_, 1, v_val_2795_);
                        crate::leanh::lean_ctor_set(v___x_2783_, 0, v_size_x27_2786_);
                        v___x_2797_ = v___x_2783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2799_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_size_x27_2786_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_val_2795_);
                        v___x_2797_ = v_reuseFailAlloc_2799_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2755_);
                    if v_isShared_2784_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2783_, 1, v_buckets_x27_2788_);
                        crate::leanh::lean_ctor_set(v___x_2783_, 0, v_size_x27_2786_);
                        v___x_2801_ = v___x_2783_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_size_x27_2786_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_buckets_x27_2788_);
                        v___x_2801_ = v_reuseFailAlloc_2803_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2798_, 0, v___x_2781_);
                crate::leanh::lean_ctor_set(v___x_2798_, 1, v___x_2797_);
                return v___x_2798_;
            }
            3 => {
                v___x_2802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2802_, 0, v___x_2781_);
                crate::leanh::lean_ctor_set(v___x_2802_, 1, v___x_2801_);
                return v___x_2802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_get_x3f___redArg(
    mut v_beq_2808_: *mut crate::leanh::LeanObject,
    mut v_inst_2809_: *mut crate::leanh::LeanObject,
    mut v_m_2810_: *mut crate::leanh::LeanObject,
    mut v_a_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    v_buckets_2812_ = crate::leanh::lean_ctor_get(v_m_2810_, 1);
    v___x_2813_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2814_ = lean_array_get_size(v_buckets_2812_);
    v___x_2815_ = lean_nat_dec_lt(v___x_2813_, v___x_2814_);
    if v___x_2815_ == 0 {
        let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_2811_);
        crate::leanh::lean_dec_ref(v_inst_2809_);
        crate::leanh::lean_dec_ref(v_beq_2808_);
        v___x_2816_ = crate::leanh::lean_box(0);
        return v___x_2816_;
    } else {
        let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_beq_2818_: *mut crate::leanh::LeanObject,
    mut v_inst_2819_: *mut crate::leanh::LeanObject,
    mut v_m_2820_: *mut crate::leanh::LeanObject,
    mut v_a_2821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2822_ =
        l_Std_HashMap_Raw_get_x3f___redArg(v_beq_2818_, v_inst_2819_, v_m_2820_, v_a_2821_);
    crate::leanh::lean_dec_ref(v_m_2820_);
    return v_res_2822_;
}
pub unsafe fn l_Std_HashMap_Raw_get_x3f(
    mut v_00_u03b1_2823_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2824_: *mut crate::leanh::LeanObject,
    mut v_beq_2825_: *mut crate::leanh::LeanObject,
    mut v_inst_2826_: *mut crate::leanh::LeanObject,
    mut v_m_2827_: *mut crate::leanh::LeanObject,
    mut v_a_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    v_buckets_2829_ = crate::leanh::lean_ctor_get(v_m_2827_, 1);
    v___x_2830_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2831_ = lean_array_get_size(v_buckets_2829_);
    v___x_2832_ = lean_nat_dec_lt(v___x_2830_, v___x_2831_);
    if v___x_2832_ == 0 {
        let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_2828_);
        crate::leanh::lean_dec_ref(v_inst_2826_);
        crate::leanh::lean_dec_ref(v_beq_2825_);
        v___x_2833_ = crate::leanh::lean_box(0);
        return v___x_2833_;
    } else {
        let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2835_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2836_: *mut crate::leanh::LeanObject,
    mut v_beq_2837_: *mut crate::leanh::LeanObject,
    mut v_inst_2838_: *mut crate::leanh::LeanObject,
    mut v_m_2839_: *mut crate::leanh::LeanObject,
    mut v_a_2840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2841_ = l_Std_HashMap_Raw_get_x3f(
        v_00_u03b1_2835_,
        v_00_u03b2_2836_,
        v_beq_2837_,
        v_inst_2838_,
        v_m_2839_,
        v_a_2840_,
    );
    crate::leanh::lean_dec_ref(v_m_2839_);
    return v_res_2841_;
}
pub unsafe fn l_Std_HashMap_Raw_contains___redArg(
    mut v_inst_2842_: *mut crate::leanh::LeanObject,
    mut v_inst_2843_: *mut crate::leanh::LeanObject,
    mut v_m_2844_: *mut crate::leanh::LeanObject,
    mut v_a_2845_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    v_buckets_2846_ = crate::leanh::lean_ctor_get(v_m_2844_, 1);
    v___x_2847_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2848_ = lean_array_get_size(v_buckets_2846_);
    v___x_2849_ = lean_nat_dec_lt(v___x_2847_, v___x_2848_);
    if v___x_2849_ == 0 {
        crate::leanh::lean_dec(v_a_2845_);
        crate::leanh::lean_dec_ref(v_inst_2843_);
        crate::leanh::lean_dec_ref(v_inst_2842_);
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
    mut v_inst_2851_: *mut crate::leanh::LeanObject,
    mut v_inst_2852_: *mut crate::leanh::LeanObject,
    mut v_m_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2855_: u8 = 0;
    let mut v_r_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2855_ =
        l_Std_HashMap_Raw_contains___redArg(v_inst_2851_, v_inst_2852_, v_m_2853_, v_a_2854_);
    crate::leanh::lean_dec_ref(v_m_2853_);
    v_r_2856_ = crate::leanh::lean_box((v_res_2855_) as usize);
    return v_r_2856_;
}
pub unsafe fn l_Std_HashMap_Raw_contains(
    mut v_00_u03b1_2857_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2858_: *mut crate::leanh::LeanObject,
    mut v_inst_2859_: *mut crate::leanh::LeanObject,
    mut v_inst_2860_: *mut crate::leanh::LeanObject,
    mut v_m_2861_: *mut crate::leanh::LeanObject,
    mut v_a_2862_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    v_buckets_2863_ = crate::leanh::lean_ctor_get(v_m_2861_, 1);
    v___x_2864_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2865_ = lean_array_get_size(v_buckets_2863_);
    v___x_2866_ = lean_nat_dec_lt(v___x_2864_, v___x_2865_);
    if v___x_2866_ == 0 {
        crate::leanh::lean_dec(v_a_2862_);
        crate::leanh::lean_dec_ref(v_inst_2860_);
        crate::leanh::lean_dec_ref(v_inst_2859_);
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
    mut v_00_u03b1_2868_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2869_: *mut crate::leanh::LeanObject,
    mut v_inst_2870_: *mut crate::leanh::LeanObject,
    mut v_inst_2871_: *mut crate::leanh::LeanObject,
    mut v_m_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2874_: u8 = 0;
    let mut v_r_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2874_ = l_Std_HashMap_Raw_contains(
        v_00_u03b1_2868_,
        v_00_u03b2_2869_,
        v_inst_2870_,
        v_inst_2871_,
        v_m_2872_,
        v_a_2873_,
    );
    crate::leanh::lean_dec_ref(v_m_2872_);
    v_r_2875_ = crate::leanh::lean_box((v_res_2874_) as usize);
    return v_r_2875_;
}
pub unsafe fn l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(
    mut v_00_u03b1_2876_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2877_: *mut crate::leanh::LeanObject,
    mut v_inst_2878_: *mut crate::leanh::LeanObject,
    mut v_inst_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = crate::leanh::lean_box(0);
    return v___x_2880_;
}
pub unsafe fn l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(
    mut v_00_u03b1_2881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2882_: *mut crate::leanh::LeanObject,
    mut v_inst_2883_: *mut crate::leanh::LeanObject,
    mut v_inst_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2885_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(
        v_00_u03b1_2881_,
        v_00_u03b2_2882_,
        v_inst_2883_,
        v_inst_2884_,
    );
    crate::leanh::lean_dec_ref(v_inst_2884_);
    crate::leanh::lean_dec_ref(v_inst_2883_);
    return v_res_2885_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableMem___redArg(
    mut v_inst_2886_: *mut crate::leanh::LeanObject,
    mut v_inst_2887_: *mut crate::leanh::LeanObject,
    mut v_m_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
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
    mut v_inst_2891_: *mut crate::leanh::LeanObject,
    mut v_inst_2892_: *mut crate::leanh::LeanObject,
    mut v_m_2893_: *mut crate::leanh::LeanObject,
    mut v_a_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2895_: u8 = 0;
    let mut v_r_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_Std_HashMap_Raw_instDecidableMem___redArg(
        v_inst_2891_,
        v_inst_2892_,
        v_m_2893_,
        v_a_2894_,
    );
    crate::leanh::lean_dec_ref(v_m_2893_);
    v_r_2896_ = crate::leanh::lean_box((v_res_2895_) as usize);
    return v_r_2896_;
}
pub unsafe fn l_Std_HashMap_Raw_instDecidableMem(
    mut v_00_u03b1_2897_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2898_: *mut crate::leanh::LeanObject,
    mut v_inst_2899_: *mut crate::leanh::LeanObject,
    mut v_inst_2900_: *mut crate::leanh::LeanObject,
    mut v_m_2901_: *mut crate::leanh::LeanObject,
    mut v_a_2902_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_2904_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2905_: *mut crate::leanh::LeanObject,
    mut v_inst_2906_: *mut crate::leanh::LeanObject,
    mut v_inst_2907_: *mut crate::leanh::LeanObject,
    mut v_m_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2910_: u8 = 0;
    let mut v_r_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2910_ = l_Std_HashMap_Raw_instDecidableMem(
        v_00_u03b1_2904_,
        v_00_u03b2_2905_,
        v_inst_2906_,
        v_inst_2907_,
        v_m_2908_,
        v_a_2909_,
    );
    crate::leanh::lean_dec_ref(v_m_2908_);
    v_r_2911_ = crate::leanh::lean_box((v_res_2910_) as usize);
    return v_r_2911_;
}
pub unsafe fn l_Std_HashMap_Raw_get___redArg(
    mut v_inst_2912_: *mut crate::leanh::LeanObject,
    mut v_inst_2913_: *mut crate::leanh::LeanObject,
    mut v_m_2914_: *mut crate::leanh::LeanObject,
    mut v_a_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_2912_,
        v_inst_2913_,
        v_m_2914_,
        v_a_2915_,
    );
    return v___x_2916_;
}
pub unsafe fn l_Std_HashMap_Raw_get___redArg___boxed(
    mut v_inst_2917_: *mut crate::leanh::LeanObject,
    mut v_inst_2918_: *mut crate::leanh::LeanObject,
    mut v_m_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Std_HashMap_Raw_get___redArg(v_inst_2917_, v_inst_2918_, v_m_2919_, v_a_2920_);
    crate::leanh::lean_dec_ref(v_m_2919_);
    return v_res_2921_;
}
pub unsafe fn l_Std_HashMap_Raw_get(
    mut v_00_u03b1_2922_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2923_: *mut crate::leanh::LeanObject,
    mut v_inst_2924_: *mut crate::leanh::LeanObject,
    mut v_inst_2925_: *mut crate::leanh::LeanObject,
    mut v_m_2926_: *mut crate::leanh::LeanObject,
    mut v_a_2927_: *mut crate::leanh::LeanObject,
    mut v_h_2928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_2924_,
        v_inst_2925_,
        v_m_2926_,
        v_a_2927_,
    );
    return v___x_2929_;
}
pub unsafe fn l_Std_HashMap_Raw_get___boxed(
    mut v_00_u03b1_2930_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2931_: *mut crate::leanh::LeanObject,
    mut v_inst_2932_: *mut crate::leanh::LeanObject,
    mut v_inst_2933_: *mut crate::leanh::LeanObject,
    mut v_m_2934_: *mut crate::leanh::LeanObject,
    mut v_a_2935_: *mut crate::leanh::LeanObject,
    mut v_h_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2937_ = l_Std_HashMap_Raw_get(
        v_00_u03b1_2930_,
        v_00_u03b2_2931_,
        v_inst_2932_,
        v_inst_2933_,
        v_m_2934_,
        v_a_2935_,
        v_h_2936_,
    );
    crate::leanh::lean_dec_ref(v_m_2934_);
    return v_res_2937_;
}
pub unsafe fn l_Std_HashMap_Raw_getD___redArg(
    mut v_inst_2938_: *mut crate::leanh::LeanObject,
    mut v_inst_2939_: *mut crate::leanh::LeanObject,
    mut v_m_2940_: *mut crate::leanh::LeanObject,
    mut v_a_2941_: *mut crate::leanh::LeanObject,
    mut v_fallback_2942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    v_buckets_2943_ = crate::leanh::lean_ctor_get(v_m_2940_, 1);
    v___x_2944_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2945_ = lean_array_get_size(v_buckets_2943_);
    v___x_2946_ = lean_nat_dec_lt(v___x_2944_, v___x_2945_);
    if v___x_2946_ == 0 {
        crate::leanh::lean_dec(v_a_2941_);
        crate::leanh::lean_dec_ref(v_inst_2939_);
        crate::leanh::lean_dec_ref(v_inst_2938_);
        crate::leanh::lean_inc(v_fallback_2942_);
        return v_fallback_2942_;
    } else {
        let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2948_: *mut crate::leanh::LeanObject,
    mut v_inst_2949_: *mut crate::leanh::LeanObject,
    mut v_m_2950_: *mut crate::leanh::LeanObject,
    mut v_a_2951_: *mut crate::leanh::LeanObject,
    mut v_fallback_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Std_HashMap_Raw_getD___redArg(
        v_inst_2948_,
        v_inst_2949_,
        v_m_2950_,
        v_a_2951_,
        v_fallback_2952_,
    );
    crate::leanh::lean_dec(v_fallback_2952_);
    crate::leanh::lean_dec_ref(v_m_2950_);
    return v_res_2953_;
}
pub unsafe fn l_Std_HashMap_Raw_getD(
    mut v_00_u03b1_2954_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2955_: *mut crate::leanh::LeanObject,
    mut v_inst_2956_: *mut crate::leanh::LeanObject,
    mut v_inst_2957_: *mut crate::leanh::LeanObject,
    mut v_m_2958_: *mut crate::leanh::LeanObject,
    mut v_a_2959_: *mut crate::leanh::LeanObject,
    mut v_fallback_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    v_buckets_2961_ = crate::leanh::lean_ctor_get(v_m_2958_, 1);
    v___x_2962_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2963_ = lean_array_get_size(v_buckets_2961_);
    v___x_2964_ = lean_nat_dec_lt(v___x_2962_, v___x_2963_);
    if v___x_2964_ == 0 {
        crate::leanh::lean_dec(v_a_2959_);
        crate::leanh::lean_dec_ref(v_inst_2957_);
        crate::leanh::lean_dec_ref(v_inst_2956_);
        crate::leanh::lean_inc(v_fallback_2960_);
        return v_fallback_2960_;
    } else {
        let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2966_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2967_: *mut crate::leanh::LeanObject,
    mut v_inst_2968_: *mut crate::leanh::LeanObject,
    mut v_inst_2969_: *mut crate::leanh::LeanObject,
    mut v_m_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_fallback_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2973_ = l_Std_HashMap_Raw_getD(
        v_00_u03b1_2966_,
        v_00_u03b2_2967_,
        v_inst_2968_,
        v_inst_2969_,
        v_m_2970_,
        v_a_2971_,
        v_fallback_2972_,
    );
    crate::leanh::lean_dec(v_fallback_2972_);
    crate::leanh::lean_dec_ref(v_m_2970_);
    return v_res_2973_;
}
pub unsafe fn l_Std_HashMap_Raw_get_x21___redArg(
    mut v_inst_2974_: *mut crate::leanh::LeanObject,
    mut v_inst_2975_: *mut crate::leanh::LeanObject,
    mut v_inst_2976_: *mut crate::leanh::LeanObject,
    mut v_m_2977_: *mut crate::leanh::LeanObject,
    mut v_a_2978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    v_buckets_2979_ = crate::leanh::lean_ctor_get(v_m_2977_, 1);
    v___x_2980_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2981_ = lean_array_get_size(v_buckets_2979_);
    v___x_2982_ = lean_nat_dec_lt(v___x_2980_, v___x_2981_);
    if v___x_2982_ == 0 {
        crate::leanh::lean_dec(v_a_2978_);
        crate::leanh::lean_dec_ref(v_inst_2975_);
        crate::leanh::lean_dec_ref(v_inst_2974_);
        crate::leanh::lean_inc(v_inst_2976_);
        return v_inst_2976_;
    } else {
        let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2984_: *mut crate::leanh::LeanObject,
    mut v_inst_2985_: *mut crate::leanh::LeanObject,
    mut v_inst_2986_: *mut crate::leanh::LeanObject,
    mut v_m_2987_: *mut crate::leanh::LeanObject,
    mut v_a_2988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2989_ = l_Std_HashMap_Raw_get_x21___redArg(
        v_inst_2984_,
        v_inst_2985_,
        v_inst_2986_,
        v_m_2987_,
        v_a_2988_,
    );
    crate::leanh::lean_dec_ref(v_m_2987_);
    crate::leanh::lean_dec(v_inst_2986_);
    return v_res_2989_;
}
pub unsafe fn l_Std_HashMap_Raw_get_x21(
    mut v_00_u03b1_2990_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2991_: *mut crate::leanh::LeanObject,
    mut v_inst_2992_: *mut crate::leanh::LeanObject,
    mut v_inst_2993_: *mut crate::leanh::LeanObject,
    mut v_inst_2994_: *mut crate::leanh::LeanObject,
    mut v_m_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    v_buckets_2997_ = crate::leanh::lean_ctor_get(v_m_2995_, 1);
    v___x_2998_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2999_ = lean_array_get_size(v_buckets_2997_);
    v___x_3000_ = lean_nat_dec_lt(v___x_2998_, v___x_2999_);
    if v___x_3000_ == 0 {
        crate::leanh::lean_dec(v_a_2996_);
        crate::leanh::lean_dec_ref(v_inst_2993_);
        crate::leanh::lean_dec_ref(v_inst_2992_);
        crate::leanh::lean_inc(v_inst_2994_);
        return v_inst_2994_;
    } else {
        let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3002_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3003_: *mut crate::leanh::LeanObject,
    mut v_inst_3004_: *mut crate::leanh::LeanObject,
    mut v_inst_3005_: *mut crate::leanh::LeanObject,
    mut v_inst_3006_: *mut crate::leanh::LeanObject,
    mut v_m_3007_: *mut crate::leanh::LeanObject,
    mut v_a_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3009_ = l_Std_HashMap_Raw_get_x21(
        v_00_u03b1_3002_,
        v_00_u03b2_3003_,
        v_inst_3004_,
        v_inst_3005_,
        v_inst_3006_,
        v_m_3007_,
        v_a_3008_,
    );
    crate::leanh::lean_dec_ref(v_m_3007_);
    crate::leanh::lean_dec(v_inst_3006_);
    return v_res_3009_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(
    mut v_inst_3010_: *mut crate::leanh::LeanObject,
    mut v_inst_3011_: *mut crate::leanh::LeanObject,
    mut v_m_3012_: *mut crate::leanh::LeanObject,
    mut v_a_3013_: *mut crate::leanh::LeanObject,
    mut v_h_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_3010_,
        v_inst_3011_,
        v_m_3012_,
        v_a_3013_,
    );
    return v___x_3015_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(
    mut v_inst_3016_: *mut crate::leanh::LeanObject,
    mut v_inst_3017_: *mut crate::leanh::LeanObject,
    mut v_m_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_h_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(
        v_inst_3016_,
        v_inst_3017_,
        v_m_3018_,
        v_a_3019_,
        v_h_3020_,
    );
    crate::leanh::lean_dec_ref(v_m_3018_);
    return v_res_3021_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(
    mut v_inst_3022_: *mut crate::leanh::LeanObject,
    mut v_inst_3023_: *mut crate::leanh::LeanObject,
    mut v_m_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: u8 = 0;
    v_buckets_3026_ = crate::leanh::lean_ctor_get(v_m_3024_, 1);
    v___x_3027_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3028_ = lean_array_get_size(v_buckets_3026_);
    v___x_3029_ = lean_nat_dec_lt(v___x_3027_, v___x_3028_);
    if v___x_3029_ == 0 {
        let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3025_);
        crate::leanh::lean_dec_ref(v_inst_3023_);
        crate::leanh::lean_dec_ref(v_inst_3022_);
        v___x_3030_ = crate::leanh::lean_box(0);
        return v___x_3030_;
    } else {
        let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3032_: *mut crate::leanh::LeanObject,
    mut v_inst_3033_: *mut crate::leanh::LeanObject,
    mut v_m_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3036_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(
        v_inst_3032_,
        v_inst_3033_,
        v_m_3034_,
        v_a_3035_,
    );
    crate::leanh::lean_dec_ref(v_m_3034_);
    return v_res_3036_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(
    mut v_inst_3037_: *mut crate::leanh::LeanObject,
    mut v_inst_3038_: *mut crate::leanh::LeanObject,
    mut v_inst_3039_: *mut crate::leanh::LeanObject,
    mut v_m_3040_: *mut crate::leanh::LeanObject,
    mut v_a_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    v_buckets_3042_ = crate::leanh::lean_ctor_get(v_m_3040_, 1);
    v___x_3043_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3044_ = lean_array_get_size(v_buckets_3042_);
    v___x_3045_ = lean_nat_dec_lt(v___x_3043_, v___x_3044_);
    if v___x_3045_ == 0 {
        crate::leanh::lean_dec(v_a_3041_);
        crate::leanh::lean_dec_ref(v_inst_3038_);
        crate::leanh::lean_dec_ref(v_inst_3037_);
        crate::leanh::lean_inc(v_inst_3039_);
        return v_inst_3039_;
    } else {
        let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3047_: *mut crate::leanh::LeanObject,
    mut v_inst_3048_: *mut crate::leanh::LeanObject,
    mut v_inst_3049_: *mut crate::leanh::LeanObject,
    mut v_m_3050_: *mut crate::leanh::LeanObject,
    mut v_a_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3052_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(
        v_inst_3047_,
        v_inst_3048_,
        v_inst_3049_,
        v_m_3050_,
        v_a_3051_,
    );
    crate::leanh::lean_dec_ref(v_m_3050_);
    crate::leanh::lean_dec(v_inst_3049_);
    return v_res_3052_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(
    mut v_inst_3053_: *mut crate::leanh::LeanObject,
    mut v_inst_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_3054_, 2);
    crate::leanh::lean_inc_ref_n(v_inst_3053_, 2);
    v___f_3055_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3055_, 0, v_inst_3053_);
    crate::leanh::lean_closure_set(v___f_3055_, 1, v_inst_3054_);
    v___f_3056_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3056_, 0, v_inst_3053_);
    crate::leanh::lean_closure_set(v___f_3056_, 1, v_inst_3054_);
    v___f_3057_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3057_, 0, v_inst_3053_);
    crate::leanh::lean_closure_set(v___f_3057_, 1, v_inst_3054_);
    v___x_3058_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3058_, 0, v___f_3055_);
    crate::leanh::lean_ctor_set(v___x_3058_, 1, v___f_3056_);
    crate::leanh::lean_ctor_set(v___x_3058_, 2, v___f_3057_);
    return v___x_3058_;
}
pub unsafe fn l_Std_HashMap_Raw_instGetElem_x3fMem(
    mut v_00_u03b1_3059_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3060_: *mut crate::leanh::LeanObject,
    mut v_inst_3061_: *mut crate::leanh::LeanObject,
    mut v_inst_3062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3063_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_3061_, v_inst_3062_);
    return v___x_3063_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x3f___redArg(
    mut v_inst_3064_: *mut crate::leanh::LeanObject,
    mut v_inst_3065_: *mut crate::leanh::LeanObject,
    mut v_m_3066_: *mut crate::leanh::LeanObject,
    mut v_a_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    v_buckets_3068_ = crate::leanh::lean_ctor_get(v_m_3066_, 1);
    v___x_3069_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3070_ = lean_array_get_size(v_buckets_3068_);
    v___x_3071_ = lean_nat_dec_lt(v___x_3069_, v___x_3070_);
    if v___x_3071_ == 0 {
        let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3067_);
        crate::leanh::lean_dec_ref(v_inst_3065_);
        crate::leanh::lean_dec_ref(v_inst_3064_);
        v___x_3072_ = crate::leanh::lean_box(0);
        return v___x_3072_;
    } else {
        let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3074_: *mut crate::leanh::LeanObject,
    mut v_inst_3075_: *mut crate::leanh::LeanObject,
    mut v_m_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3078_ =
        l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_3074_, v_inst_3075_, v_m_3076_, v_a_3077_);
    crate::leanh::lean_dec_ref(v_m_3076_);
    return v_res_3078_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x3f(
    mut v_00_u03b1_3079_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3080_: *mut crate::leanh::LeanObject,
    mut v_inst_3081_: *mut crate::leanh::LeanObject,
    mut v_inst_3082_: *mut crate::leanh::LeanObject,
    mut v_m_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: u8 = 0;
    v_buckets_3085_ = crate::leanh::lean_ctor_get(v_m_3083_, 1);
    v___x_3086_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3087_ = lean_array_get_size(v_buckets_3085_);
    v___x_3088_ = lean_nat_dec_lt(v___x_3086_, v___x_3087_);
    if v___x_3088_ == 0 {
        let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_3084_);
        crate::leanh::lean_dec_ref(v_inst_3082_);
        crate::leanh::lean_dec_ref(v_inst_3081_);
        v___x_3089_ = crate::leanh::lean_box(0);
        return v___x_3089_;
    } else {
        let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3091_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3092_: *mut crate::leanh::LeanObject,
    mut v_inst_3093_: *mut crate::leanh::LeanObject,
    mut v_inst_3094_: *mut crate::leanh::LeanObject,
    mut v_m_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Std_HashMap_Raw_getKey_x3f(
        v_00_u03b1_3091_,
        v_00_u03b2_3092_,
        v_inst_3093_,
        v_inst_3094_,
        v_m_3095_,
        v_a_3096_,
    );
    crate::leanh::lean_dec_ref(v_m_3095_);
    return v_res_3097_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey___redArg(
    mut v_inst_3098_: *mut crate::leanh::LeanObject,
    mut v_inst_3099_: *mut crate::leanh::LeanObject,
    mut v_m_3100_: *mut crate::leanh::LeanObject,
    mut v_a_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3098_,
        v_inst_3099_,
        v_m_3100_,
        v_a_3101_,
    );
    return v___x_3102_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey___redArg___boxed(
    mut v_inst_3103_: *mut crate::leanh::LeanObject,
    mut v_inst_3104_: *mut crate::leanh::LeanObject,
    mut v_m_3105_: *mut crate::leanh::LeanObject,
    mut v_a_3106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3107_ =
        l_Std_HashMap_Raw_getKey___redArg(v_inst_3103_, v_inst_3104_, v_m_3105_, v_a_3106_);
    crate::leanh::lean_dec_ref(v_m_3105_);
    return v_res_3107_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey(
    mut v_00_u03b1_3108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3109_: *mut crate::leanh::LeanObject,
    mut v_inst_3110_: *mut crate::leanh::LeanObject,
    mut v_inst_3111_: *mut crate::leanh::LeanObject,
    mut v_m_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_h_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3110_,
        v_inst_3111_,
        v_m_3112_,
        v_a_3113_,
    );
    return v___x_3115_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey___boxed(
    mut v_00_u03b1_3116_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3117_: *mut crate::leanh::LeanObject,
    mut v_inst_3118_: *mut crate::leanh::LeanObject,
    mut v_inst_3119_: *mut crate::leanh::LeanObject,
    mut v_m_3120_: *mut crate::leanh::LeanObject,
    mut v_a_3121_: *mut crate::leanh::LeanObject,
    mut v_h_3122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3123_ = l_Std_HashMap_Raw_getKey(
        v_00_u03b1_3116_,
        v_00_u03b2_3117_,
        v_inst_3118_,
        v_inst_3119_,
        v_m_3120_,
        v_a_3121_,
        v_h_3122_,
    );
    crate::leanh::lean_dec_ref(v_m_3120_);
    return v_res_3123_;
}
pub unsafe fn l_Std_HashMap_Raw_getKeyD___redArg(
    mut v_inst_3124_: *mut crate::leanh::LeanObject,
    mut v_inst_3125_: *mut crate::leanh::LeanObject,
    mut v_m_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_fallback_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    v_buckets_3129_ = crate::leanh::lean_ctor_get(v_m_3126_, 1);
    v___x_3130_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3131_ = lean_array_get_size(v_buckets_3129_);
    v___x_3132_ = lean_nat_dec_lt(v___x_3130_, v___x_3131_);
    if v___x_3132_ == 0 {
        crate::leanh::lean_dec(v_a_3127_);
        crate::leanh::lean_dec_ref(v_inst_3125_);
        crate::leanh::lean_dec_ref(v_inst_3124_);
        crate::leanh::lean_inc(v_fallback_3128_);
        return v_fallback_3128_;
    } else {
        let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3134_: *mut crate::leanh::LeanObject,
    mut v_inst_3135_: *mut crate::leanh::LeanObject,
    mut v_m_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_fallback_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_Std_HashMap_Raw_getKeyD___redArg(
        v_inst_3134_,
        v_inst_3135_,
        v_m_3136_,
        v_a_3137_,
        v_fallback_3138_,
    );
    crate::leanh::lean_dec(v_fallback_3138_);
    crate::leanh::lean_dec_ref(v_m_3136_);
    return v_res_3139_;
}
pub unsafe fn l_Std_HashMap_Raw_getKeyD(
    mut v_00_u03b1_3140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3141_: *mut crate::leanh::LeanObject,
    mut v_inst_3142_: *mut crate::leanh::LeanObject,
    mut v_inst_3143_: *mut crate::leanh::LeanObject,
    mut v_m_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_fallback_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    v_buckets_3147_ = crate::leanh::lean_ctor_get(v_m_3144_, 1);
    v___x_3148_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3149_ = lean_array_get_size(v_buckets_3147_);
    v___x_3150_ = lean_nat_dec_lt(v___x_3148_, v___x_3149_);
    if v___x_3150_ == 0 {
        crate::leanh::lean_dec(v_a_3145_);
        crate::leanh::lean_dec_ref(v_inst_3143_);
        crate::leanh::lean_dec_ref(v_inst_3142_);
        crate::leanh::lean_inc(v_fallback_3146_);
        return v_fallback_3146_;
    } else {
        let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3152_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3153_: *mut crate::leanh::LeanObject,
    mut v_inst_3154_: *mut crate::leanh::LeanObject,
    mut v_inst_3155_: *mut crate::leanh::LeanObject,
    mut v_m_3156_: *mut crate::leanh::LeanObject,
    mut v_a_3157_: *mut crate::leanh::LeanObject,
    mut v_fallback_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_Std_HashMap_Raw_getKeyD(
        v_00_u03b1_3152_,
        v_00_u03b2_3153_,
        v_inst_3154_,
        v_inst_3155_,
        v_m_3156_,
        v_a_3157_,
        v_fallback_3158_,
    );
    crate::leanh::lean_dec(v_fallback_3158_);
    crate::leanh::lean_dec_ref(v_m_3156_);
    return v_res_3159_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x21___redArg(
    mut v_inst_3160_: *mut crate::leanh::LeanObject,
    mut v_inst_3161_: *mut crate::leanh::LeanObject,
    mut v_inst_3162_: *mut crate::leanh::LeanObject,
    mut v_m_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    v_buckets_3165_ = crate::leanh::lean_ctor_get(v_m_3163_, 1);
    v___x_3166_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3167_ = lean_array_get_size(v_buckets_3165_);
    v___x_3168_ = lean_nat_dec_lt(v___x_3166_, v___x_3167_);
    if v___x_3168_ == 0 {
        crate::leanh::lean_dec(v_a_3164_);
        crate::leanh::lean_dec_ref(v_inst_3161_);
        crate::leanh::lean_dec_ref(v_inst_3160_);
        crate::leanh::lean_inc(v_inst_3162_);
        return v_inst_3162_;
    } else {
        let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3170_: *mut crate::leanh::LeanObject,
    mut v_inst_3171_: *mut crate::leanh::LeanObject,
    mut v_inst_3172_: *mut crate::leanh::LeanObject,
    mut v_m_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_Std_HashMap_Raw_getKey_x21___redArg(
        v_inst_3170_,
        v_inst_3171_,
        v_inst_3172_,
        v_m_3173_,
        v_a_3174_,
    );
    crate::leanh::lean_dec_ref(v_m_3173_);
    crate::leanh::lean_dec(v_inst_3172_);
    return v_res_3175_;
}
pub unsafe fn l_Std_HashMap_Raw_getKey_x21(
    mut v_00_u03b1_3176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3177_: *mut crate::leanh::LeanObject,
    mut v_inst_3178_: *mut crate::leanh::LeanObject,
    mut v_inst_3179_: *mut crate::leanh::LeanObject,
    mut v_inst_3180_: *mut crate::leanh::LeanObject,
    mut v_m_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    v_buckets_3183_ = crate::leanh::lean_ctor_get(v_m_3181_, 1);
    v___x_3184_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3185_ = lean_array_get_size(v_buckets_3183_);
    v___x_3186_ = lean_nat_dec_lt(v___x_3184_, v___x_3185_);
    if v___x_3186_ == 0 {
        crate::leanh::lean_dec(v_a_3182_);
        crate::leanh::lean_dec_ref(v_inst_3179_);
        crate::leanh::lean_dec_ref(v_inst_3178_);
        crate::leanh::lean_inc(v_inst_3180_);
        return v_inst_3180_;
    } else {
        let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3188_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3189_: *mut crate::leanh::LeanObject,
    mut v_inst_3190_: *mut crate::leanh::LeanObject,
    mut v_inst_3191_: *mut crate::leanh::LeanObject,
    mut v_inst_3192_: *mut crate::leanh::LeanObject,
    mut v_m_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_Std_HashMap_Raw_getKey_x21(
        v_00_u03b1_3188_,
        v_00_u03b2_3189_,
        v_inst_3190_,
        v_inst_3191_,
        v_inst_3192_,
        v_m_3193_,
        v_a_3194_,
    );
    crate::leanh::lean_dec_ref(v_m_3193_);
    crate::leanh::lean_dec(v_inst_3192_);
    return v_res_3195_;
}
pub unsafe fn l_Std_HashMap_Raw_erase___redArg(
    mut v_inst_3196_: *mut crate::leanh::LeanObject,
    mut v_inst_3197_: *mut crate::leanh::LeanObject,
    mut v_m_3198_: *mut crate::leanh::LeanObject,
    mut v_a_3199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    v_buckets_3200_ = crate::leanh::lean_ctor_get(v_m_3198_, 1);
    v___x_3201_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3202_ = lean_array_get_size(v_buckets_3200_);
    v___x_3203_ = lean_nat_dec_lt(v___x_3201_, v___x_3202_);
    if v___x_3203_ == 0 {
        crate::leanh::lean_dec(v_a_3199_);
        crate::leanh::lean_dec_ref(v_inst_3197_);
        crate::leanh::lean_dec_ref(v_inst_3196_);
        return v_m_3198_;
    } else {
        let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3205_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3206_: *mut crate::leanh::LeanObject,
    mut v_inst_3207_: *mut crate::leanh::LeanObject,
    mut v_inst_3208_: *mut crate::leanh::LeanObject,
    mut v_m_3209_: *mut crate::leanh::LeanObject,
    mut v_a_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    v_buckets_3211_ = crate::leanh::lean_ctor_get(v_m_3209_, 1);
    v___x_3212_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3213_ = lean_array_get_size(v_buckets_3211_);
    v___x_3214_ = lean_nat_dec_lt(v___x_3212_, v___x_3213_);
    if v___x_3214_ == 0 {
        crate::leanh::lean_dec(v_a_3210_);
        crate::leanh::lean_dec_ref(v_inst_3208_);
        crate::leanh::lean_dec_ref(v_inst_3207_);
        return v_m_3209_;
    } else {
        let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_3217_ = crate::leanh::lean_ctor_get(v_m_3216_, 0);
    crate::leanh::lean_inc(v_size_3217_);
    return v_size_3217_;
}
pub unsafe fn l_Std_HashMap_Raw_size___redArg___boxed(
    mut v_m_3218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3219_ = l_Std_HashMap_Raw_size___redArg(v_m_3218_);
    crate::leanh::lean_dec_ref(v_m_3218_);
    return v_res_3219_;
}
pub unsafe fn l_Std_HashMap_Raw_size(
    mut v_00_u03b1_3220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3221_: *mut crate::leanh::LeanObject,
    mut v_m_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_3223_ = crate::leanh::lean_ctor_get(v_m_3222_, 0);
    crate::leanh::lean_inc(v_size_3223_);
    return v_size_3223_;
}
pub unsafe fn l_Std_HashMap_Raw_size___boxed(
    mut v_00_u03b1_3224_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3225_: *mut crate::leanh::LeanObject,
    mut v_m_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3227_ = l_Std_HashMap_Raw_size(v_00_u03b1_3224_, v_00_u03b2_3225_, v_m_3226_);
    crate::leanh::lean_dec_ref(v_m_3226_);
    return v_res_3227_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty___redArg(
    mut v_m_3228_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    v_size_3229_ = crate::leanh::lean_ctor_get(v_m_3228_, 0);
    v___x_3230_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3231_ = lean_nat_dec_eq(v_size_3229_, v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty___redArg___boxed(
    mut v_m_3232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3233_: u8 = 0;
    let mut v_r_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3233_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_3232_);
    crate::leanh::lean_dec_ref(v_m_3232_);
    v_r_3234_ = crate::leanh::lean_box((v_res_3233_) as usize);
    return v_r_3234_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty(
    mut v_00_u03b1_3235_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3236_: *mut crate::leanh::LeanObject,
    mut v_m_3237_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    v_size_3238_ = crate::leanh::lean_ctor_get(v_m_3237_, 0);
    v___x_3239_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3240_ = lean_nat_dec_eq(v_size_3238_, v___x_3239_);
    return v___x_3240_;
}
pub unsafe fn l_Std_HashMap_Raw_isEmpty___boxed(
    mut v_00_u03b1_3241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3242_: *mut crate::leanh::LeanObject,
    mut v_m_3243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3244_: u8 = 0;
    let mut v_r_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3244_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_3241_, v_00_u03b2_3242_, v_m_3243_);
    crate::leanh::lean_dec_ref(v_m_3243_);
    v_r_3245_ = crate::leanh::lean_box((v_res_3244_) as usize);
    return v_r_3245_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg___lam__0(
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_b_3247_: *mut crate::leanh::LeanObject,
    mut v_d_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3249_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3249_, 0, v_a_3246_);
    crate::leanh::lean_ctor_set(v___x_3249_, 1, v_d_3248_);
    return v___x_3249_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(
    mut v_a_3250_: *mut crate::leanh::LeanObject,
    mut v_b_3251_: *mut crate::leanh::LeanObject,
    mut v_d_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3253_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_3250_, v_b_3251_, v_d_3252_);
    crate::leanh::lean_dec(v_b_3251_);
    return v_res_3253_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg___lam__1(
    mut v___x_3254_: *mut crate::leanh::LeanObject,
    mut v___f_3255_: *mut crate::leanh::LeanObject,
    mut v_l_3256_: *mut crate::leanh::LeanObject,
    mut v_acc_3257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_3254_,
        v___f_3255_,
        v_acc_3257_,
        v_l_3256_,
    );
    return v___x_3258_;
}
pub unsafe fn l_Std_HashMap_Raw_keys___redArg(
    mut v_m_3282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    v___x_3283_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3284_ = crate::leanh::lean_ctor_get(v_m_3282_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3284_);
    crate::leanh::lean_dec_ref(v_m_3282_);
    v___x_3285_ = crate::leanh::lean_box(0);
    v___x_3286_ = lean_array_get_size(v_buckets_3284_);
    v___x_3287_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3288_ = lean_nat_dec_lt(v___x_3287_, v___x_3286_);
    if v___x_3288_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_3284_);
        return v___x_3285_;
    } else {
        let mut v___f_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3290_: usize = 0;
        let mut v___x_3291_: usize = 0;
        let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3289_ = l_Std_HashMap_Raw_keys___redArg___closed__11;
        v___x_3290_ = lean_usize_of_nat(v___x_3286_);
        v___x_3291_ = 0usize;
        v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3294_: *mut crate::leanh::LeanObject,
    mut v_m_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: u8 = 0;
    v___x_3296_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3297_ = crate::leanh::lean_ctor_get(v_m_3295_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3297_);
    crate::leanh::lean_dec_ref(v_m_3295_);
    v___x_3298_ = crate::leanh::lean_box(0);
    v___x_3299_ = lean_array_get_size(v_buckets_3297_);
    v___x_3300_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3301_ = lean_nat_dec_lt(v___x_3300_, v___x_3299_);
    if v___x_3301_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_3297_);
        return v___x_3298_;
    } else {
        let mut v___f_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3303_: usize = 0;
        let mut v___x_3304_: usize = 0;
        let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3302_ = l_Std_HashMap_Raw_keys___redArg___closed__11;
        v___x_3303_ = lean_usize_of_nat(v___x_3299_);
        v___x_3304_ = 0usize;
        v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
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
    mut v_inst_3310_: *mut crate::leanh::LeanObject,
    mut v_inst_3311_: *mut crate::leanh::LeanObject,
    mut v_l_3312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    v___x_3313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3314_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3314_ == 0 {
        crate::leanh::lean_dec(v_l_3312_);
        crate::leanh::lean_dec_ref(v_inst_3311_);
        crate::leanh::lean_dec_ref(v_inst_3310_);
        return v___x_3313_;
    } else {
        let mut v___f_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3318_: *mut crate::leanh::LeanObject,
    mut v_inst_3319_: *mut crate::leanh::LeanObject,
    mut v_inst_3320_: *mut crate::leanh::LeanObject,
    mut v_l_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: u8 = 0;
    v___x_3322_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3323_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3323_ == 0 {
        crate::leanh::lean_dec(v_l_3321_);
        crate::leanh::lean_dec_ref(v_inst_3320_);
        crate::leanh::lean_dec_ref(v_inst_3319_);
        return v___x_3322_;
    } else {
        let mut v___f_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3326_: *mut crate::leanh::LeanObject,
    mut v_inst_3327_: *mut crate::leanh::LeanObject,
    mut v_l_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: u8 = 0;
    v___x_3329_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3330_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3330_ == 0 {
        crate::leanh::lean_dec(v_l_3328_);
        crate::leanh::lean_dec_ref(v_inst_3327_);
        crate::leanh::lean_dec_ref(v_inst_3326_);
        return v___x_3329_;
    } else {
        let mut v___f_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3333_: *mut crate::leanh::LeanObject,
    mut v_inst_3334_: *mut crate::leanh::LeanObject,
    mut v_inst_3335_: *mut crate::leanh::LeanObject,
    mut v_l_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    v___x_3337_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3338_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3338_ == 0 {
        crate::leanh::lean_dec(v_l_3336_);
        crate::leanh::lean_dec_ref(v_inst_3335_);
        crate::leanh::lean_dec_ref(v_inst_3334_);
        return v___x_3337_;
    } else {
        let mut v___f_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3345_: *mut crate::leanh::LeanObject,
    mut v_inst_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: u8 = 0;
    v___x_3348_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3349_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3349_ == 0 {
        crate::leanh::lean_dec_ref(v_a_3347_);
        crate::leanh::lean_dec_ref(v_inst_3346_);
        crate::leanh::lean_dec_ref(v_inst_3345_);
        return v___x_3348_;
    } else {
        let mut v___f_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3352_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3353_: *mut crate::leanh::LeanObject,
    mut v_inst_3354_: *mut crate::leanh::LeanObject,
    mut v_inst_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    v___x_3357_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_3358_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_3358_ == 0 {
        crate::leanh::lean_dec_ref(v_a_3356_);
        crate::leanh::lean_dec_ref(v_inst_3355_);
        crate::leanh::lean_dec_ref(v_inst_3354_);
        return v___x_3357_;
    } else {
        let mut v___f_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3361_: *mut crate::leanh::LeanObject,
    mut v_inst_3362_: *mut crate::leanh::LeanObject,
    mut v_m_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
    mut v_f_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: u8 = 0;
    v_buckets_3366_ = crate::leanh::lean_ctor_get(v_m_3363_, 1);
    v___x_3367_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3368_ = lean_array_get_size(v_buckets_3366_);
    v___x_3369_ = lean_nat_dec_lt(v___x_3367_, v___x_3368_);
    if v___x_3369_ == 0 {
        let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_3365_);
        crate::leanh::lean_dec(v_a_3364_);
        crate::leanh::lean_dec_ref(v_m_3363_);
        crate::leanh::lean_dec_ref(v_inst_3362_);
        crate::leanh::lean_dec_ref(v_inst_3361_);
        v___x_3370_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3370_;
    } else {
        let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3373_: *mut crate::leanh::LeanObject,
    mut v_inst_3374_: *mut crate::leanh::LeanObject,
    mut v_inst_3375_: *mut crate::leanh::LeanObject,
    mut v_inst_3376_: *mut crate::leanh::LeanObject,
    mut v_m_3377_: *mut crate::leanh::LeanObject,
    mut v_a_3378_: *mut crate::leanh::LeanObject,
    mut v_f_3379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    v_buckets_3380_ = crate::leanh::lean_ctor_get(v_m_3377_, 1);
    v___x_3381_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3382_ = lean_array_get_size(v_buckets_3380_);
    v___x_3383_ = lean_nat_dec_lt(v___x_3381_, v___x_3382_);
    if v___x_3383_ == 0 {
        let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_3379_);
        crate::leanh::lean_dec(v_a_3378_);
        crate::leanh::lean_dec_ref(v_m_3377_);
        crate::leanh::lean_dec_ref(v_inst_3376_);
        crate::leanh::lean_dec_ref(v_inst_3374_);
        v___x_3384_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3384_;
    } else {
        let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3386_: *mut crate::leanh::LeanObject,
    mut v_inst_3387_: *mut crate::leanh::LeanObject,
    mut v_m_3388_: *mut crate::leanh::LeanObject,
    mut v_a_3389_: *mut crate::leanh::LeanObject,
    mut v_f_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    v_buckets_3391_ = crate::leanh::lean_ctor_get(v_m_3388_, 1);
    v___x_3392_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3393_ = lean_array_get_size(v_buckets_3391_);
    v___x_3394_ = lean_nat_dec_lt(v___x_3392_, v___x_3393_);
    if v___x_3394_ == 0 {
        let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_3390_);
        crate::leanh::lean_dec(v_a_3389_);
        crate::leanh::lean_dec_ref(v_m_3388_);
        crate::leanh::lean_dec_ref(v_inst_3387_);
        crate::leanh::lean_dec_ref(v_inst_3386_);
        v___x_3395_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3395_;
    } else {
        let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3398_: *mut crate::leanh::LeanObject,
    mut v_inst_3399_: *mut crate::leanh::LeanObject,
    mut v_inst_3400_: *mut crate::leanh::LeanObject,
    mut v_inst_3401_: *mut crate::leanh::LeanObject,
    mut v_m_3402_: *mut crate::leanh::LeanObject,
    mut v_a_3403_: *mut crate::leanh::LeanObject,
    mut v_f_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: u8 = 0;
    v_buckets_3405_ = crate::leanh::lean_ctor_get(v_m_3402_, 1);
    v___x_3406_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3407_ = lean_array_get_size(v_buckets_3405_);
    v___x_3408_ = lean_nat_dec_lt(v___x_3406_, v___x_3407_);
    if v___x_3408_ == 0 {
        let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_3404_);
        crate::leanh::lean_dec(v_a_3403_);
        crate::leanh::lean_dec_ref(v_m_3402_);
        crate::leanh::lean_dec_ref(v_inst_3401_);
        crate::leanh::lean_dec_ref(v_inst_3399_);
        v___x_3409_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_3409_;
    } else {
        let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_3411_: *mut crate::leanh::LeanObject,
    mut v_b_3412_: *mut crate::leanh::LeanObject,
    mut v_d_3413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3414_, 0, v_a_3411_);
    crate::leanh::lean_ctor_set(v___x_3414_, 1, v_b_3412_);
    v___x_3415_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3415_, 0, v___x_3414_);
    crate::leanh::lean_ctor_set(v___x_3415_, 1, v_d_3413_);
    return v___x_3415_;
}
pub unsafe fn l_Std_HashMap_Raw_toList___redArg___lam__1(
    mut v___x_3416_: *mut crate::leanh::LeanObject,
    mut v___f_3417_: *mut crate::leanh::LeanObject,
    mut v_l_3418_: *mut crate::leanh::LeanObject,
    mut v_acc_3419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3420_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_3416_,
        v___f_3417_,
        v_acc_3419_,
        v_l_3418_,
    );
    return v___x_3420_;
}
pub unsafe fn l_Std_HashMap_Raw_toList___redArg(
    mut v_m_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    v___x_3426_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3427_ = crate::leanh::lean_ctor_get(v_m_3425_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3427_);
    crate::leanh::lean_dec_ref(v_m_3425_);
    v___x_3428_ = crate::leanh::lean_box(0);
    v___x_3429_ = lean_array_get_size(v_buckets_3427_);
    v___x_3430_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3431_ = lean_nat_dec_lt(v___x_3430_, v___x_3429_);
    if v___x_3431_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_3427_);
        return v___x_3428_;
    } else {
        let mut v___f_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3433_: usize = 0;
        let mut v___x_3434_: usize = 0;
        let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3432_ = l_Std_HashMap_Raw_toList___redArg___closed__1;
        v___x_3433_ = lean_usize_of_nat(v___x_3429_);
        v___x_3434_ = 0usize;
        v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3436_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3437_: *mut crate::leanh::LeanObject,
    mut v_m_3438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: u8 = 0;
    v___x_3439_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3440_ = crate::leanh::lean_ctor_get(v_m_3438_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3440_);
    crate::leanh::lean_dec_ref(v_m_3438_);
    v___x_3441_ = crate::leanh::lean_box(0);
    v___x_3442_ = lean_array_get_size(v_buckets_3440_);
    v___x_3443_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3444_ = lean_nat_dec_lt(v___x_3443_, v___x_3442_);
    if v___x_3444_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_3440_);
        return v___x_3441_;
    } else {
        let mut v___f_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3446_: usize = 0;
        let mut v___x_3447_: usize = 0;
        let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_3445_ = l_Std_HashMap_Raw_toList___redArg___closed__1;
        v___x_3446_ = lean_usize_of_nat(v___x_3442_);
        v___x_3447_ = 0usize;
        v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
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
    mut v_inst_3449_: *mut crate::leanh::LeanObject,
    mut v_f_3450_: *mut crate::leanh::LeanObject,
    mut v_acc_3451_: *mut crate::leanh::LeanObject,
    mut v_l_3452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_3449_,
        v_f_3450_,
        v_acc_3451_,
        v_l_3452_,
    );
    return v___x_3453_;
}
pub unsafe fn l_Std_HashMap_Raw_foldM___redArg(
    mut v_inst_3454_: *mut crate::leanh::LeanObject,
    mut v_f_3455_: *mut crate::leanh::LeanObject,
    mut v_init_3456_: *mut crate::leanh::LeanObject,
    mut v_b_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    v_buckets_3458_ = crate::leanh::lean_ctor_get(v_b_3457_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3458_);
    crate::leanh::lean_dec_ref(v_b_3457_);
    v___x_3459_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3460_ = lean_array_get_size(v_buckets_3458_);
    v___x_3461_ = lean_nat_dec_lt(v___x_3459_, v___x_3460_);
    if v___x_3461_ == 0 {
        let mut v_toApplicative_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_3458_);
        crate::leanh::lean_dec(v_f_3455_);
        v_toApplicative_3462_ = crate::leanh::lean_ctor_get(v_inst_3454_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3462_);
        crate::leanh::lean_dec_ref(v_inst_3454_);
        v_toPure_3463_ = crate::leanh::lean_ctor_get(v_toApplicative_3462_, 1);
        crate::leanh::lean_inc(v_toPure_3463_);
        crate::leanh::lean_dec_ref(v_toApplicative_3462_);
        v___x_3464_ =
            crate::leanh::lean_apply_2(v_toPure_3463_, crate::leanh::lean_box(0), v_init_3456_);
        return v___x_3464_;
    } else {
        let mut v___f_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3466_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_3454_);
        v___f_3465_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3465_, 0, v_inst_3454_);
        crate::leanh::lean_closure_set(v___f_3465_, 1, v_f_3455_);
        v___x_3466_ = lean_nat_dec_le(v___x_3460_, v___x_3460_);
        if v___x_3466_ == 0 {
            if v___x_3461_ == 0 {
                let mut v_toApplicative_3467_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_3465_);
                crate::leanh::lean_dec_ref(v_buckets_3458_);
                v_toApplicative_3467_ = crate::leanh::lean_ctor_get(v_inst_3454_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3467_);
                crate::leanh::lean_dec_ref(v_inst_3454_);
                v_toPure_3468_ = crate::leanh::lean_ctor_get(v_toApplicative_3467_, 1);
                crate::leanh::lean_inc(v_toPure_3468_);
                crate::leanh::lean_dec_ref(v_toApplicative_3467_);
                v___x_3469_ = crate::leanh::lean_apply_2(
                    v_toPure_3468_,
                    crate::leanh::lean_box(0),
                    v_init_3456_,
                );
                return v___x_3469_;
            } else {
                let mut v___x_3470_: usize = 0;
                let mut v___x_3471_: usize = 0;
                let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3470_ = 0usize;
                v___x_3471_ = lean_usize_of_nat(v___x_3460_);
                v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3473_ = 0usize;
            v___x_3474_ = lean_usize_of_nat(v___x_3460_);
            v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3476_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3477_: *mut crate::leanh::LeanObject,
    mut v_m_3478_: *mut crate::leanh::LeanObject,
    mut v_inst_3479_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3480_: *mut crate::leanh::LeanObject,
    mut v_f_3481_: *mut crate::leanh::LeanObject,
    mut v_init_3482_: *mut crate::leanh::LeanObject,
    mut v_b_3483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: u8 = 0;
    v_buckets_3484_ = crate::leanh::lean_ctor_get(v_b_3483_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3484_);
    crate::leanh::lean_dec_ref(v_b_3483_);
    v___x_3485_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3486_ = lean_array_get_size(v_buckets_3484_);
    v___x_3487_ = lean_nat_dec_lt(v___x_3485_, v___x_3486_);
    if v___x_3487_ == 0 {
        let mut v_toApplicative_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_3484_);
        crate::leanh::lean_dec(v_f_3481_);
        v_toApplicative_3488_ = crate::leanh::lean_ctor_get(v_inst_3479_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3488_);
        crate::leanh::lean_dec_ref(v_inst_3479_);
        v_toPure_3489_ = crate::leanh::lean_ctor_get(v_toApplicative_3488_, 1);
        crate::leanh::lean_inc(v_toPure_3489_);
        crate::leanh::lean_dec_ref(v_toApplicative_3488_);
        v___x_3490_ =
            crate::leanh::lean_apply_2(v_toPure_3489_, crate::leanh::lean_box(0), v_init_3482_);
        return v___x_3490_;
    } else {
        let mut v___f_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3492_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_3479_);
        v___f_3491_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3491_, 0, v_inst_3479_);
        crate::leanh::lean_closure_set(v___f_3491_, 1, v_f_3481_);
        v___x_3492_ = lean_nat_dec_le(v___x_3486_, v___x_3486_);
        if v___x_3492_ == 0 {
            if v___x_3487_ == 0 {
                let mut v_toApplicative_3493_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_3491_);
                crate::leanh::lean_dec_ref(v_buckets_3484_);
                v_toApplicative_3493_ = crate::leanh::lean_ctor_get(v_inst_3479_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3493_);
                crate::leanh::lean_dec_ref(v_inst_3479_);
                v_toPure_3494_ = crate::leanh::lean_ctor_get(v_toApplicative_3493_, 1);
                crate::leanh::lean_inc(v_toPure_3494_);
                crate::leanh::lean_dec_ref(v_toApplicative_3493_);
                v___x_3495_ = crate::leanh::lean_apply_2(
                    v_toPure_3494_,
                    crate::leanh::lean_box(0),
                    v_init_3482_,
                );
                return v___x_3495_;
            } else {
                let mut v___x_3496_: usize = 0;
                let mut v___x_3497_: usize = 0;
                let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3496_ = 0usize;
                v___x_3497_ = lean_usize_of_nat(v___x_3486_);
                v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3499_ = 0usize;
            v___x_3500_ = lean_usize_of_nat(v___x_3486_);
            v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_f_3502_: *mut crate::leanh::LeanObject,
    mut v_x1_3503_: *mut crate::leanh::LeanObject,
    mut v_x2_3504_: *mut crate::leanh::LeanObject,
    mut v_x3_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3506_ = crate::leanh::lean_apply_3(v_f_3502_, v_x1_3503_, v_x2_3504_, v_x3_3505_);
    return v___x_3506_;
}
pub unsafe fn l_Std_HashMap_Raw_fold___redArg___lam__1(
    mut v___x_3507_: *mut crate::leanh::LeanObject,
    mut v___f_3508_: *mut crate::leanh::LeanObject,
    mut v_acc_3509_: *mut crate::leanh::LeanObject,
    mut v_l_3510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3511_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_3507_,
        v___f_3508_,
        v_acc_3509_,
        v_l_3510_,
    );
    return v___x_3511_;
}
pub unsafe fn l_Std_HashMap_Raw_fold___redArg(
    mut v_f_3512_: *mut crate::leanh::LeanObject,
    mut v_init_3513_: *mut crate::leanh::LeanObject,
    mut v_b_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    v___x_3515_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3516_ = crate::leanh::lean_ctor_get(v_b_3514_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3516_);
    crate::leanh::lean_dec_ref(v_b_3514_);
    v___x_3517_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3518_ = lean_array_get_size(v_buckets_3516_);
    v___x_3519_ = lean_nat_dec_lt(v___x_3517_, v___x_3518_);
    if v___x_3519_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_3516_);
        crate::leanh::lean_dec(v_f_3512_);
        return v_init_3513_;
    } else {
        let mut v___f_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3522_: u8 = 0;
        v___f_3520_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3520_, 0, v_f_3512_);
        v___f_3521_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3521_, 0, v___x_3515_);
        crate::leanh::lean_closure_set(v___f_3521_, 1, v___f_3520_);
        v___x_3522_ = lean_nat_dec_le(v___x_3518_, v___x_3518_);
        if v___x_3522_ == 0 {
            if v___x_3519_ == 0 {
                crate::leanh::lean_dec_ref(v___f_3521_);
                crate::leanh::lean_dec_ref(v_buckets_3516_);
                return v_init_3513_;
            } else {
                let mut v___x_3523_: usize = 0;
                let mut v___x_3524_: usize = 0;
                let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3523_ = 0usize;
                v___x_3524_ = lean_usize_of_nat(v___x_3518_);
                v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3526_ = 0usize;
            v___x_3527_ = lean_usize_of_nat(v___x_3518_);
            v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3529_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3530_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3531_: *mut crate::leanh::LeanObject,
    mut v_f_3532_: *mut crate::leanh::LeanObject,
    mut v_init_3533_: *mut crate::leanh::LeanObject,
    mut v_b_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    v___x_3535_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3536_ = crate::leanh::lean_ctor_get(v_b_3534_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3536_);
    crate::leanh::lean_dec_ref(v_b_3534_);
    v___x_3537_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3538_ = lean_array_get_size(v_buckets_3536_);
    v___x_3539_ = lean_nat_dec_lt(v___x_3537_, v___x_3538_);
    if v___x_3539_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_3536_);
        crate::leanh::lean_dec(v_f_3532_);
        return v_init_3533_;
    } else {
        let mut v___f_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3542_: u8 = 0;
        v___f_3540_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3540_, 0, v_f_3532_);
        v___f_3541_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3541_, 0, v___x_3535_);
        crate::leanh::lean_closure_set(v___f_3541_, 1, v___f_3540_);
        v___x_3542_ = lean_nat_dec_le(v___x_3538_, v___x_3538_);
        if v___x_3542_ == 0 {
            if v___x_3539_ == 0 {
                crate::leanh::lean_dec_ref(v___f_3541_);
                crate::leanh::lean_dec_ref(v_buckets_3536_);
                return v_init_3533_;
            } else {
                let mut v___x_3543_: usize = 0;
                let mut v___x_3544_: usize = 0;
                let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3543_ = 0usize;
                v___x_3544_ = lean_usize_of_nat(v___x_3538_);
                v___x_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3546_ = 0usize;
            v___x_3547_ = lean_usize_of_nat(v___x_3538_);
            v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_f_3549_: *mut crate::leanh::LeanObject,
    mut v_x_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
    mut v___y_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = crate::leanh::lean_apply_2(v_f_3549_, v___y_3551_, v___y_3552_);
    return v___x_3553_;
}
pub unsafe fn l_Std_HashMap_Raw_forM___redArg___lam__1(
    mut v_inst_3554_: *mut crate::leanh::LeanObject,
    mut v___f_3555_: *mut crate::leanh::LeanObject,
    mut v_x_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = crate::leanh::lean_box(0);
    v___x_3559_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_3554_,
        v___f_3555_,
        v___x_3558_,
        v___y_3557_,
    );
    return v___x_3559_;
}
pub unsafe fn l_Std_HashMap_Raw_forM___redArg(
    mut v_inst_3560_: *mut crate::leanh::LeanObject,
    mut v_f_3561_: *mut crate::leanh::LeanObject,
    mut v_b_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: u8 = 0;
    v_buckets_3563_ = crate::leanh::lean_ctor_get(v_b_3562_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3563_);
    crate::leanh::lean_dec_ref(v_b_3562_);
    v___x_3564_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3565_ = lean_array_get_size(v_buckets_3563_);
    v___x_3566_ = crate::leanh::lean_box(0);
    v___x_3567_ = lean_nat_dec_lt(v___x_3564_, v___x_3565_);
    if v___x_3567_ == 0 {
        let mut v_toApplicative_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_3563_);
        crate::leanh::lean_dec(v_f_3561_);
        v_toApplicative_3568_ = crate::leanh::lean_ctor_get(v_inst_3560_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3568_);
        crate::leanh::lean_dec_ref(v_inst_3560_);
        v_toPure_3569_ = crate::leanh::lean_ctor_get(v_toApplicative_3568_, 1);
        crate::leanh::lean_inc(v_toPure_3569_);
        crate::leanh::lean_dec_ref(v_toApplicative_3568_);
        v___x_3570_ =
            crate::leanh::lean_apply_2(v_toPure_3569_, crate::leanh::lean_box(0), v___x_3566_);
        return v___x_3570_;
    } else {
        let mut v___f_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3573_: u8 = 0;
        v___f_3571_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3571_, 0, v_f_3561_);
        crate::leanh::lean_inc_ref(v_inst_3560_);
        v___f_3572_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3572_, 0, v_inst_3560_);
        crate::leanh::lean_closure_set(v___f_3572_, 1, v___f_3571_);
        v___x_3573_ = lean_nat_dec_le(v___x_3565_, v___x_3565_);
        if v___x_3573_ == 0 {
            if v___x_3567_ == 0 {
                let mut v_toApplicative_3574_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_3572_);
                crate::leanh::lean_dec_ref(v_buckets_3563_);
                v_toApplicative_3574_ = crate::leanh::lean_ctor_get(v_inst_3560_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3574_);
                crate::leanh::lean_dec_ref(v_inst_3560_);
                v_toPure_3575_ = crate::leanh::lean_ctor_get(v_toApplicative_3574_, 1);
                crate::leanh::lean_inc(v_toPure_3575_);
                crate::leanh::lean_dec_ref(v_toApplicative_3574_);
                v___x_3576_ = crate::leanh::lean_apply_2(
                    v_toPure_3575_,
                    crate::leanh::lean_box(0),
                    v___x_3566_,
                );
                return v___x_3576_;
            } else {
                let mut v___x_3577_: usize = 0;
                let mut v___x_3578_: usize = 0;
                let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3577_ = 0usize;
                v___x_3578_ = lean_usize_of_nat(v___x_3565_);
                v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3580_ = 0usize;
            v___x_3581_ = lean_usize_of_nat(v___x_3565_);
            v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3583_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3584_: *mut crate::leanh::LeanObject,
    mut v_m_3585_: *mut crate::leanh::LeanObject,
    mut v_inst_3586_: *mut crate::leanh::LeanObject,
    mut v_f_3587_: *mut crate::leanh::LeanObject,
    mut v_b_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    v_buckets_3589_ = crate::leanh::lean_ctor_get(v_b_3588_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3589_);
    crate::leanh::lean_dec_ref(v_b_3588_);
    v___x_3590_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3591_ = lean_array_get_size(v_buckets_3589_);
    v___x_3592_ = crate::leanh::lean_box(0);
    v___x_3593_ = lean_nat_dec_lt(v___x_3590_, v___x_3591_);
    if v___x_3593_ == 0 {
        let mut v_toApplicative_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_3589_);
        crate::leanh::lean_dec(v_f_3587_);
        v_toApplicative_3594_ = crate::leanh::lean_ctor_get(v_inst_3586_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3594_);
        crate::leanh::lean_dec_ref(v_inst_3586_);
        v_toPure_3595_ = crate::leanh::lean_ctor_get(v_toApplicative_3594_, 1);
        crate::leanh::lean_inc(v_toPure_3595_);
        crate::leanh::lean_dec_ref(v_toApplicative_3594_);
        v___x_3596_ =
            crate::leanh::lean_apply_2(v_toPure_3595_, crate::leanh::lean_box(0), v___x_3592_);
        return v___x_3596_;
    } else {
        let mut v___f_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3599_: u8 = 0;
        v___f_3597_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3597_, 0, v_f_3587_);
        crate::leanh::lean_inc_ref(v_inst_3586_);
        v___f_3598_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3598_, 0, v_inst_3586_);
        crate::leanh::lean_closure_set(v___f_3598_, 1, v___f_3597_);
        v___x_3599_ = lean_nat_dec_le(v___x_3591_, v___x_3591_);
        if v___x_3599_ == 0 {
            if v___x_3593_ == 0 {
                let mut v_toApplicative_3600_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_3598_);
                crate::leanh::lean_dec_ref(v_buckets_3589_);
                v_toApplicative_3600_ = crate::leanh::lean_ctor_get(v_inst_3586_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3600_);
                crate::leanh::lean_dec_ref(v_inst_3586_);
                v_toPure_3601_ = crate::leanh::lean_ctor_get(v_toApplicative_3600_, 1);
                crate::leanh::lean_inc(v_toPure_3601_);
                crate::leanh::lean_dec_ref(v_toApplicative_3600_);
                v___x_3602_ = crate::leanh::lean_apply_2(
                    v_toPure_3601_,
                    crate::leanh::lean_box(0),
                    v___x_3592_,
                );
                return v___x_3602_;
            } else {
                let mut v___x_3603_: usize = 0;
                let mut v___x_3604_: usize = 0;
                let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3603_ = 0usize;
                v___x_3604_ = lean_usize_of_nat(v___x_3591_);
                v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3606_ = 0usize;
            v___x_3607_ = lean_usize_of_nat(v___x_3591_);
            v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_inst_3609_: *mut crate::leanh::LeanObject,
    mut v_f_3610_: *mut crate::leanh::LeanObject,
    mut v_a_3611_: *mut crate::leanh::LeanObject,
    mut v_x_3612_: *mut crate::leanh::LeanObject,
    mut v___y_3613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_3609_, v_f_3610_, v_a_3611_, v___y_3613_);
    return v___x_3614_;
}
pub unsafe fn l_Std_HashMap_Raw_forIn___redArg(
    mut v_inst_3615_: *mut crate::leanh::LeanObject,
    mut v_f_3616_: *mut crate::leanh::LeanObject,
    mut v_init_3617_: *mut crate::leanh::LeanObject,
    mut v_b_3618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3621_: usize = 0;
    let mut v___x_3622_: usize = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3619_ = crate::leanh::lean_ctor_get(v_b_3618_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3619_);
    crate::leanh::lean_dec_ref(v_b_3618_);
    crate::leanh::lean_inc_ref(v_inst_3615_);
    v___f_3620_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3620_, 0, v_inst_3615_);
    crate::leanh::lean_closure_set(v___f_3620_, 1, v_f_3616_);
    v_sz_3621_ = lean_array_size(v_buckets_3619_);
    v___x_3622_ = 0usize;
    v___x_3623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3624_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3625_: *mut crate::leanh::LeanObject,
    mut v_m_3626_: *mut crate::leanh::LeanObject,
    mut v_inst_3627_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_3628_: *mut crate::leanh::LeanObject,
    mut v_f_3629_: *mut crate::leanh::LeanObject,
    mut v_init_3630_: *mut crate::leanh::LeanObject,
    mut v_b_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3634_: usize = 0;
    let mut v___x_3635_: usize = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3632_ = crate::leanh::lean_ctor_get(v_b_3631_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3632_);
    crate::leanh::lean_dec_ref(v_b_3631_);
    crate::leanh::lean_inc_ref(v_inst_3627_);
    v___f_3633_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3633_, 0, v_inst_3627_);
    crate::leanh::lean_closure_set(v___f_3633_, 1, v_f_3629_);
    v_sz_3634_ = lean_array_size(v_buckets_3632_);
    v___x_3635_ = 0usize;
    v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_f_3637_: *mut crate::leanh::LeanObject,
    mut v_x_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3641_, 0, v___y_3639_);
    crate::leanh::lean_ctor_set(v___x_3641_, 1, v___y_3640_);
    v___x_3642_ = crate::leanh::lean_apply_1(v_f_3637_, v___x_3641_);
    return v___x_3642_;
}
pub unsafe fn l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(
    mut v_inst_3643_: *mut crate::leanh::LeanObject,
    mut v_m_3644_: *mut crate::leanh::LeanObject,
    mut v_f_3645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    v_buckets_3646_ = crate::leanh::lean_ctor_get(v_m_3644_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3646_);
    crate::leanh::lean_dec_ref(v_m_3644_);
    v___x_3647_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3648_ = lean_array_get_size(v_buckets_3646_);
    v___x_3649_ = crate::leanh::lean_box(0);
    v___x_3650_ = lean_nat_dec_lt(v___x_3647_, v___x_3648_);
    if v___x_3650_ == 0 {
        let mut v_toApplicative_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_3646_);
        crate::leanh::lean_dec(v_f_3645_);
        v_toApplicative_3651_ = crate::leanh::lean_ctor_get(v_inst_3643_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3651_);
        crate::leanh::lean_dec_ref(v_inst_3643_);
        v_toPure_3652_ = crate::leanh::lean_ctor_get(v_toApplicative_3651_, 1);
        crate::leanh::lean_inc(v_toPure_3652_);
        crate::leanh::lean_dec_ref(v_toApplicative_3651_);
        v___x_3653_ =
            crate::leanh::lean_apply_2(v_toPure_3652_, crate::leanh::lean_box(0), v___x_3649_);
        return v___x_3653_;
    } else {
        let mut v___f_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3656_: u8 = 0;
        v___f_3654_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3654_, 0, v_f_3645_);
        crate::leanh::lean_inc_ref(v_inst_3643_);
        v___f_3655_ = crate::leanh::lean_alloc_closure(
            l_Std_HashMap_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3655_, 0, v_inst_3643_);
        crate::leanh::lean_closure_set(v___f_3655_, 1, v___f_3654_);
        v___x_3656_ = lean_nat_dec_le(v___x_3648_, v___x_3648_);
        if v___x_3656_ == 0 {
            if v___x_3650_ == 0 {
                let mut v_toApplicative_3657_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_3655_);
                crate::leanh::lean_dec_ref(v_buckets_3646_);
                v_toApplicative_3657_ = crate::leanh::lean_ctor_get(v_inst_3643_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3657_);
                crate::leanh::lean_dec_ref(v_inst_3643_);
                v_toPure_3658_ = crate::leanh::lean_ctor_get(v_toApplicative_3657_, 1);
                crate::leanh::lean_inc(v_toPure_3658_);
                crate::leanh::lean_dec_ref(v_toApplicative_3657_);
                v___x_3659_ = crate::leanh::lean_apply_2(
                    v_toPure_3658_,
                    crate::leanh::lean_box(0),
                    v___x_3649_,
                );
                return v___x_3659_;
            } else {
                let mut v___x_3660_: usize = 0;
                let mut v___x_3661_: usize = 0;
                let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3660_ = 0usize;
                v___x_3661_ = lean_usize_of_nat(v___x_3648_);
                v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3663_ = 0usize;
            v___x_3664_ = lean_usize_of_nat(v___x_3648_);
            v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_inst_3666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3667_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3667_, 0, v_inst_3666_);
    return v___f_3667_;
}
pub unsafe fn l_Std_HashMap_Raw_instForMProdOfMonad(
    mut v_00_u03b1_3668_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3669_: *mut crate::leanh::LeanObject,
    mut v_m_3670_: *mut crate::leanh::LeanObject,
    mut v_inst_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3672_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3672_, 0, v_inst_3671_);
    return v___f_3672_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(
    mut v_f_3673_: *mut crate::leanh::LeanObject,
    mut v_a_3674_: *mut crate::leanh::LeanObject,
    mut v_b_3675_: *mut crate::leanh::LeanObject,
    mut v_acc_3676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3677_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3677_, 0, v_a_3674_);
    crate::leanh::lean_ctor_set(v___x_3677_, 1, v_b_3675_);
    v___x_3678_ = crate::leanh::lean_apply_2(v_f_3673_, v___x_3677_, v_acc_3676_);
    return v___x_3678_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(
    mut v_inst_3679_: *mut crate::leanh::LeanObject,
    mut v___f_3680_: *mut crate::leanh::LeanObject,
    mut v_a_3681_: *mut crate::leanh::LeanObject,
    mut v_x_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3684_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_3679_, v___f_3680_, v_a_3681_, v___y_3683_);
    return v___x_3684_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(
    mut v_inst_3685_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3686_: *mut crate::leanh::LeanObject,
    mut v_m_3687_: *mut crate::leanh::LeanObject,
    mut v_init_3688_: *mut crate::leanh::LeanObject,
    mut v_f_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3693_: usize = 0;
    let mut v___x_3694_: usize = 0;
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3690_ = crate::leanh::lean_ctor_get(v_m_3687_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3690_);
    crate::leanh::lean_dec_ref(v_m_3687_);
    v___f_3691_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3691_, 0, v_f_3689_);
    crate::leanh::lean_inc_ref(v_inst_3685_);
    v___f_3692_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3692_, 0, v_inst_3685_);
    crate::leanh::lean_closure_set(v___f_3692_, 1, v___f_3691_);
    v_sz_3693_ = lean_array_size(v_buckets_3690_);
    v___x_3694_ = 0usize;
    v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
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
    mut v_inst_3696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3697_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3697_, 0, v_inst_3696_);
    return v___f_3697_;
}
pub unsafe fn l_Std_HashMap_Raw_instForInProdOfMonad(
    mut v_00_u03b1_3698_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3699_: *mut crate::leanh::LeanObject,
    mut v_m_3700_: *mut crate::leanh::LeanObject,
    mut v_inst_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3702_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3702_, 0, v_inst_3701_);
    return v___f_3702_;
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___lam__0(
    mut v_p_3703_: *mut crate::leanh::LeanObject,
    mut v___x_3704_: *mut crate::leanh::LeanObject,
    mut v___x_3705_: *mut crate::leanh::LeanObject,
    mut v_a_3706_: *mut crate::leanh::LeanObject,
    mut v_b_3707_: *mut crate::leanh::LeanObject,
    mut v_acc_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    v___x_3709_ = crate::leanh::lean_apply_2(v_p_3703_, v_a_3706_, v_b_3707_);
    v___x_3710_ = (crate::leanh::lean_unbox(v___x_3709_) as u8);
    if v___x_3710_ == 0 {
        let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3705_);
        v___x_3711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3711_, 0, v___x_3709_);
        v___x_3712_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3712_, 0, v___x_3711_);
        crate::leanh::lean_ctor_set(v___x_3712_, 1, v___x_3704_);
        v___x_3713_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3713_, 0, v___x_3712_);
        return v___x_3713_;
    } else {
        let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3714_, 0, v___x_3705_);
        return v___x_3714_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___lam__0___boxed(
    mut v_p_3715_: *mut crate::leanh::LeanObject,
    mut v___x_3716_: *mut crate::leanh::LeanObject,
    mut v___x_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_b_3719_: *mut crate::leanh::LeanObject,
    mut v_acc_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3721_ = l_Std_HashMap_Raw_all___redArg___lam__0(
        v_p_3715_,
        v___x_3716_,
        v___x_3717_,
        v_a_3718_,
        v_b_3719_,
        v_acc_3720_,
    );
    crate::leanh::lean_dec_ref(v_acc_3720_);
    return v_res_3721_;
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___lam__1(
    mut v___x_3722_: *mut crate::leanh::LeanObject,
    mut v___f_3723_: *mut crate::leanh::LeanObject,
    mut v_a_3724_: *mut crate::leanh::LeanObject,
    mut v_x_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3727_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_3722_, v___f_3723_, v_a_3724_, v___y_3726_);
    return v___x_3727_;
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg(
    mut v_m_3731_: *mut crate::leanh::LeanObject,
    mut v_p_3732_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3739_: usize = 0;
    let mut v___x_3740_: usize = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3733_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3734_ = crate::leanh::lean_ctor_get(v_m_3731_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3734_);
    crate::leanh::lean_dec_ref(v_m_3731_);
    v___x_3735_ = crate::leanh::lean_box(0);
    v___x_3736_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3737_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3737_, 0, v_p_3732_);
    crate::leanh::lean_closure_set(v___f_3737_, 1, v___x_3735_);
    crate::leanh::lean_closure_set(v___f_3737_, 2, v___x_3736_);
    v___f_3738_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3738_, 0, v___x_3733_);
    crate::leanh::lean_closure_set(v___f_3738_, 1, v___f_3737_);
    v_sz_3739_ = lean_array_size(v_buckets_3734_);
    v___x_3740_ = 0usize;
    v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3733_,
        v_buckets_3734_,
        v___f_3738_,
        v_sz_3739_,
        v___x_3740_,
        v___x_3736_,
    );
    v_fst_3742_ = crate::leanh::lean_ctor_get(v___x_3741_, 0);
    crate::leanh::lean_inc(v_fst_3742_);
    crate::leanh::lean_dec(v___x_3741_);
    if crate::leanh::lean_obj_tag(v_fst_3742_) == 0 {
        let mut v___x_3743_: u8 = 0;
        v___x_3743_ = 1;
        return v___x_3743_;
    } else {
        let mut v_val_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3745_: u8 = 0;
        v_val_3744_ = crate::leanh::lean_ctor_get(v_fst_3742_, 0);
        crate::leanh::lean_inc(v_val_3744_);
        crate::leanh::lean_dec_ref_known(v_fst_3742_, 1);
        v___x_3745_ = (crate::leanh::lean_unbox(v_val_3744_) as u8);
        crate::leanh::lean_dec(v_val_3744_);
        return v___x_3745_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_all___redArg___boxed(
    mut v_m_3746_: *mut crate::leanh::LeanObject,
    mut v_p_3747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3748_: u8 = 0;
    let mut v_r_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3748_ = l_Std_HashMap_Raw_all___redArg(v_m_3746_, v_p_3747_);
    v_r_3749_ = crate::leanh::lean_box((v_res_3748_) as usize);
    return v_r_3749_;
}
pub unsafe fn l_Std_HashMap_Raw_all(
    mut v_00_u03b1_3750_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3751_: *mut crate::leanh::LeanObject,
    mut v_m_3752_: *mut crate::leanh::LeanObject,
    mut v_p_3753_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3760_: usize = 0;
    let mut v___x_3761_: usize = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3755_ = crate::leanh::lean_ctor_get(v_m_3752_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3755_);
    crate::leanh::lean_dec_ref(v_m_3752_);
    v___x_3756_ = crate::leanh::lean_box(0);
    v___x_3757_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3758_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3758_, 0, v_p_3753_);
    crate::leanh::lean_closure_set(v___f_3758_, 1, v___x_3756_);
    crate::leanh::lean_closure_set(v___f_3758_, 2, v___x_3757_);
    v___f_3759_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3759_, 0, v___x_3754_);
    crate::leanh::lean_closure_set(v___f_3759_, 1, v___f_3758_);
    v_sz_3760_ = lean_array_size(v_buckets_3755_);
    v___x_3761_ = 0usize;
    v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3754_,
        v_buckets_3755_,
        v___f_3759_,
        v_sz_3760_,
        v___x_3761_,
        v___x_3757_,
    );
    v_fst_3763_ = crate::leanh::lean_ctor_get(v___x_3762_, 0);
    crate::leanh::lean_inc(v_fst_3763_);
    crate::leanh::lean_dec(v___x_3762_);
    if crate::leanh::lean_obj_tag(v_fst_3763_) == 0 {
        let mut v___x_3764_: u8 = 0;
        v___x_3764_ = 1;
        return v___x_3764_;
    } else {
        let mut v_val_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3766_: u8 = 0;
        v_val_3765_ = crate::leanh::lean_ctor_get(v_fst_3763_, 0);
        crate::leanh::lean_inc(v_val_3765_);
        crate::leanh::lean_dec_ref_known(v_fst_3763_, 1);
        v___x_3766_ = (crate::leanh::lean_unbox(v_val_3765_) as u8);
        crate::leanh::lean_dec(v_val_3765_);
        return v___x_3766_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_all___boxed(
    mut v_00_u03b1_3767_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3768_: *mut crate::leanh::LeanObject,
    mut v_m_3769_: *mut crate::leanh::LeanObject,
    mut v_p_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3771_: u8 = 0;
    let mut v_r_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l_Std_HashMap_Raw_all(v_00_u03b1_3767_, v_00_u03b2_3768_, v_m_3769_, v_p_3770_);
    v_r_3772_ = crate::leanh::lean_box((v_res_3771_) as usize);
    return v_r_3772_;
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg___lam__0(
    mut v_p_3773_: *mut crate::leanh::LeanObject,
    mut v___x_3774_: *mut crate::leanh::LeanObject,
    mut v___x_3775_: *mut crate::leanh::LeanObject,
    mut v_a_3776_: *mut crate::leanh::LeanObject,
    mut v_b_3777_: *mut crate::leanh::LeanObject,
    mut v_acc_3778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: u8 = 0;
    v___x_3779_ = crate::leanh::lean_apply_2(v_p_3773_, v_a_3776_, v_b_3777_);
    v___x_3780_ = (crate::leanh::lean_unbox(v___x_3779_) as u8);
    if v___x_3780_ == 0 {
        let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3781_, 0, v___x_3774_);
        return v___x_3781_;
    } else {
        let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3774_);
        v___x_3782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3782_, 0, v___x_3779_);
        v___x_3783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3783_, 0, v___x_3782_);
        crate::leanh::lean_ctor_set(v___x_3783_, 1, v___x_3775_);
        v___x_3784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3784_, 0, v___x_3783_);
        return v___x_3784_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg___lam__0___boxed(
    mut v_p_3785_: *mut crate::leanh::LeanObject,
    mut v___x_3786_: *mut crate::leanh::LeanObject,
    mut v___x_3787_: *mut crate::leanh::LeanObject,
    mut v_a_3788_: *mut crate::leanh::LeanObject,
    mut v_b_3789_: *mut crate::leanh::LeanObject,
    mut v_acc_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Std_HashMap_Raw_any___redArg___lam__0(
        v_p_3785_,
        v___x_3786_,
        v___x_3787_,
        v_a_3788_,
        v_b_3789_,
        v_acc_3790_,
    );
    crate::leanh::lean_dec_ref(v_acc_3790_);
    return v_res_3791_;
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg(
    mut v_m_3792_: *mut crate::leanh::LeanObject,
    mut v_p_3793_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3800_: usize = 0;
    let mut v___x_3801_: usize = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3795_ = crate::leanh::lean_ctor_get(v_m_3792_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3795_);
    crate::leanh::lean_dec_ref(v_m_3792_);
    v___x_3796_ = crate::leanh::lean_box(0);
    v___x_3797_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3798_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3798_, 0, v_p_3793_);
    crate::leanh::lean_closure_set(v___f_3798_, 1, v___x_3797_);
    crate::leanh::lean_closure_set(v___f_3798_, 2, v___x_3796_);
    v___f_3799_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3799_, 0, v___x_3794_);
    crate::leanh::lean_closure_set(v___f_3799_, 1, v___f_3798_);
    v_sz_3800_ = lean_array_size(v_buckets_3795_);
    v___x_3801_ = 0usize;
    v___x_3802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3794_,
        v_buckets_3795_,
        v___f_3799_,
        v_sz_3800_,
        v___x_3801_,
        v___x_3797_,
    );
    v_fst_3803_ = crate::leanh::lean_ctor_get(v___x_3802_, 0);
    crate::leanh::lean_inc(v_fst_3803_);
    crate::leanh::lean_dec(v___x_3802_);
    if crate::leanh::lean_obj_tag(v_fst_3803_) == 0 {
        let mut v___x_3804_: u8 = 0;
        v___x_3804_ = 0;
        return v___x_3804_;
    } else {
        let mut v_val_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3806_: u8 = 0;
        v_val_3805_ = crate::leanh::lean_ctor_get(v_fst_3803_, 0);
        crate::leanh::lean_inc(v_val_3805_);
        crate::leanh::lean_dec_ref_known(v_fst_3803_, 1);
        v___x_3806_ = (crate::leanh::lean_unbox(v_val_3805_) as u8);
        crate::leanh::lean_dec(v_val_3805_);
        return v___x_3806_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_any___redArg___boxed(
    mut v_m_3807_: *mut crate::leanh::LeanObject,
    mut v_p_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3809_: u8 = 0;
    let mut v_r_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3809_ = l_Std_HashMap_Raw_any___redArg(v_m_3807_, v_p_3808_);
    v_r_3810_ = crate::leanh::lean_box((v_res_3809_) as usize);
    return v_r_3810_;
}
pub unsafe fn l_Std_HashMap_Raw_any(
    mut v_00_u03b1_3811_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3812_: *mut crate::leanh::LeanObject,
    mut v_m_3813_: *mut crate::leanh::LeanObject,
    mut v_p_3814_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3821_: usize = 0;
    let mut v___x_3822_: usize = 0;
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3815_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_3816_ = crate::leanh::lean_ctor_get(v_m_3813_, 1);
    crate::leanh::lean_inc_ref(v_buckets_3816_);
    crate::leanh::lean_dec_ref(v_m_3813_);
    v___x_3817_ = crate::leanh::lean_box(0);
    v___x_3818_ = l_Std_HashMap_Raw_all___redArg___closed__0;
    v___f_3819_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3819_, 0, v_p_3814_);
    crate::leanh::lean_closure_set(v___f_3819_, 1, v___x_3818_);
    crate::leanh::lean_closure_set(v___f_3819_, 2, v___x_3817_);
    v___f_3820_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3820_, 0, v___x_3815_);
    crate::leanh::lean_closure_set(v___f_3820_, 1, v___f_3819_);
    v_sz_3821_ = lean_array_size(v_buckets_3816_);
    v___x_3822_ = 0usize;
    v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3815_,
        v_buckets_3816_,
        v___f_3820_,
        v_sz_3821_,
        v___x_3822_,
        v___x_3818_,
    );
    v_fst_3824_ = crate::leanh::lean_ctor_get(v___x_3823_, 0);
    crate::leanh::lean_inc(v_fst_3824_);
    crate::leanh::lean_dec(v___x_3823_);
    if crate::leanh::lean_obj_tag(v_fst_3824_) == 0 {
        let mut v___x_3825_: u8 = 0;
        v___x_3825_ = 0;
        return v___x_3825_;
    } else {
        let mut v_val_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3827_: u8 = 0;
        v_val_3826_ = crate::leanh::lean_ctor_get(v_fst_3824_, 0);
        crate::leanh::lean_inc(v_val_3826_);
        crate::leanh::lean_dec_ref_known(v_fst_3824_, 1);
        v___x_3827_ = (crate::leanh::lean_unbox(v_val_3826_) as u8);
        crate::leanh::lean_dec(v_val_3826_);
        return v___x_3827_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_any___boxed(
    mut v_00_u03b1_3828_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3829_: *mut crate::leanh::LeanObject,
    mut v_m_3830_: *mut crate::leanh::LeanObject,
    mut v_p_3831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3832_: u8 = 0;
    let mut v_r_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3832_ = l_Std_HashMap_Raw_any(v_00_u03b1_3828_, v_00_u03b2_3829_, v_m_3830_, v_p_3831_);
    v_r_3833_ = crate::leanh::lean_box((v_res_3832_) as usize);
    return v_r_3833_;
}
pub unsafe fn l_Std_HashMap_Raw_union___redArg___lam__0(
    mut v_inst_3834_: *mut crate::leanh::LeanObject,
    mut v_inst_3835_: *mut crate::leanh::LeanObject,
    mut v_a_3836_: *mut crate::leanh::LeanObject,
    mut v_b_3837_: *mut crate::leanh::LeanObject,
    mut v_acc_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_3839_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_3834_,
        v_inst_3835_,
        v_acc_3838_,
        v_a_3836_,
        v_b_3837_,
    );
    v___x_3840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3840_, 0, v_r_3839_);
    return v___x_3840_;
}
pub unsafe fn l_Std_HashMap_Raw_union___redArg___lam__1(
    mut v___x_3841_: *mut crate::leanh::LeanObject,
    mut v___f_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
    mut v_x_3844_: *mut crate::leanh::LeanObject,
    mut v___y_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3846_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_3841_, v___f_3842_, v_a_3843_, v___y_3845_);
    return v___x_3846_;
}
pub unsafe fn l_Std_HashMap_Raw_union___redArg(
    mut v_inst_3849_: *mut crate::leanh::LeanObject,
    mut v_inst_3850_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3851_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: u8 = 0;
    v_size_3853_ = crate::leanh::lean_ctor_get(v_m_u2081_3851_, 0);
    v_buckets_3854_ = crate::leanh::lean_ctor_get(v_m_u2081_3851_, 1);
    v___x_3855_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3856_ = lean_array_get_size(v_buckets_3854_);
    v___x_3857_ = lean_nat_dec_lt(v___x_3855_, v___x_3856_);
    if v___x_3857_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_3851_);
        crate::leanh::lean_dec_ref(v_inst_3850_);
        crate::leanh::lean_dec_ref(v_inst_3849_);
        return v_m_u2082_3852_;
    } else {
        let mut v_size_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3861_: u8 = 0;
        v_size_3858_ = crate::leanh::lean_ctor_get(v_m_u2082_3852_, 0);
        v_buckets_3859_ = crate::leanh::lean_ctor_get(v_m_u2082_3852_, 1);
        v___x_3860_ = lean_array_get_size(v_buckets_3859_);
        v___x_3861_ = lean_nat_dec_lt(v___x_3855_, v___x_3860_);
        if v___x_3861_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_3852_);
            crate::leanh::lean_dec_ref(v_inst_3850_);
            crate::leanh::lean_dec_ref(v_inst_3849_);
            return v_m_u2081_3851_;
        } else {
            let mut v___x_3862_: u8 = 0;
            v___x_3862_ = lean_nat_dec_le(v_size_3853_, v_size_3858_);
            if v___x_3862_ == 0 {
                let mut v___f_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___f_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_3868_: usize = 0;
                let mut v___x_3869_: usize = 0;
                let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_buckets_3854_);
                crate::leanh::lean_dec_ref(v_m_u2081_3851_);
                v___f_3865_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3865_, 0, v_inst_3849_);
                crate::leanh::lean_closure_set(v___f_3865_, 1, v_inst_3850_);
                v___x_3866_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
                v___f_3867_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3867_, 0, v___x_3866_);
                crate::leanh::lean_closure_set(v___f_3867_, 1, v___f_3865_);
                v_sz_3868_ = lean_array_size(v_buckets_3854_);
                v___x_3869_ = 0usize;
                v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_00_u03b1_3871_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3872_: *mut crate::leanh::LeanObject,
    mut v_inst_3873_: *mut crate::leanh::LeanObject,
    mut v_inst_3874_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3875_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    v_size_3877_ = crate::leanh::lean_ctor_get(v_m_u2081_3875_, 0);
    v_buckets_3878_ = crate::leanh::lean_ctor_get(v_m_u2081_3875_, 1);
    v___x_3879_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3880_ = lean_array_get_size(v_buckets_3878_);
    v___x_3881_ = lean_nat_dec_lt(v___x_3879_, v___x_3880_);
    if v___x_3881_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_3875_);
        crate::leanh::lean_dec_ref(v_inst_3874_);
        crate::leanh::lean_dec_ref(v_inst_3873_);
        return v_m_u2082_3876_;
    } else {
        let mut v_size_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3885_: u8 = 0;
        v_size_3882_ = crate::leanh::lean_ctor_get(v_m_u2082_3876_, 0);
        v_buckets_3883_ = crate::leanh::lean_ctor_get(v_m_u2082_3876_, 1);
        v___x_3884_ = lean_array_get_size(v_buckets_3883_);
        v___x_3885_ = lean_nat_dec_lt(v___x_3879_, v___x_3884_);
        if v___x_3885_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_3876_);
            crate::leanh::lean_dec_ref(v_inst_3874_);
            crate::leanh::lean_dec_ref(v_inst_3873_);
            return v_m_u2081_3875_;
        } else {
            let mut v___x_3886_: u8 = 0;
            v___x_3886_ = lean_nat_dec_le(v_size_3877_, v_size_3882_);
            if v___x_3886_ == 0 {
                let mut v___f_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___f_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_3892_: usize = 0;
                let mut v___x_3893_: usize = 0;
                let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_buckets_3878_);
                crate::leanh::lean_dec_ref(v_m_u2081_3875_);
                v___f_3889_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3889_, 0, v_inst_3873_);
                crate::leanh::lean_closure_set(v___f_3889_, 1, v_inst_3874_);
                v___x_3890_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
                v___f_3891_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3891_, 0, v___x_3890_);
                crate::leanh::lean_closure_set(v___f_3891_, 1, v___f_3889_);
                v_sz_3892_ = lean_array_size(v_buckets_3878_);
                v___x_3893_ = 0usize;
                v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_3895_: *mut crate::leanh::LeanObject,
    mut v_inst_3896_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3897_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    v_buckets_3899_ = crate::leanh::lean_ctor_get(v_m_u2081_3897_, 1);
    v___x_3900_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3901_ = lean_array_get_size(v_buckets_3899_);
    v___x_3902_ = lean_nat_dec_lt(v___x_3900_, v___x_3901_);
    if v___x_3902_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_3897_);
        crate::leanh::lean_dec_ref(v_inst_3896_);
        crate::leanh::lean_dec_ref(v_inst_3895_);
        return v_m_u2082_3898_;
    } else {
        let mut v_buckets_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3905_: u8 = 0;
        v_buckets_3903_ = crate::leanh::lean_ctor_get(v_m_u2082_3898_, 1);
        v___x_3904_ = lean_array_get_size(v_buckets_3903_);
        v___x_3905_ = lean_nat_dec_lt(v___x_3900_, v___x_3904_);
        if v___x_3905_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_3898_);
            crate::leanh::lean_dec_ref(v_inst_3896_);
            crate::leanh::lean_dec_ref(v_inst_3895_);
            return v_m_u2081_3897_;
        } else {
            let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3907_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3908_: *mut crate::leanh::LeanObject,
    mut v_inst_3909_: *mut crate::leanh::LeanObject,
    mut v_inst_3910_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3911_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    v_buckets_3913_ = crate::leanh::lean_ctor_get(v_m_u2081_3911_, 1);
    v___x_3914_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3915_ = lean_array_get_size(v_buckets_3913_);
    v___x_3916_ = lean_nat_dec_lt(v___x_3914_, v___x_3915_);
    if v___x_3916_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_3911_);
        crate::leanh::lean_dec_ref(v_inst_3910_);
        crate::leanh::lean_dec_ref(v_inst_3909_);
        return v_m_u2082_3912_;
    } else {
        let mut v_buckets_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3919_: u8 = 0;
        v_buckets_3917_ = crate::leanh::lean_ctor_get(v_m_u2082_3912_, 1);
        v___x_3918_ = lean_array_get_size(v_buckets_3917_);
        v___x_3919_ = lean_nat_dec_lt(v___x_3914_, v___x_3918_);
        if v___x_3919_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_3912_);
            crate::leanh::lean_dec_ref(v_inst_3910_);
            crate::leanh::lean_dec_ref(v_inst_3909_);
            return v_m_u2081_3911_;
        } else {
            let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3921_: *mut crate::leanh::LeanObject,
    mut v_inst_3922_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3923_: *mut crate::leanh::LeanObject,
    mut v___x_3924_: u8,
    mut v_k_3925_: *mut crate::leanh::LeanObject,
    mut v_x_3926_: *mut crate::leanh::LeanObject,
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
    mut v_inst_3929_: *mut crate::leanh::LeanObject,
    mut v_inst_3930_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3931_: *mut crate::leanh::LeanObject,
    mut v___x_3932_: *mut crate::leanh::LeanObject,
    mut v_k_3933_: *mut crate::leanh::LeanObject,
    mut v_x_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_91__boxed_3935_: u8 = 0;
    let mut v_res_3936_: u8 = 0;
    let mut v_r_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_91__boxed_3935_ = (crate::leanh::lean_unbox(v___x_3932_) as u8);
    v_res_3936_ = l_Std_HashMap_Raw_diff___redArg___lam__0(
        v_inst_3929_,
        v_inst_3930_,
        v_m_u2082_3931_,
        v___x_91__boxed_3935_,
        v_k_3933_,
        v_x_3934_,
    );
    crate::leanh::lean_dec(v_x_3934_);
    crate::leanh::lean_dec_ref(v_m_u2082_3931_);
    v_r_3937_ = crate::leanh::lean_box((v_res_3936_) as usize);
    return v_r_3937_;
}
pub unsafe fn l_Std_HashMap_Raw_diff___redArg(
    mut v_inst_3938_: *mut crate::leanh::LeanObject,
    mut v_inst_3939_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3940_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: u8 = 0;
    v_size_3942_ = crate::leanh::lean_ctor_get(v_m_u2081_3940_, 0);
    v_buckets_3943_ = crate::leanh::lean_ctor_get(v_m_u2081_3940_, 1);
    v___x_3944_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3945_ = lean_array_get_size(v_buckets_3943_);
    v___x_3946_ = lean_nat_dec_lt(v___x_3944_, v___x_3945_);
    if v___x_3946_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_3940_);
        crate::leanh::lean_dec_ref(v_inst_3939_);
        crate::leanh::lean_dec_ref(v_inst_3938_);
        return v_m_u2082_3941_;
    } else {
        let mut v_size_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3950_: u8 = 0;
        v_size_3947_ = crate::leanh::lean_ctor_get(v_m_u2082_3941_, 0);
        v_buckets_3948_ = crate::leanh::lean_ctor_get(v_m_u2082_3941_, 1);
        v___x_3949_ = lean_array_get_size(v_buckets_3948_);
        v___x_3950_ = lean_nat_dec_lt(v___x_3944_, v___x_3949_);
        if v___x_3950_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_3941_);
            crate::leanh::lean_dec_ref(v_inst_3939_);
            crate::leanh::lean_dec_ref(v_inst_3938_);
            return v_m_u2081_3940_;
        } else {
            let mut v___x_3951_: u8 = 0;
            v___x_3951_ = lean_nat_dec_le(v_size_3942_, v_size_3947_);
            if v___x_3951_ == 0 {
                let mut v___f_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3954_ = crate::leanh::lean_box((v___x_3951_) as usize);
                v___f_3955_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3955_, 0, v_inst_3938_);
                crate::leanh::lean_closure_set(v___f_3955_, 1, v_inst_3939_);
                crate::leanh::lean_closure_set(v___f_3955_, 2, v_m_u2082_3941_);
                crate::leanh::lean_closure_set(v___f_3955_, 3, v___x_3954_);
                v___x_3956_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3955_, v_m_u2081_3940_);
                return v___x_3956_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_diff(
    mut v_00_u03b1_3957_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3958_: *mut crate::leanh::LeanObject,
    mut v_inst_3959_: *mut crate::leanh::LeanObject,
    mut v_inst_3960_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_3961_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_3962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    v_size_3963_ = crate::leanh::lean_ctor_get(v_m_u2081_3961_, 0);
    v_buckets_3964_ = crate::leanh::lean_ctor_get(v_m_u2081_3961_, 1);
    v___x_3965_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3966_ = lean_array_get_size(v_buckets_3964_);
    v___x_3967_ = lean_nat_dec_lt(v___x_3965_, v___x_3966_);
    if v___x_3967_ == 0 {
        crate::leanh::lean_dec_ref(v_m_u2081_3961_);
        crate::leanh::lean_dec_ref(v_inst_3960_);
        crate::leanh::lean_dec_ref(v_inst_3959_);
        return v_m_u2082_3962_;
    } else {
        let mut v_size_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3971_: u8 = 0;
        v_size_3968_ = crate::leanh::lean_ctor_get(v_m_u2082_3962_, 0);
        v_buckets_3969_ = crate::leanh::lean_ctor_get(v_m_u2082_3962_, 1);
        v___x_3970_ = lean_array_get_size(v_buckets_3969_);
        v___x_3971_ = lean_nat_dec_lt(v___x_3965_, v___x_3970_);
        if v___x_3971_ == 0 {
            crate::leanh::lean_dec_ref(v_m_u2082_3962_);
            crate::leanh::lean_dec_ref(v_inst_3960_);
            crate::leanh::lean_dec_ref(v_inst_3959_);
            return v_m_u2081_3961_;
        } else {
            let mut v___x_3972_: u8 = 0;
            v___x_3972_ = lean_nat_dec_le(v_size_3963_, v_size_3968_);
            if v___x_3972_ == 0 {
                let mut v___f_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3975_ = crate::leanh::lean_box((v___x_3972_) as usize);
                v___f_3976_ = crate::leanh::lean_alloc_closure(
                    l_Std_HashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3976_, 0, v_inst_3959_);
                crate::leanh::lean_closure_set(v___f_3976_, 1, v_inst_3960_);
                crate::leanh::lean_closure_set(v___f_3976_, 2, v_m_u2082_3962_);
                crate::leanh::lean_closure_set(v___f_3976_, 3, v___x_3975_);
                v___x_3977_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_3976_, v_m_u2081_3961_);
                return v___x_3977_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(
    mut v_inst_3978_: *mut crate::leanh::LeanObject,
    mut v_inst_3979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3980_ =
        crate::leanh::lean_alloc_closure(l_Std_HashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_3980_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3980_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3980_, 2, v_inst_3978_);
    crate::leanh::lean_closure_set(v___x_3980_, 3, v_inst_3979_);
    return v___x_3980_;
}
pub unsafe fn l_Std_HashMap_Raw_instUnionOfBEqOfHashable(
    mut v_00_u03b1_3981_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3982_: *mut crate::leanh::LeanObject,
    mut v_inst_3983_: *mut crate::leanh::LeanObject,
    mut v_inst_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3985_ =
        crate::leanh::lean_alloc_closure(l_Std_HashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_3985_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3985_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3985_, 2, v_inst_3983_);
    crate::leanh::lean_closure_set(v___x_3985_, 3, v_inst_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(
    mut v_inst_3986_: *mut crate::leanh::LeanObject,
    mut v_inst_3987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ =
        crate::leanh::lean_alloc_closure(l_Std_HashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_3988_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3988_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3988_, 2, v_inst_3986_);
    crate::leanh::lean_closure_set(v___x_3988_, 3, v_inst_3987_);
    return v___x_3988_;
}
pub unsafe fn l_Std_HashMap_Raw_instInterOfBEqOfHashable(
    mut v_00_u03b1_3989_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3990_: *mut crate::leanh::LeanObject,
    mut v_inst_3991_: *mut crate::leanh::LeanObject,
    mut v_inst_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3993_ =
        crate::leanh::lean_alloc_closure(l_Std_HashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_3993_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3993_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3993_, 2, v_inst_3991_);
    crate::leanh::lean_closure_set(v___x_3993_, 3, v_inst_3992_);
    return v___x_3993_;
}
pub unsafe fn l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(
    mut v_inst_3994_: *mut crate::leanh::LeanObject,
    mut v_inst_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ =
        crate::leanh::lean_alloc_closure(l_Std_HashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_3996_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3996_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3996_, 2, v_inst_3994_);
    crate::leanh::lean_closure_set(v___x_3996_, 3, v_inst_3995_);
    return v___x_3996_;
}
pub unsafe fn l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(
    mut v_00_u03b1_3997_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3998_: *mut crate::leanh::LeanObject,
    mut v_inst_3999_: *mut crate::leanh::LeanObject,
    mut v_inst_4000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4001_ =
        crate::leanh::lean_alloc_closure(l_Std_HashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4001_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4001_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4001_, 2, v_inst_3999_);
    crate::leanh::lean_closure_set(v___x_4001_, 3, v_inst_4000_);
    return v___x_4001_;
}
pub unsafe fn l_Std_HashMap_Raw_beq___redArg(
    mut v_inst_4002_: *mut crate::leanh::LeanObject,
    mut v_inst_4003_: *mut crate::leanh::LeanObject,
    mut v_inst_4004_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4005_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4006_: *mut crate::leanh::LeanObject,
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
    mut v_inst_4008_: *mut crate::leanh::LeanObject,
    mut v_inst_4009_: *mut crate::leanh::LeanObject,
    mut v_inst_4010_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4011_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4013_: u8 = 0;
    let mut v_r_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4013_ = l_Std_HashMap_Raw_beq___redArg(
        v_inst_4008_,
        v_inst_4009_,
        v_inst_4010_,
        v_m_u2081_4011_,
        v_m_u2082_4012_,
    );
    v_r_4014_ = crate::leanh::lean_box((v_res_4013_) as usize);
    return v_r_4014_;
}
pub unsafe fn l_Std_HashMap_Raw_beq(
    mut v_00_u03b1_4015_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4016_: *mut crate::leanh::LeanObject,
    mut v_inst_4017_: *mut crate::leanh::LeanObject,
    mut v_inst_4018_: *mut crate::leanh::LeanObject,
    mut v_inst_4019_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4020_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4021_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_4023_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4024_: *mut crate::leanh::LeanObject,
    mut v_inst_4025_: *mut crate::leanh::LeanObject,
    mut v_inst_4026_: *mut crate::leanh::LeanObject,
    mut v_inst_4027_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_4028_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_4029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4030_: u8 = 0;
    let mut v_r_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4030_ = l_Std_HashMap_Raw_beq(
        v_00_u03b1_4023_,
        v_00_u03b2_4024_,
        v_inst_4025_,
        v_inst_4026_,
        v_inst_4027_,
        v_m_u2081_4028_,
        v_m_u2082_4029_,
    );
    v_r_4031_ = crate::leanh::lean_box((v_res_4030_) as usize);
    return v_r_4031_;
}
pub unsafe fn l_Std_HashMap_Raw_instBEqOfHashable___redArg(
    mut v_inst_4032_: *mut crate::leanh::LeanObject,
    mut v_inst_4033_: *mut crate::leanh::LeanObject,
    mut v_inst_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___x_4035_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4035_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4035_, 2, v_inst_4032_);
    crate::leanh::lean_closure_set(v___x_4035_, 3, v_inst_4033_);
    crate::leanh::lean_closure_set(v___x_4035_, 4, v_inst_4034_);
    return v___x_4035_;
}
pub unsafe fn l_Std_HashMap_Raw_instBEqOfHashable(
    mut v_00_u03b1_4036_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4037_: *mut crate::leanh::LeanObject,
    mut v_inst_4038_: *mut crate::leanh::LeanObject,
    mut v_inst_4039_: *mut crate::leanh::LeanObject,
    mut v_inst_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___x_4041_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4041_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4041_, 2, v_inst_4038_);
    crate::leanh::lean_closure_set(v___x_4041_, 3, v_inst_4039_);
    crate::leanh::lean_closure_set(v___x_4041_, 4, v_inst_4040_);
    return v___x_4041_;
}
pub unsafe fn l_Std_HashMap_Raw_filterMap___redArg(
    mut v_f_4042_: *mut crate::leanh::LeanObject,
    mut v_m_4043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    v_buckets_4044_ = crate::leanh::lean_ctor_get(v_m_4043_, 1);
    v___x_4045_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4046_ = lean_array_get_size(v_buckets_4044_);
    v___x_4047_ = lean_nat_dec_lt(v___x_4045_, v___x_4046_);
    if v___x_4047_ == 0 {
        let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4043_);
        crate::leanh::lean_dec_ref(v_f_4042_);
        v___x_4048_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4048_;
    } else {
        let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4049_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4042_, v_m_4043_);
        return v___x_4049_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_filterMap(
    mut v_00_u03b1_4050_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4051_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4052_: *mut crate::leanh::LeanObject,
    mut v_f_4053_: *mut crate::leanh::LeanObject,
    mut v_m_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u8 = 0;
    v_buckets_4055_ = crate::leanh::lean_ctor_get(v_m_4054_, 1);
    v___x_4056_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4057_ = lean_array_get_size(v_buckets_4055_);
    v___x_4058_ = lean_nat_dec_lt(v___x_4056_, v___x_4057_);
    if v___x_4058_ == 0 {
        let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4054_);
        crate::leanh::lean_dec_ref(v_f_4053_);
        v___x_4059_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4059_;
    } else {
        let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4060_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4053_, v_m_4054_);
        return v___x_4060_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_map___redArg(
    mut v_f_4061_: *mut crate::leanh::LeanObject,
    mut v_m_4062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    v_buckets_4063_ = crate::leanh::lean_ctor_get(v_m_4062_, 1);
    v___x_4064_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4065_ = lean_array_get_size(v_buckets_4063_);
    v___x_4066_ = lean_nat_dec_lt(v___x_4064_, v___x_4065_);
    if v___x_4066_ == 0 {
        let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4062_);
        crate::leanh::lean_dec(v_f_4061_);
        v___x_4067_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4067_;
    } else {
        let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4068_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4061_, v_m_4062_);
        return v___x_4068_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_map(
    mut v_00_u03b1_4069_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4070_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4071_: *mut crate::leanh::LeanObject,
    mut v_f_4072_: *mut crate::leanh::LeanObject,
    mut v_m_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    v_buckets_4074_ = crate::leanh::lean_ctor_get(v_m_4073_, 1);
    v___x_4075_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4076_ = lean_array_get_size(v_buckets_4074_);
    v___x_4077_ = lean_nat_dec_lt(v___x_4075_, v___x_4076_);
    if v___x_4077_ == 0 {
        let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4073_);
        crate::leanh::lean_dec(v_f_4072_);
        v___x_4078_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4078_;
    } else {
        let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4079_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4072_, v_m_4073_);
        return v___x_4079_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_filter___redArg(
    mut v_f_4080_: *mut crate::leanh::LeanObject,
    mut v_m_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    v_buckets_4082_ = crate::leanh::lean_ctor_get(v_m_4081_, 1);
    v___x_4083_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4084_ = lean_array_get_size(v_buckets_4082_);
    v___x_4085_ = lean_nat_dec_lt(v___x_4083_, v___x_4084_);
    if v___x_4085_ == 0 {
        let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4081_);
        crate::leanh::lean_dec_ref(v_f_4080_);
        v___x_4086_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4086_;
    } else {
        let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4087_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4080_, v_m_4081_);
        return v___x_4087_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_filter(
    mut v_00_u03b1_4088_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4089_: *mut crate::leanh::LeanObject,
    mut v_f_4090_: *mut crate::leanh::LeanObject,
    mut v_m_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    v_buckets_4092_ = crate::leanh::lean_ctor_get(v_m_4091_, 1);
    v___x_4093_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4094_ = lean_array_get_size(v_buckets_4092_);
    v___x_4095_ = lean_nat_dec_lt(v___x_4093_, v___x_4094_);
    if v___x_4095_ == 0 {
        let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_m_4091_);
        crate::leanh::lean_dec_ref(v_f_4090_);
        v___x_4096_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4096_;
    } else {
        let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4097_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4090_, v_m_4091_);
        return v___x_4097_;
    }
}
pub unsafe fn l_Std_HashMap_Raw_toArray___redArg___lam__0(
    mut v_x1_4098_: *mut crate::leanh::LeanObject,
    mut v_x2_4099_: *mut crate::leanh::LeanObject,
    mut v_x3_4100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4101_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4101_, 0, v_x2_4099_);
    crate::leanh::lean_ctor_set(v___x_4101_, 1, v_x3_4100_);
    v___x_4102_ = lean_array_push(v_x1_4098_, v___x_4101_);
    return v___x_4102_;
}
pub unsafe fn l_Std_HashMap_Raw_toArray___redArg___lam__1(
    mut v___x_4103_: *mut crate::leanh::LeanObject,
    mut v___f_4104_: *mut crate::leanh::LeanObject,
    mut v_acc_4105_: *mut crate::leanh::LeanObject,
    mut v_l_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4103_,
        v___f_4104_,
        v_acc_4105_,
        v_l_4106_,
    );
    return v___x_4107_;
}
pub unsafe fn l_Std_HashMap_Raw_toArray___redArg(
    mut v_m_4112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    v_size_4113_ = crate::leanh::lean_ctor_get(v_m_4112_, 0);
    crate::leanh::lean_inc(v_size_4113_);
    v_buckets_4114_ = crate::leanh::lean_ctor_get(v_m_4112_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4114_);
    crate::leanh::lean_dec_ref(v_m_4112_);
    v___x_4115_ = lean_mk_empty_array_with_capacity(v_size_4113_);
    crate::leanh::lean_dec(v_size_4113_);
    v___x_4116_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4117_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4118_ = lean_array_get_size(v_buckets_4114_);
    v___x_4119_ = lean_nat_dec_lt(v___x_4117_, v___x_4118_);
    if v___x_4119_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4114_);
        return v___x_4115_;
    } else {
        let mut v___f_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4121_: u8 = 0;
        v___f_4120_ = l_Std_HashMap_Raw_toArray___redArg___closed__1;
        v___x_4121_ = lean_nat_dec_le(v___x_4118_, v___x_4118_);
        if v___x_4121_ == 0 {
            if v___x_4119_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4114_);
                return v___x_4115_;
            } else {
                let mut v___x_4122_: usize = 0;
                let mut v___x_4123_: usize = 0;
                let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4122_ = 0usize;
                v___x_4123_ = lean_usize_of_nat(v___x_4118_);
                v___x_4124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4125_ = 0usize;
            v___x_4126_ = lean_usize_of_nat(v___x_4118_);
            v___x_4127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_4128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4129_: *mut crate::leanh::LeanObject,
    mut v_m_4130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    v_size_4131_ = crate::leanh::lean_ctor_get(v_m_4130_, 0);
    crate::leanh::lean_inc(v_size_4131_);
    v_buckets_4132_ = crate::leanh::lean_ctor_get(v_m_4130_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4132_);
    crate::leanh::lean_dec_ref(v_m_4130_);
    v___x_4133_ = lean_mk_empty_array_with_capacity(v_size_4131_);
    crate::leanh::lean_dec(v_size_4131_);
    v___x_4134_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4135_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4136_ = lean_array_get_size(v_buckets_4132_);
    v___x_4137_ = lean_nat_dec_lt(v___x_4135_, v___x_4136_);
    if v___x_4137_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4132_);
        return v___x_4133_;
    } else {
        let mut v___f_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4139_: u8 = 0;
        v___f_4138_ = l_Std_HashMap_Raw_toArray___redArg___closed__1;
        v___x_4139_ = lean_nat_dec_le(v___x_4136_, v___x_4136_);
        if v___x_4139_ == 0 {
            if v___x_4137_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4132_);
                return v___x_4133_;
            } else {
                let mut v___x_4140_: usize = 0;
                let mut v___x_4141_: usize = 0;
                let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4140_ = 0usize;
                v___x_4141_ = lean_usize_of_nat(v___x_4136_);
                v___x_4142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4143_ = 0usize;
            v___x_4144_ = lean_usize_of_nat(v___x_4136_);
            v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_x1_4146_: *mut crate::leanh::LeanObject,
    mut v_x2_4147_: *mut crate::leanh::LeanObject,
    mut v_x3_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = lean_array_push(v_x1_4146_, v_x2_4147_);
    return v___x_4149_;
}
pub unsafe fn l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(
    mut v_x1_4150_: *mut crate::leanh::LeanObject,
    mut v_x2_4151_: *mut crate::leanh::LeanObject,
    mut v_x3_4152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4153_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_4150_, v_x2_4151_, v_x3_4152_);
    crate::leanh::lean_dec(v_x3_4152_);
    return v_res_4153_;
}
pub unsafe fn l_Std_HashMap_Raw_keysArray___redArg___lam__1(
    mut v___x_4154_: *mut crate::leanh::LeanObject,
    mut v___f_4155_: *mut crate::leanh::LeanObject,
    mut v_acc_4156_: *mut crate::leanh::LeanObject,
    mut v_l_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4158_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4154_,
        v___f_4155_,
        v_acc_4156_,
        v_l_4157_,
    );
    return v___x_4158_;
}
pub unsafe fn l_Std_HashMap_Raw_keysArray___redArg(
    mut v_m_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    v_size_4164_ = crate::leanh::lean_ctor_get(v_m_4163_, 0);
    crate::leanh::lean_inc(v_size_4164_);
    v_buckets_4165_ = crate::leanh::lean_ctor_get(v_m_4163_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4165_);
    crate::leanh::lean_dec_ref(v_m_4163_);
    v___x_4166_ = lean_mk_empty_array_with_capacity(v_size_4164_);
    crate::leanh::lean_dec(v_size_4164_);
    v___x_4167_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4168_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4169_ = lean_array_get_size(v_buckets_4165_);
    v___x_4170_ = lean_nat_dec_lt(v___x_4168_, v___x_4169_);
    if v___x_4170_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4165_);
        return v___x_4166_;
    } else {
        let mut v___f_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4172_: u8 = 0;
        v___f_4171_ = l_Std_HashMap_Raw_keysArray___redArg___closed__1;
        v___x_4172_ = lean_nat_dec_le(v___x_4169_, v___x_4169_);
        if v___x_4172_ == 0 {
            if v___x_4170_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4165_);
                return v___x_4166_;
            } else {
                let mut v___x_4173_: usize = 0;
                let mut v___x_4174_: usize = 0;
                let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4173_ = 0usize;
                v___x_4174_ = lean_usize_of_nat(v___x_4169_);
                v___x_4175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4176_ = 0usize;
            v___x_4177_ = lean_usize_of_nat(v___x_4169_);
            v___x_4178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_4179_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4180_: *mut crate::leanh::LeanObject,
    mut v_m_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: u8 = 0;
    v_size_4182_ = crate::leanh::lean_ctor_get(v_m_4181_, 0);
    crate::leanh::lean_inc(v_size_4182_);
    v_buckets_4183_ = crate::leanh::lean_ctor_get(v_m_4181_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4183_);
    crate::leanh::lean_dec_ref(v_m_4181_);
    v___x_4184_ = lean_mk_empty_array_with_capacity(v_size_4182_);
    crate::leanh::lean_dec(v_size_4182_);
    v___x_4185_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4186_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4187_ = lean_array_get_size(v_buckets_4183_);
    v___x_4188_ = lean_nat_dec_lt(v___x_4186_, v___x_4187_);
    if v___x_4188_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4183_);
        return v___x_4184_;
    } else {
        let mut v___f_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4190_: u8 = 0;
        v___f_4189_ = l_Std_HashMap_Raw_keysArray___redArg___closed__1;
        v___x_4190_ = lean_nat_dec_le(v___x_4187_, v___x_4187_);
        if v___x_4190_ == 0 {
            if v___x_4188_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4183_);
                return v___x_4184_;
            } else {
                let mut v___x_4191_: usize = 0;
                let mut v___x_4192_: usize = 0;
                let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4191_ = 0usize;
                v___x_4192_ = lean_usize_of_nat(v___x_4187_);
                v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4194_ = 0usize;
            v___x_4195_ = lean_usize_of_nat(v___x_4187_);
            v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_b_4198_: *mut crate::leanh::LeanObject,
    mut v_d_4199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4200_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4200_, 0, v_b_4198_);
    crate::leanh::lean_ctor_set(v___x_4200_, 1, v_d_4199_);
    return v___x_4200_;
}
pub unsafe fn l_Std_HashMap_Raw_values___redArg___lam__0___boxed(
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_b_4202_: *mut crate::leanh::LeanObject,
    mut v_d_4203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_4201_, v_b_4202_, v_d_4203_);
    crate::leanh::lean_dec(v_a_4201_);
    return v_res_4204_;
}
pub unsafe fn l_Std_HashMap_Raw_values___redArg(
    mut v_m_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: u8 = 0;
    v___x_4210_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_4211_ = crate::leanh::lean_ctor_get(v_m_4209_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4211_);
    crate::leanh::lean_dec_ref(v_m_4209_);
    v___x_4212_ = crate::leanh::lean_box(0);
    v___x_4213_ = lean_array_get_size(v_buckets_4211_);
    v___x_4214_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4215_ = lean_nat_dec_lt(v___x_4214_, v___x_4213_);
    if v___x_4215_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4211_);
        return v___x_4212_;
    } else {
        let mut v___f_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4217_: usize = 0;
        let mut v___x_4218_: usize = 0;
        let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4216_ = l_Std_HashMap_Raw_values___redArg___closed__1;
        v___x_4217_ = lean_usize_of_nat(v___x_4213_);
        v___x_4218_ = 0usize;
        v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
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
    mut v_00_u03b1_4220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4221_: *mut crate::leanh::LeanObject,
    mut v_m_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    v___x_4223_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v_buckets_4224_ = crate::leanh::lean_ctor_get(v_m_4222_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4224_);
    crate::leanh::lean_dec_ref(v_m_4222_);
    v___x_4225_ = crate::leanh::lean_box(0);
    v___x_4226_ = lean_array_get_size(v_buckets_4224_);
    v___x_4227_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4228_ = lean_nat_dec_lt(v___x_4227_, v___x_4226_);
    if v___x_4228_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4224_);
        return v___x_4225_;
    } else {
        let mut v___f_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4230_: usize = 0;
        let mut v___x_4231_: usize = 0;
        let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4229_ = l_Std_HashMap_Raw_values___redArg___closed__1;
        v___x_4230_ = lean_usize_of_nat(v___x_4226_);
        v___x_4231_ = 0usize;
        v___x_4232_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
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
    mut v_x1_4233_: *mut crate::leanh::LeanObject,
    mut v_x2_4234_: *mut crate::leanh::LeanObject,
    mut v_x3_4235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4236_ = lean_array_push(v_x1_4233_, v_x3_4235_);
    return v___x_4236_;
}
pub unsafe fn l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(
    mut v_x1_4237_: *mut crate::leanh::LeanObject,
    mut v_x2_4238_: *mut crate::leanh::LeanObject,
    mut v_x3_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4240_ =
        l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_4237_, v_x2_4238_, v_x3_4239_);
    crate::leanh::lean_dec(v_x2_4238_);
    return v_res_4240_;
}
pub unsafe fn l_Std_HashMap_Raw_valuesArray___redArg(
    mut v_m_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    v_size_4246_ = crate::leanh::lean_ctor_get(v_m_4245_, 0);
    crate::leanh::lean_inc(v_size_4246_);
    v_buckets_4247_ = crate::leanh::lean_ctor_get(v_m_4245_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4247_);
    crate::leanh::lean_dec_ref(v_m_4245_);
    v___x_4248_ = lean_mk_empty_array_with_capacity(v_size_4246_);
    crate::leanh::lean_dec(v_size_4246_);
    v___x_4249_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4250_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4251_ = lean_array_get_size(v_buckets_4247_);
    v___x_4252_ = lean_nat_dec_lt(v___x_4250_, v___x_4251_);
    if v___x_4252_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4247_);
        return v___x_4248_;
    } else {
        let mut v___f_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4254_: u8 = 0;
        v___f_4253_ = l_Std_HashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4254_ = lean_nat_dec_le(v___x_4251_, v___x_4251_);
        if v___x_4254_ == 0 {
            if v___x_4252_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4247_);
                return v___x_4248_;
            } else {
                let mut v___x_4255_: usize = 0;
                let mut v___x_4256_: usize = 0;
                let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4255_ = 0usize;
                v___x_4256_ = lean_usize_of_nat(v___x_4251_);
                v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4258_ = 0usize;
            v___x_4259_ = lean_usize_of_nat(v___x_4251_);
            v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_4261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4262_: *mut crate::leanh::LeanObject,
    mut v_m_4263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: u8 = 0;
    v_size_4264_ = crate::leanh::lean_ctor_get(v_m_4263_, 0);
    crate::leanh::lean_inc(v_size_4264_);
    v_buckets_4265_ = crate::leanh::lean_ctor_get(v_m_4263_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4265_);
    crate::leanh::lean_dec_ref(v_m_4263_);
    v___x_4266_ = lean_mk_empty_array_with_capacity(v_size_4264_);
    crate::leanh::lean_dec(v_size_4264_);
    v___x_4267_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
    v___x_4268_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4269_ = lean_array_get_size(v_buckets_4265_);
    v___x_4270_ = lean_nat_dec_lt(v___x_4268_, v___x_4269_);
    if v___x_4270_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_4265_);
        return v___x_4266_;
    } else {
        let mut v___f_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: u8 = 0;
        v___f_4271_ = l_Std_HashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4272_ = lean_nat_dec_le(v___x_4269_, v___x_4269_);
        if v___x_4272_ == 0 {
            if v___x_4270_ == 0 {
                crate::leanh::lean_dec_ref(v_buckets_4265_);
                return v___x_4266_;
            } else {
                let mut v___x_4273_: usize = 0;
                let mut v___x_4274_: usize = 0;
                let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4273_ = 0usize;
                v___x_4274_ = lean_usize_of_nat(v___x_4269_);
                v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4276_ = 0usize;
            v___x_4277_ = lean_usize_of_nat(v___x_4269_);
            v___x_4278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_inst_4279_: *mut crate::leanh::LeanObject,
    mut v_inst_4280_: *mut crate::leanh::LeanObject,
    mut v_inst_4281_: *mut crate::leanh::LeanObject,
    mut v_m_4282_: *mut crate::leanh::LeanObject,
    mut v_l_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    v_buckets_4284_ = crate::leanh::lean_ctor_get(v_m_4282_, 1);
    v___x_4285_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4286_ = lean_array_get_size(v_buckets_4284_);
    v___x_4287_ = lean_nat_dec_lt(v___x_4285_, v___x_4286_);
    if v___x_4287_ == 0 {
        crate::leanh::lean_dec(v_l_4283_);
        crate::leanh::lean_dec(v_inst_4281_);
        crate::leanh::lean_dec_ref(v_inst_4280_);
        crate::leanh::lean_dec_ref(v_inst_4279_);
        return v_m_4282_;
    } else {
        let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4289_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4290_: *mut crate::leanh::LeanObject,
    mut v_inst_4291_: *mut crate::leanh::LeanObject,
    mut v_inst_4292_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4293_: *mut crate::leanh::LeanObject,
    mut v_inst_4294_: *mut crate::leanh::LeanObject,
    mut v_m_4295_: *mut crate::leanh::LeanObject,
    mut v_l_4296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    v_buckets_4297_ = crate::leanh::lean_ctor_get(v_m_4295_, 1);
    v___x_4298_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4299_ = lean_array_get_size(v_buckets_4297_);
    v___x_4300_ = lean_nat_dec_lt(v___x_4298_, v___x_4299_);
    if v___x_4300_ == 0 {
        crate::leanh::lean_dec(v_l_4296_);
        crate::leanh::lean_dec(v_inst_4294_);
        crate::leanh::lean_dec_ref(v_inst_4292_);
        crate::leanh::lean_dec_ref(v_inst_4291_);
        return v_m_4295_;
    } else {
        let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4302_: *mut crate::leanh::LeanObject,
    mut v_inst_4303_: *mut crate::leanh::LeanObject,
    mut v_inst_4304_: *mut crate::leanh::LeanObject,
    mut v_m_4305_: *mut crate::leanh::LeanObject,
    mut v_l_4306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    v_buckets_4307_ = crate::leanh::lean_ctor_get(v_m_4305_, 1);
    v___x_4308_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4309_ = lean_array_get_size(v_buckets_4307_);
    v___x_4310_ = lean_nat_dec_lt(v___x_4308_, v___x_4309_);
    if v___x_4310_ == 0 {
        crate::leanh::lean_dec(v_l_4306_);
        crate::leanh::lean_dec(v_inst_4304_);
        crate::leanh::lean_dec_ref(v_inst_4303_);
        crate::leanh::lean_dec_ref(v_inst_4302_);
        return v_m_4305_;
    } else {
        let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4312_: *mut crate::leanh::LeanObject,
    mut v_inst_4313_: *mut crate::leanh::LeanObject,
    mut v_inst_4314_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4315_: *mut crate::leanh::LeanObject,
    mut v_inst_4316_: *mut crate::leanh::LeanObject,
    mut v_m_4317_: *mut crate::leanh::LeanObject,
    mut v_l_4318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: u8 = 0;
    v_buckets_4319_ = crate::leanh::lean_ctor_get(v_m_4317_, 1);
    v___x_4320_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4321_ = lean_array_get_size(v_buckets_4319_);
    v___x_4322_ = lean_nat_dec_lt(v___x_4320_, v___x_4321_);
    if v___x_4322_ == 0 {
        crate::leanh::lean_dec(v_l_4318_);
        crate::leanh::lean_dec(v_inst_4316_);
        crate::leanh::lean_dec_ref(v_inst_4314_);
        crate::leanh::lean_dec_ref(v_inst_4313_);
        return v_m_4317_;
    } else {
        let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4324_: *mut crate::leanh::LeanObject,
    mut v_inst_4325_: *mut crate::leanh::LeanObject,
    mut v_l_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: u8 = 0;
    v___x_4327_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_4328_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_4328_ == 0 {
        crate::leanh::lean_dec_ref(v_l_4326_);
        crate::leanh::lean_dec_ref(v_inst_4325_);
        crate::leanh::lean_dec_ref(v_inst_4324_);
        return v___x_4327_;
    } else {
        let mut v___f_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4331_: *mut crate::leanh::LeanObject,
    mut v_inst_4332_: *mut crate::leanh::LeanObject,
    mut v_inst_4333_: *mut crate::leanh::LeanObject,
    mut v_l_4334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: u8 = 0;
    v___x_4335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_4336_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_4336_ == 0 {
        crate::leanh::lean_dec_ref(v_l_4334_);
        crate::leanh::lean_dec_ref(v_inst_4333_);
        crate::leanh::lean_dec_ref(v_inst_4332_);
        return v___x_4335_;
    } else {
        let mut v___f_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4340_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_4339_);
    return v___x_4340_;
}
pub unsafe fn l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(
    mut v_m_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_4341_);
    crate::leanh::lean_dec_ref(v_m_4341_);
    return v_res_4342_;
}
pub unsafe fn l_Std_HashMap_Raw_Internal_numBuckets(
    mut v_00_u03b1_4343_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4344_: *mut crate::leanh::LeanObject,
    mut v_m_4345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_4345_);
    return v___x_4346_;
}
pub unsafe fn l_Std_HashMap_Raw_Internal_numBuckets___boxed(
    mut v_00_u03b1_4347_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4348_: *mut crate::leanh::LeanObject,
    mut v_m_4349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4350_ =
        l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_4347_, v_00_u03b2_4348_, v_m_4349_);
    crate::leanh::lean_dec_ref(v_m_4349_);
    return v_res_4350_;
}
pub unsafe fn l_Std_HashMap_Raw_instRepr___redArg___lam__2(
    mut v___x_4354_: *mut crate::leanh::LeanObject,
    mut v___f_4355_: *mut crate::leanh::LeanObject,
    mut v_m_4356_: *mut crate::leanh::LeanObject,
    mut v_prec_4357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___f_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: usize = 0;
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v_unused_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4358_ = l_Std_HashMap_Raw_keys___redArg___closed__9;
                v_buckets_4359_ = crate::leanh::lean_ctor_get(v_m_4356_, 1);
                v_isSharedCheck_4379_ = (!crate::leanh::lean_is_exclusive(v_m_4356_)) as u8;
                if v_isSharedCheck_4379_ == 0 {
                    v_unused_4380_ = crate::leanh::lean_ctor_get(v_m_4356_, 0);
                    crate::leanh::lean_dec(v_unused_4380_);
                    v___x_4361_ = v_m_4356_;
                    v_isShared_4362_ = v_isSharedCheck_4379_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4359_);
                    crate::leanh::lean_dec(v_m_4356_);
                    v___x_4361_ = crate::leanh::lean_box(0);
                    v_isShared_4362_ = v_isSharedCheck_4379_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4363_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1;
                v___x_4371_ = crate::leanh::lean_box(0);
                v___x_4372_ = lean_array_get_size(v_buckets_4359_);
                v___x_4373_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4374_ = lean_nat_dec_lt(v___x_4373_, v___x_4372_);
                if v___x_4374_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_4359_);
                    crate::leanh::lean_dec_ref(v___f_4355_);
                    v___y_4365_ = v___x_4371_;
                    state = 2;
                    continue;
                } else {
                    v___f_4375_ = crate::leanh::lean_alloc_closure(
                        l_Std_HashMap_Raw_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_4375_, 0, v___x_4358_);
                    crate::leanh::lean_closure_set(v___f_4375_, 1, v___f_4355_);
                    v___x_4376_ = lean_usize_of_nat(v___x_4372_);
                    v___x_4377_ = 0usize;
                    v___x_4378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
                    crate::leanh::lean_ctor_set_tag(v___x_4361_, 5);
                    crate::leanh::lean_ctor_set(v___x_4361_, 1, v___x_4366_);
                    crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4363_);
                    v___x_4368_ = v___x_4361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 1, v___x_4366_);
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
    mut v___x_4381_: *mut crate::leanh::LeanObject,
    mut v___f_4382_: *mut crate::leanh::LeanObject,
    mut v_m_4383_: *mut crate::leanh::LeanObject,
    mut v_prec_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4385_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(
        v___x_4381_,
        v___f_4382_,
        v_m_4383_,
        v_prec_4384_,
    );
    crate::leanh::lean_dec(v_prec_4384_);
    return v_res_4385_;
}
pub unsafe fn l_Std_HashMap_Raw_instRepr___redArg(
    mut v_inst_4386_: *mut crate::leanh::LeanObject,
    mut v_inst_4387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4388_ = l_Std_HashMap_Raw_toList___redArg___closed__0;
    v___f_4389_ = crate::leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4389_, 0, v_inst_4387_);
    v___x_4390_ =
        crate::leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_4390_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4390_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4390_, 2, v_inst_4386_);
    crate::leanh::lean_closure_set(v___x_4390_, 3, v___f_4389_);
    v___f_4391_ = crate::leanh::lean_alloc_closure(
        l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4391_, 0, v___x_4390_);
    crate::leanh::lean_closure_set(v___f_4391_, 1, v___f_4388_);
    return v___f_4391_;
}
pub unsafe fn l_Std_HashMap_Raw_instRepr(
    mut v_00_u03b1_4392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4393_: *mut crate::leanh::LeanObject,
    mut v_inst_4394_: *mut crate::leanh::LeanObject,
    mut v_inst_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4396_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_4394_, v_inst_4395_);
    return v___x_4396_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_Raw(
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
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_Raw(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashMap_Raw(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_Raw(builtin);
}
