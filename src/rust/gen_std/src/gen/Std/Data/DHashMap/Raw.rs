// Lean compiler output
// Module: Std.Data.DHashMap.Raw
// Imports: Init.Data.LawfulHashable Std.Data.DHashMap.Internal.Defs Std.Data.DHashMap.Internal.Defs
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
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_Raw_instEmptyCollection___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__0_value: leanh::LeanStringObject<4> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__1_value: leanh::LeanStringObject<9> =
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
        m_data: [68, 72, 97, 115, 104, 77, 97, 112, 0],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__2_value: leanh::LeanStringObject<4> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__3_value: leanh::LeanStringObject<9> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__1_value)
                as *mut leanh::LeanObject,
            18035583711357664763 as *mut leanh::LeanObject,
        ],
    };
static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value)
                as *mut leanh::LeanObject,
            4155810031736705028 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__3_value)
                as *mut leanh::LeanObject,
            14381247710261688386 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__5_value: leanh::LeanStringObject<8> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__5_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__7_value: leanh::LeanStringObject<5> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__8_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__9_value: leanh::LeanStringObject<5> =
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
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__9_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__11_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__10_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_term___x7em___00__closed__13_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__4_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_term___x7em___00__closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_DHashMap_Raw_term___x7em__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [82, 97, 119, 46, 69, 113, 117, 105, 118, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value) as *mut leanh::LeanObject;
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value) as *mut leanh::LeanObject,3422484220311391684 as *mut leanh::LeanObject] };
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value) as *mut leanh::LeanObject,16179887037867133675 as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value) as *mut leanh::LeanObject;
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__1_value) as *mut leanh::LeanObject,18035583711357664763 as *mut leanh::LeanObject] };
static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw_term___x7em___00__closed__2_value) as *mut leanh::LeanObject,4155810031736705028 as *mut leanh::LeanObject] };
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value) as *mut leanh::LeanObject,8373056252130840875 as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value) as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value) as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1: u8 =
    0;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toArray___redArg___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_toArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1_value:
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
    m_fun: l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_keysArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keysArray___redArg___closed__1_value:
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
    m_fun: l_Std_DHashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_keysArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keysArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_union___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_union___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_union___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_values___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_values___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_values___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_values___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_values___redArg___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_values___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_values___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_values___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_values___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_valuesArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_valuesArray___redArg___closed__1_value:
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
    m_fun: l_Std_DHashMap_Raw_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_valuesArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_valuesArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toList___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_toList___redArg___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_DHashMap_Raw_toList___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_toList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_toList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_toList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value:
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
    m_fun: l_Std_DHashMap_Raw_Const_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Raw_Const_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_Const_toList___redArg___closed__1_value:
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
    m_fun: l_Std_DHashMap_Raw_Const_toList___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_Const_toList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_Const_toList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keys___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_DHashMap_Raw_keys___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keys___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_keys___redArg___closed__1_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_DHashMap_Raw_values___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Raw_keys___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_DHashMap_Raw_keys___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_keys___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_ofList___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_ofList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_ofList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Raw_ofList___redArg___closed__1_value: leanh::LeanClosureObject<
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
        core::ptr::addr_of!(l_Std_DHashMap_Raw_ofList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Raw_ofList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Raw_ofList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity___redArg(
    mut v_capacity_2640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ = leanh::lean_unsigned_to_nat(0);
    v___x_2642_ = leanh::lean_unsigned_to_nat(4);
    v___x_2643_ = lean_nat_mul(v_capacity_2640_, v___x_2642_);
    v___x_2644_ = leanh::lean_unsigned_to_nat(3);
    v___x_2645_ = lean_nat_div(v___x_2643_, v___x_2644_);
    leanh::lean_dec(v___x_2643_);
    v___x_2646_ = l_Nat_nextPowerOfTwo(v___x_2645_);
    leanh::lean_dec(v___x_2645_);
    v___x_2647_ = leanh::lean_box(0);
    v___x_2648_ = lean_mk_array(v___x_2646_, v___x_2647_);
    v___x_2649_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2649_, 0, v___x_2641_);
    leanh::lean_ctor_set(v___x_2649_, 1, v___x_2648_);
    return v___x_2649_;
}
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity___redArg___boxed(
    mut v_capacity_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Std_DHashMap_Raw_emptyWithCapacity___redArg(v_capacity_2650_);
    leanh::lean_dec(v_capacity_2650_);
    return v_res_2651_;
}
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity(
    mut v_00_u03b1_2652_: *mut leanh::LeanObject,
    mut v_00_u03b2_2653_: *mut leanh::LeanObject,
    mut v_capacity_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = leanh::lean_unsigned_to_nat(0);
    v___x_2656_ = leanh::lean_unsigned_to_nat(4);
    v___x_2657_ = lean_nat_mul(v_capacity_2654_, v___x_2656_);
    v___x_2658_ = leanh::lean_unsigned_to_nat(3);
    v___x_2659_ = lean_nat_div(v___x_2657_, v___x_2658_);
    leanh::lean_dec(v___x_2657_);
    v___x_2660_ = l_Nat_nextPowerOfTwo(v___x_2659_);
    leanh::lean_dec(v___x_2659_);
    v___x_2661_ = leanh::lean_box(0);
    v___x_2662_ = lean_mk_array(v___x_2660_, v___x_2661_);
    v___x_2663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2663_, 0, v___x_2655_);
    leanh::lean_ctor_set(v___x_2663_, 1, v___x_2662_);
    return v___x_2663_;
}
pub unsafe fn l_Std_DHashMap_Raw_emptyWithCapacity___boxed(
    mut v_00_u03b1_2664_: *mut leanh::LeanObject,
    mut v_00_u03b2_2665_: *mut leanh::LeanObject,
    mut v_capacity_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2667_ =
        l_Std_DHashMap_Raw_emptyWithCapacity(v_00_u03b1_2664_, v_00_u03b2_2665_, v_capacity_2666_);
    leanh::lean_dec(v_capacity_2666_);
    return v_res_2667_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = leanh::lean_box(0);
    v___x_2669_ = leanh::lean_unsigned_to_nat(16);
    v___x_2670_ = lean_mk_array(v___x_2669_, v___x_2668_);
    return v___x_2670_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2672_ = leanh::lean_unsigned_to_nat(0);
    v___x_2673_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2673_, 0, v___x_2672_);
    leanh::lean_ctor_set(v___x_2673_, 1, v___x_2671_);
    return v___x_2673_;
}
pub unsafe fn l_Std_DHashMap_Raw_instEmptyCollection(
    mut v_00_u03b1_2674_: *mut leanh::LeanObject,
    mut v_00_u03b2_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2676_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInhabited(
    mut v_00_u03b1_2677_: *mut leanh::LeanObject,
    mut v_00_u03b2_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2679_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    return v___x_2679_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5;
    v___x_2721_ = l_String_toRawSubstring_x27(v___x_2720_);
    return v___x_2721_;
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(
    mut v_x_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: u8 = 0;
    v___x_2748_ = l_Std_DHashMap_Raw_term___x7em___00__closed__4;
    leanh::lean_inc(v_x_2745_);
    v___x_2749_ = l_Lean_Syntax_isOfKind(v_x_2745_, v___x_2748_);
    if v___x_2749_ == 0 {
        let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2745_);
        v___x_2750_ = leanh::lean_box(1);
        v___x_2751_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2751_, 0, v___x_2750_);
        leanh::lean_ctor_set(v___x_2751_, 1, v_a_2747_);
        return v___x_2751_;
    } else {
        let mut v_quotContext_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2759_: u8 = 0;
        let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2752_ = leanh::lean_ctor_get(v_a_2746_, 1);
        v_currMacroScope_2753_ = leanh::lean_ctor_get(v_a_2746_, 2);
        v_ref_2754_ = leanh::lean_ctor_get(v_a_2746_, 5);
        v___x_2755_ = leanh::lean_unsigned_to_nat(0);
        v___x_2756_ = l_Lean_Syntax_getArg(v_x_2745_, v___x_2755_);
        v___x_2757_ = leanh::lean_unsigned_to_nat(2);
        v___x_2758_ = l_Lean_Syntax_getArg(v_x_2745_, v___x_2757_);
        leanh::lean_dec(v_x_2745_);
        v___x_2759_ = 0;
        v___x_2760_ = l_Lean_SourceInfo_fromRef(v_ref_2754_, v___x_2759_);
        v___x_2761_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4;
        v___x_2762_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once), _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
        v___x_2763_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8;
        leanh::lean_inc(v_currMacroScope_2753_);
        leanh::lean_inc(v_quotContext_2752_);
        v___x_2764_ =
            l_Lean_addMacroScope(v_quotContext_2752_, v___x_2763_, v_currMacroScope_2753_);
        v___x_2765_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13;
        leanh::lean_inc_n(v___x_2760_, 2);
        v___x_2766_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2766_, 0, v___x_2760_);
        leanh::lean_ctor_set(v___x_2766_, 1, v___x_2762_);
        leanh::lean_ctor_set(v___x_2766_, 2, v___x_2764_);
        leanh::lean_ctor_set(v___x_2766_, 3, v___x_2765_);
        v___x_2767_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15;
        v___x_2768_ = l_Lean_Syntax_node2(v___x_2760_, v___x_2767_, v___x_2756_, v___x_2758_);
        v___x_2769_ = l_Lean_Syntax_node2(v___x_2760_, v___x_2761_, v___x_2766_, v___x_2768_);
        v___x_2770_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2770_, 0, v___x_2769_);
        leanh::lean_ctor_set(v___x_2770_, 1, v_a_2747_);
        return v___x_2770_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(
    mut v_x_2771_: *mut leanh::LeanObject,
    mut v_a_2772_: *mut leanh::LeanObject,
    mut v_a_2773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(v_x_2771_, v_a_2772_, v_a_2773_);
    leanh::lean_dec_ref(v_a_2772_);
    return v_res_2774_;
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(
    mut v_x_2778_: *mut leanh::LeanObject,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: u8 = 0;
    v___x_2781_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4;
    leanh::lean_inc(v_x_2778_);
    v___x_2782_ = l_Lean_Syntax_isOfKind(v_x_2778_, v___x_2781_);
    if v___x_2782_ == 0 {
        let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2778_);
        v___x_2783_ = leanh::lean_box(0);
        v___x_2784_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2784_, 0, v___x_2783_);
        leanh::lean_ctor_set(v___x_2784_, 1, v_a_2780_);
        return v___x_2784_;
    } else {
        let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2788_: u8 = 0;
        v___x_2785_ = leanh::lean_unsigned_to_nat(0);
        v___x_2786_ = l_Lean_Syntax_getArg(v_x_2778_, v___x_2785_);
        v___x_2787_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1;
        leanh::lean_inc(v___x_2786_);
        v___x_2788_ = l_Lean_Syntax_isOfKind(v___x_2786_, v___x_2787_);
        if v___x_2788_ == 0 {
            let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2786_);
            leanh::lean_dec(v_x_2778_);
            v___x_2789_ = leanh::lean_box(0);
            v___x_2790_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2790_, 0, v___x_2789_);
            leanh::lean_ctor_set(v___x_2790_, 1, v_a_2780_);
            return v___x_2790_;
        } else {
            let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2794_: u8 = 0;
            v___x_2791_ = leanh::lean_unsigned_to_nat(1);
            v___x_2792_ = l_Lean_Syntax_getArg(v_x_2778_, v___x_2791_);
            leanh::lean_dec(v_x_2778_);
            v___x_2793_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_2792_);
            v___x_2794_ = l_Lean_Syntax_matchesNull(v___x_2792_, v___x_2793_);
            if v___x_2794_ == 0 {
                let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_2792_);
                leanh::lean_dec(v___x_2786_);
                v___x_2795_ = leanh::lean_box(0);
                v___x_2796_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                leanh::lean_ctor_set(v___x_2796_, 1, v_a_2780_);
                return v___x_2796_;
            } else {
                let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2800_: u8 = 0;
                let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2797_ = l_Lean_Syntax_getArg(v___x_2792_, v___x_2785_);
                v___x_2798_ = l_Lean_Syntax_getArg(v___x_2792_, v___x_2791_);
                leanh::lean_dec(v___x_2792_);
                v_ref_2799_ = l_Lean_replaceRef(v___x_2786_, v_a_2779_);
                leanh::lean_dec(v___x_2786_);
                v___x_2800_ = 0;
                v___x_2801_ = l_Lean_SourceInfo_fromRef(v_ref_2799_, v___x_2800_);
                leanh::lean_dec(v_ref_2799_);
                v___x_2802_ = l_Std_DHashMap_Raw_term___x7em___00__closed__4;
                v___x_2803_ = l_Std_DHashMap_Raw_term___x7em___00__closed__7;
                leanh::lean_inc(v___x_2801_);
                v___x_2804_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2804_, 0, v___x_2801_);
                leanh::lean_ctor_set(v___x_2804_, 1, v___x_2803_);
                v___x_2805_ = l_Lean_Syntax_node3(
                    v___x_2801_,
                    v___x_2802_,
                    v___x_2797_,
                    v___x_2804_,
                    v___x_2798_,
                );
                v___x_2806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2806_, 0, v___x_2805_);
                leanh::lean_ctor_set(v___x_2806_, 1, v_a_2780_);
                return v___x_2806_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(
    mut v_x_2807_: *mut leanh::LeanObject,
    mut v_a_2808_: *mut leanh::LeanObject,
    mut v_a_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_2807_, v_a_2808_, v_a_2809_);
    leanh::lean_dec(v_a_2808_);
    return v_res_2810_;
}
pub unsafe fn l_Std_DHashMap_Raw_insert___redArg(
    mut v_inst_2811_: *mut leanh::LeanObject,
    mut v_inst_2812_: *mut leanh::LeanObject,
    mut v_m_2813_: *mut leanh::LeanObject,
    mut v_a_2814_: *mut leanh::LeanObject,
    mut v_b_2815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    v_buckets_2816_ = leanh::lean_ctor_get(v_m_2813_, 1);
    v___x_2817_ = leanh::lean_unsigned_to_nat(0);
    v___x_2818_ = lean_array_get_size(v_buckets_2816_);
    v___x_2819_ = lean_nat_dec_lt(v___x_2817_, v___x_2818_);
    if v___x_2819_ == 0 {
        leanh::lean_dec(v_b_2815_);
        leanh::lean_dec(v_a_2814_);
        leanh::lean_dec_ref(v_inst_2812_);
        leanh::lean_dec_ref(v_inst_2811_);
        return v_m_2813_;
    } else {
        let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2821_: *mut leanh::LeanObject,
    mut v_00_u03b2_2822_: *mut leanh::LeanObject,
    mut v_inst_2823_: *mut leanh::LeanObject,
    mut v_inst_2824_: *mut leanh::LeanObject,
    mut v_m_2825_: *mut leanh::LeanObject,
    mut v_a_2826_: *mut leanh::LeanObject,
    mut v_b_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v_buckets_2828_ = leanh::lean_ctor_get(v_m_2825_, 1);
    v___x_2829_ = leanh::lean_unsigned_to_nat(0);
    v___x_2830_ = lean_array_get_size(v_buckets_2828_);
    v___x_2831_ = lean_nat_dec_lt(v___x_2829_, v___x_2830_);
    if v___x_2831_ == 0 {
        leanh::lean_dec(v_b_2827_);
        leanh::lean_dec(v_a_2826_);
        leanh::lean_dec_ref(v_inst_2824_);
        leanh::lean_dec_ref(v_inst_2823_);
        return v_m_2825_;
    } else {
        let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
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
-> *mut leanh::LeanObject {
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2833_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0,
    );
    v___x_2834_ = lean_array_get_size(v___x_2833_);
    return v___x_2834_;
}
pub unsafe fn _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1()
-> u8 {
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    v___x_2835_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0,
    );
    v___x_2836_ = leanh::lean_unsigned_to_nat(0);
    v___x_2837_ = lean_nat_dec_lt(v___x_2836_, v___x_2835_);
    return v___x_2837_;
}
pub unsafe fn l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2838_: *mut leanh::LeanObject,
    mut v_inst_2839_: *mut leanh::LeanObject,
    mut v_x_2840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u8 = 0;
    v_fst_2841_ = leanh::lean_ctor_get(v_x_2840_, 0);
    leanh::lean_inc(v_fst_2841_);
    v_snd_2842_ = leanh::lean_ctor_get(v_x_2840_, 1);
    leanh::lean_inc(v_snd_2842_);
    leanh::lean_dec_ref(v_x_2840_);
    v___x_2843_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_2844_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2844_ == 0 {
        leanh::lean_dec(v_snd_2842_);
        leanh::lean_dec(v_fst_2841_);
        leanh::lean_dec_ref(v_inst_2839_);
        leanh::lean_dec_ref(v_inst_2838_);
        return v___x_2843_;
    } else {
        let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2846_: *mut leanh::LeanObject,
    mut v_inst_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2848_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2848_, 0, v_inst_2846_);
    leanh::lean_closure_set(v___f_2848_, 1, v_inst_2847_);
    return v___f_2848_;
}
pub unsafe fn l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(
    mut v_00_u03b1_2849_: *mut leanh::LeanObject,
    mut v_00_u03b2_2850_: *mut leanh::LeanObject,
    mut v_inst_2851_: *mut leanh::LeanObject,
    mut v_inst_2852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2853_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2853_, 0, v_inst_2851_);
    leanh::lean_closure_set(v___f_2853_, 1, v_inst_2852_);
    return v___f_2853_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(
    mut v_inst_2854_: *mut leanh::LeanObject,
    mut v_inst_2855_: *mut leanh::LeanObject,
    mut v_x_2856_: *mut leanh::LeanObject,
    mut v_s_2857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    v_fst_2858_ = leanh::lean_ctor_get(v_x_2856_, 0);
    leanh::lean_inc(v_fst_2858_);
    v_snd_2859_ = leanh::lean_ctor_get(v_x_2856_, 1);
    leanh::lean_inc(v_snd_2859_);
    leanh::lean_dec_ref(v_x_2856_);
    v_buckets_2860_ = leanh::lean_ctor_get(v_s_2857_, 1);
    v___x_2861_ = leanh::lean_unsigned_to_nat(0);
    v___x_2862_ = lean_array_get_size(v_buckets_2860_);
    v___x_2863_ = lean_nat_dec_lt(v___x_2861_, v___x_2862_);
    if v___x_2863_ == 0 {
        leanh::lean_dec(v_snd_2859_);
        leanh::lean_dec(v_fst_2858_);
        leanh::lean_dec_ref(v_inst_2855_);
        leanh::lean_dec_ref(v_inst_2854_);
        return v_s_2857_;
    } else {
        let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2865_: *mut leanh::LeanObject,
    mut v_inst_2866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2867_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2867_, 0, v_inst_2865_);
    leanh::lean_closure_set(v___f_2867_, 1, v_inst_2866_);
    return v___f_2867_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(
    mut v_00_u03b1_2868_: *mut leanh::LeanObject,
    mut v_00_u03b2_2869_: *mut leanh::LeanObject,
    mut v_inst_2870_: *mut leanh::LeanObject,
    mut v_inst_2871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2872_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2872_, 0, v_inst_2870_);
    leanh::lean_closure_set(v___f_2872_, 1, v_inst_2871_);
    return v___f_2872_;
}
pub unsafe fn l_Std_DHashMap_Raw_insertIfNew___redArg(
    mut v_inst_2873_: *mut leanh::LeanObject,
    mut v_inst_2874_: *mut leanh::LeanObject,
    mut v_m_2875_: *mut leanh::LeanObject,
    mut v_a_2876_: *mut leanh::LeanObject,
    mut v_b_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    v_buckets_2878_ = leanh::lean_ctor_get(v_m_2875_, 1);
    v___x_2879_ = leanh::lean_unsigned_to_nat(0);
    v___x_2880_ = lean_array_get_size(v_buckets_2878_);
    v___x_2881_ = lean_nat_dec_lt(v___x_2879_, v___x_2880_);
    if v___x_2881_ == 0 {
        leanh::lean_dec(v_b_2877_);
        leanh::lean_dec(v_a_2876_);
        leanh::lean_dec_ref(v_inst_2874_);
        leanh::lean_dec_ref(v_inst_2873_);
        return v_m_2875_;
    } else {
        let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2883_: *mut leanh::LeanObject,
    mut v_00_u03b2_2884_: *mut leanh::LeanObject,
    mut v_inst_2885_: *mut leanh::LeanObject,
    mut v_inst_2886_: *mut leanh::LeanObject,
    mut v_m_2887_: *mut leanh::LeanObject,
    mut v_a_2888_: *mut leanh::LeanObject,
    mut v_b_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    v_buckets_2890_ = leanh::lean_ctor_get(v_m_2887_, 1);
    v___x_2891_ = leanh::lean_unsigned_to_nat(0);
    v___x_2892_ = lean_array_get_size(v_buckets_2890_);
    v___x_2893_ = lean_nat_dec_lt(v___x_2891_, v___x_2892_);
    if v___x_2893_ == 0 {
        leanh::lean_dec(v_b_2889_);
        leanh::lean_dec(v_a_2888_);
        leanh::lean_dec_ref(v_inst_2886_);
        leanh::lean_dec_ref(v_inst_2885_);
        return v_m_2887_;
    } else {
        let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2895_: *mut leanh::LeanObject,
    mut v_inst_2896_: *mut leanh::LeanObject,
    mut v_m_2897_: *mut leanh::LeanObject,
    mut v_a_2898_: *mut leanh::LeanObject,
    mut v_b_2899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: u8 = 0;
    let mut v_val_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_unused_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2900_ = leanh::lean_ctor_get(v_m_2897_, 0);
                v_buckets_2901_ = leanh::lean_ctor_get(v_m_2897_, 1);
                v___x_2902_ = leanh::lean_unsigned_to_nat(0);
                v___x_2903_ = lean_array_get_size(v_buckets_2901_);
                v___x_2904_ = lean_nat_dec_lt(v___x_2902_, v___x_2903_);
                if v___x_2904_ == 0 {
                    leanh::lean_dec(v_b_2899_);
                    leanh::lean_dec(v_a_2898_);
                    leanh::lean_dec_ref(v_inst_2896_);
                    leanh::lean_dec_ref(v_inst_2895_);
                    v___x_2905_ = leanh::lean_box((v___x_2904_) as usize);
                    v___x_2906_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2906_, 0, v___x_2905_);
                    leanh::lean_ctor_set(v___x_2906_, 1, v_m_2897_);
                    return v___x_2906_;
                } else {
                    leanh::lean_inc_ref(v_buckets_2901_);
                    leanh::lean_inc(v_size_2900_);
                    v_isSharedCheck_2956_ = (!leanh::lean_is_exclusive(v_m_2897_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v_unused_2957_ = leanh::lean_ctor_get(v_m_2897_, 1);
                        leanh::lean_dec(v_unused_2957_);
                        v_unused_2958_ = leanh::lean_ctor_get(v_m_2897_, 0);
                        leanh::lean_dec(v_unused_2958_);
                        v___x_2908_ = v_m_2897_;
                        v_isShared_2909_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2897_);
                        v___x_2908_ = leanh::lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2956_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_2896_);
                leanh::lean_inc_n(v_a_2898_, 2);
                v___x_2910_ = leanh::lean_apply_1(v_inst_2896_, v_a_2898_);
                v___x_2911_ = 32u64;
                v___x_2912_ = leanh::lean_unbox_uint64(v___x_2910_);
                v___x_2913_ = lean_uint64_shift_right(v___x_2912_, v___x_2911_);
                v___x_2914_ = leanh::lean_unbox_uint64(v___x_2910_);
                leanh::lean_dec_ref(v___x_2910_);
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
                leanh::lean_inc(v_bkt_2924_);
                leanh::lean_inc_ref(v_inst_2895_);
                v___x_2925_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2895_,
                    v_a_2898_,
                    v_bkt_2924_,
                );
                if v___x_2925_ == 0 {
                    leanh::lean_dec_ref(v_inst_2895_);
                    v___x_2926_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2927_ = lean_nat_add(v_size_2900_, v___x_2926_);
                    leanh::lean_dec(v_size_2900_);
                    leanh::lean_inc(v_bkt_2924_);
                    v___x_2928_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2928_, 0, v_a_2898_);
                    leanh::lean_ctor_set(v___x_2928_, 1, v_b_2899_);
                    leanh::lean_ctor_set(v___x_2928_, 2, v_bkt_2924_);
                    v_buckets_x27_2929_ =
                        lean_array_uset(v_buckets_2901_, v___x_2923_, v___x_2928_);
                    v___x_2930_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2931_ = lean_nat_mul(v_size_x27_2927_, v___x_2930_);
                    v___x_2932_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2933_ = lean_nat_div(v___x_2931_, v___x_2932_);
                    leanh::lean_dec(v___x_2931_);
                    v___x_2934_ = lean_array_get_size(v_buckets_x27_2929_);
                    v___x_2935_ = lean_nat_dec_le(v___x_2933_, v___x_2934_);
                    leanh::lean_dec(v___x_2933_);
                    if v___x_2935_ == 0 {
                        v_val_2936_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2896_,
                            v_buckets_x27_2929_,
                        );
                        if v_isShared_2909_ == 0 {
                            leanh::lean_ctor_set(v___x_2908_, 1, v_val_2936_);
                            leanh::lean_ctor_set(v___x_2908_, 0, v_size_x27_2927_);
                            v___x_2938_ = v___x_2908_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2941_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2941_,
                                0,
                                v_size_x27_2927_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_val_2936_);
                            v___x_2938_ = v_reuseFailAlloc_2941_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_2896_);
                        if v_isShared_2909_ == 0 {
                            leanh::lean_ctor_set(v___x_2908_, 1, v_buckets_x27_2929_);
                            leanh::lean_ctor_set(v___x_2908_, 0, v_size_x27_2927_);
                            v___x_2943_ = v___x_2908_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2946_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2946_,
                                0,
                                v_size_x27_2927_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_2924_);
                    leanh::lean_dec_ref(v_inst_2896_);
                    v___x_2947_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_2908_, 1, v___x_2950_);
                        v___x_2952_ = v___x_2908_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2955_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_size_2900_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 1, v___x_2950_);
                        v___x_2952_ = v_reuseFailAlloc_2955_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2939_ = leanh::lean_box((v___x_2925_) as usize);
                v___x_2940_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2940_, 0, v___x_2939_);
                leanh::lean_ctor_set(v___x_2940_, 1, v___x_2938_);
                return v___x_2940_;
            }
            3 => {
                v___x_2944_ = leanh::lean_box((v___x_2925_) as usize);
                v___x_2945_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2945_, 0, v___x_2944_);
                leanh::lean_ctor_set(v___x_2945_, 1, v___x_2943_);
                return v___x_2945_;
            }
            4 => {
                v___x_2953_ = leanh::lean_box((v___x_2925_) as usize);
                v___x_2954_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2954_, 0, v___x_2953_);
                leanh::lean_ctor_set(v___x_2954_, 1, v___x_2952_);
                return v___x_2954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_containsThenInsert(
    mut v_00_u03b1_2959_: *mut leanh::LeanObject,
    mut v_00_u03b2_2960_: *mut leanh::LeanObject,
    mut v_inst_2961_: *mut leanh::LeanObject,
    mut v_inst_2962_: *mut leanh::LeanObject,
    mut v_m_2963_: *mut leanh::LeanObject,
    mut v_a_2964_: *mut leanh::LeanObject,
    mut v_b_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2975_: u8 = 0;
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: u8 = 0;
    let mut v_val_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_unused_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2966_ = leanh::lean_ctor_get(v_m_2963_, 0);
                v_buckets_2967_ = leanh::lean_ctor_get(v_m_2963_, 1);
                v___x_2968_ = leanh::lean_unsigned_to_nat(0);
                v___x_2969_ = lean_array_get_size(v_buckets_2967_);
                v___x_2970_ = lean_nat_dec_lt(v___x_2968_, v___x_2969_);
                if v___x_2970_ == 0 {
                    leanh::lean_dec(v_b_2965_);
                    leanh::lean_dec(v_a_2964_);
                    leanh::lean_dec_ref(v_inst_2962_);
                    leanh::lean_dec_ref(v_inst_2961_);
                    v___x_2971_ = leanh::lean_box((v___x_2970_) as usize);
                    v___x_2972_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2972_, 0, v___x_2971_);
                    leanh::lean_ctor_set(v___x_2972_, 1, v_m_2963_);
                    return v___x_2972_;
                } else {
                    leanh::lean_inc_ref(v_buckets_2967_);
                    leanh::lean_inc(v_size_2966_);
                    v_isSharedCheck_3022_ = (!leanh::lean_is_exclusive(v_m_2963_)) as u8;
                    if v_isSharedCheck_3022_ == 0 {
                        v_unused_3023_ = leanh::lean_ctor_get(v_m_2963_, 1);
                        leanh::lean_dec(v_unused_3023_);
                        v_unused_3024_ = leanh::lean_ctor_get(v_m_2963_, 0);
                        leanh::lean_dec(v_unused_3024_);
                        v___x_2974_ = v_m_2963_;
                        v_isShared_2975_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2963_);
                        v___x_2974_ = leanh::lean_box(0);
                        v_isShared_2975_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_2962_);
                leanh::lean_inc_n(v_a_2964_, 2);
                v___x_2976_ = leanh::lean_apply_1(v_inst_2962_, v_a_2964_);
                v___x_2977_ = 32u64;
                v___x_2978_ = leanh::lean_unbox_uint64(v___x_2976_);
                v___x_2979_ = lean_uint64_shift_right(v___x_2978_, v___x_2977_);
                v___x_2980_ = leanh::lean_unbox_uint64(v___x_2976_);
                leanh::lean_dec_ref(v___x_2976_);
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
                leanh::lean_inc(v_bkt_2990_);
                leanh::lean_inc_ref(v_inst_2961_);
                v___x_2991_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2961_,
                    v_a_2964_,
                    v_bkt_2990_,
                );
                if v___x_2991_ == 0 {
                    leanh::lean_dec_ref(v_inst_2961_);
                    v___x_2992_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2993_ = lean_nat_add(v_size_2966_, v___x_2992_);
                    leanh::lean_dec(v_size_2966_);
                    leanh::lean_inc(v_bkt_2990_);
                    v___x_2994_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2994_, 0, v_a_2964_);
                    leanh::lean_ctor_set(v___x_2994_, 1, v_b_2965_);
                    leanh::lean_ctor_set(v___x_2994_, 2, v_bkt_2990_);
                    v_buckets_x27_2995_ =
                        lean_array_uset(v_buckets_2967_, v___x_2989_, v___x_2994_);
                    v___x_2996_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2997_ = lean_nat_mul(v_size_x27_2993_, v___x_2996_);
                    v___x_2998_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2999_ = lean_nat_div(v___x_2997_, v___x_2998_);
                    leanh::lean_dec(v___x_2997_);
                    v___x_3000_ = lean_array_get_size(v_buckets_x27_2995_);
                    v___x_3001_ = lean_nat_dec_le(v___x_2999_, v___x_3000_);
                    leanh::lean_dec(v___x_2999_);
                    if v___x_3001_ == 0 {
                        v_val_3002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2962_,
                            v_buckets_x27_2995_,
                        );
                        if v_isShared_2975_ == 0 {
                            leanh::lean_ctor_set(v___x_2974_, 1, v_val_3002_);
                            leanh::lean_ctor_set(v___x_2974_, 0, v_size_x27_2993_);
                            v___x_3004_ = v___x_2974_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3007_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3007_,
                                0,
                                v_size_x27_2993_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_val_3002_);
                            v___x_3004_ = v_reuseFailAlloc_3007_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_2962_);
                        if v_isShared_2975_ == 0 {
                            leanh::lean_ctor_set(v___x_2974_, 1, v_buckets_x27_2995_);
                            leanh::lean_ctor_set(v___x_2974_, 0, v_size_x27_2993_);
                            v___x_3009_ = v___x_2974_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3012_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3012_,
                                0,
                                v_size_x27_2993_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_2990_);
                    leanh::lean_dec_ref(v_inst_2962_);
                    v___x_3013_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_2974_, 1, v___x_3016_);
                        v___x_3018_ = v___x_2974_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_size_2966_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3016_);
                        v___x_3018_ = v_reuseFailAlloc_3021_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3005_ = leanh::lean_box((v___x_2991_) as usize);
                v___x_3006_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3006_, 0, v___x_3005_);
                leanh::lean_ctor_set(v___x_3006_, 1, v___x_3004_);
                return v___x_3006_;
            }
            3 => {
                v___x_3010_ = leanh::lean_box((v___x_2991_) as usize);
                v___x_3011_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3011_, 0, v___x_3010_);
                leanh::lean_ctor_set(v___x_3011_, 1, v___x_3009_);
                return v___x_3011_;
            }
            4 => {
                v___x_3019_ = leanh::lean_box((v___x_2991_) as usize);
                v___x_3020_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3020_, 0, v___x_3019_);
                leanh::lean_ctor_set(v___x_3020_, 1, v___x_3018_);
                return v___x_3020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(
    mut v_inst_3025_: *mut leanh::LeanObject,
    mut v_inst_3026_: *mut leanh::LeanObject,
    mut v_m_3027_: *mut leanh::LeanObject,
    mut v_a_3028_: *mut leanh::LeanObject,
    mut v_b_3029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: u8 = 0;
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3055_: u8 = 0;
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v_val_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3075_: u8 = 0;
    let mut v_unused_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3030_ = leanh::lean_ctor_get(v_m_3027_, 0);
                v_buckets_3031_ = leanh::lean_ctor_get(v_m_3027_, 1);
                v___x_3032_ = leanh::lean_unsigned_to_nat(0);
                v___x_3033_ = lean_array_get_size(v_buckets_3031_);
                v___x_3034_ = lean_nat_dec_lt(v___x_3032_, v___x_3033_);
                if v___x_3034_ == 0 {
                    leanh::lean_dec(v_b_3029_);
                    leanh::lean_dec(v_a_3028_);
                    leanh::lean_dec_ref(v_inst_3026_);
                    leanh::lean_dec_ref(v_inst_3025_);
                    v___x_3035_ = leanh::lean_box(0);
                    v___x_3036_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3036_, 0, v___x_3035_);
                    leanh::lean_ctor_set(v___x_3036_, 1, v_m_3027_);
                    return v___x_3036_;
                } else {
                    leanh::lean_inc_ref(v_inst_3026_);
                    leanh::lean_inc_n(v_a_3028_, 2);
                    v___x_3037_ = leanh::lean_apply_1(v_inst_3026_, v_a_3028_);
                    v___x_3038_ = 32u64;
                    v___x_3039_ = leanh::lean_unbox_uint64(v___x_3037_);
                    v___x_3040_ = lean_uint64_shift_right(v___x_3039_, v___x_3038_);
                    v___x_3041_ = leanh::lean_unbox_uint64(v___x_3037_);
                    leanh::lean_dec_ref(v___x_3037_);
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
                    leanh::lean_inc(v_bkt_3051_);
                    v___x_3052_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                        v_inst_3025_,
                        v_a_3028_,
                        v_bkt_3051_,
                    );
                    if leanh::lean_obj_tag(v___x_3052_) == 0 {
                        leanh::lean_inc_ref(v_buckets_3031_);
                        leanh::lean_inc(v_size_3030_);
                        v_isSharedCheck_3075_ = (!leanh::lean_is_exclusive(v_m_3027_)) as u8;
                        if v_isSharedCheck_3075_ == 0 {
                            v_unused_3076_ = leanh::lean_ctor_get(v_m_3027_, 1);
                            leanh::lean_dec(v_unused_3076_);
                            v_unused_3077_ = leanh::lean_ctor_get(v_m_3027_, 0);
                            leanh::lean_dec(v_unused_3077_);
                            v___x_3054_ = v_m_3027_;
                            v_isShared_3055_ = v_isSharedCheck_3075_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_3027_);
                            v___x_3054_ = leanh::lean_box(0);
                            v_isShared_3055_ = v_isSharedCheck_3075_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_3029_);
                        leanh::lean_dec(v_a_3028_);
                        leanh::lean_dec_ref(v_inst_3026_);
                        v___x_3078_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3078_, 0, v___x_3052_);
                        leanh::lean_ctor_set(v___x_3078_, 1, v_m_3027_);
                        return v___x_3078_;
                    }
                }
            }
            1 => {
                v___x_3056_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3057_ = lean_nat_add(v_size_3030_, v___x_3056_);
                leanh::lean_dec(v_size_3030_);
                leanh::lean_inc(v_bkt_3051_);
                v___x_3058_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3058_, 0, v_a_3028_);
                leanh::lean_ctor_set(v___x_3058_, 1, v_b_3029_);
                leanh::lean_ctor_set(v___x_3058_, 2, v_bkt_3051_);
                v_buckets_x27_3059_ = lean_array_uset(v_buckets_3031_, v___x_3050_, v___x_3058_);
                v___x_3060_ = leanh::lean_unsigned_to_nat(4);
                v___x_3061_ = lean_nat_mul(v_size_x27_3057_, v___x_3060_);
                v___x_3062_ = leanh::lean_unsigned_to_nat(3);
                v___x_3063_ = lean_nat_div(v___x_3061_, v___x_3062_);
                leanh::lean_dec(v___x_3061_);
                v___x_3064_ = lean_array_get_size(v_buckets_x27_3059_);
                v___x_3065_ = lean_nat_dec_le(v___x_3063_, v___x_3064_);
                leanh::lean_dec(v___x_3063_);
                if v___x_3065_ == 0 {
                    v_val_3066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3026_,
                        v_buckets_x27_3059_,
                    );
                    if v_isShared_3055_ == 0 {
                        leanh::lean_ctor_set(v___x_3054_, 1, v_val_3066_);
                        leanh::lean_ctor_set(v___x_3054_, 0, v_size_x27_3057_);
                        v___x_3068_ = v___x_3054_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3070_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_size_x27_3057_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_val_3066_);
                        v___x_3068_ = v_reuseFailAlloc_3070_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3026_);
                    if v_isShared_3055_ == 0 {
                        leanh::lean_ctor_set(v___x_3054_, 1, v_buckets_x27_3059_);
                        leanh::lean_ctor_set(v___x_3054_, 0, v_size_x27_3057_);
                        v___x_3072_ = v___x_3054_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_size_x27_3057_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_buckets_x27_3059_);
                        v___x_3072_ = v_reuseFailAlloc_3074_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3069_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3069_, 0, v___x_3052_);
                leanh::lean_ctor_set(v___x_3069_, 1, v___x_3068_);
                return v___x_3069_;
            }
            3 => {
                v___x_3073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3073_, 0, v___x_3052_);
                leanh::lean_ctor_set(v___x_3073_, 1, v___x_3072_);
                return v___x_3073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(
    mut v_00_u03b1_3079_: *mut leanh::LeanObject,
    mut v_00_u03b2_3080_: *mut leanh::LeanObject,
    mut v_inst_3081_: *mut leanh::LeanObject,
    mut v_inst_3082_: *mut leanh::LeanObject,
    mut v_inst_3083_: *mut leanh::LeanObject,
    mut v_m_3084_: *mut leanh::LeanObject,
    mut v_a_3085_: *mut leanh::LeanObject,
    mut v_b_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3112_: u8 = 0;
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v_val_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_unused_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3087_ = leanh::lean_ctor_get(v_m_3084_, 0);
                v_buckets_3088_ = leanh::lean_ctor_get(v_m_3084_, 1);
                v___x_3089_ = leanh::lean_unsigned_to_nat(0);
                v___x_3090_ = lean_array_get_size(v_buckets_3088_);
                v___x_3091_ = lean_nat_dec_lt(v___x_3089_, v___x_3090_);
                if v___x_3091_ == 0 {
                    leanh::lean_dec(v_b_3086_);
                    leanh::lean_dec(v_a_3085_);
                    leanh::lean_dec_ref(v_inst_3082_);
                    leanh::lean_dec_ref(v_inst_3081_);
                    v___x_3092_ = leanh::lean_box(0);
                    v___x_3093_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3093_, 0, v___x_3092_);
                    leanh::lean_ctor_set(v___x_3093_, 1, v_m_3084_);
                    return v___x_3093_;
                } else {
                    leanh::lean_inc_ref(v_inst_3082_);
                    leanh::lean_inc_n(v_a_3085_, 2);
                    v___x_3094_ = leanh::lean_apply_1(v_inst_3082_, v_a_3085_);
                    v___x_3095_ = 32u64;
                    v___x_3096_ = leanh::lean_unbox_uint64(v___x_3094_);
                    v___x_3097_ = lean_uint64_shift_right(v___x_3096_, v___x_3095_);
                    v___x_3098_ = leanh::lean_unbox_uint64(v___x_3094_);
                    leanh::lean_dec_ref(v___x_3094_);
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
                    leanh::lean_inc(v_bkt_3108_);
                    v___x_3109_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                        v_inst_3081_,
                        v_a_3085_,
                        v_bkt_3108_,
                    );
                    if leanh::lean_obj_tag(v___x_3109_) == 0 {
                        leanh::lean_inc_ref(v_buckets_3088_);
                        leanh::lean_inc(v_size_3087_);
                        v_isSharedCheck_3132_ = (!leanh::lean_is_exclusive(v_m_3084_)) as u8;
                        if v_isSharedCheck_3132_ == 0 {
                            v_unused_3133_ = leanh::lean_ctor_get(v_m_3084_, 1);
                            leanh::lean_dec(v_unused_3133_);
                            v_unused_3134_ = leanh::lean_ctor_get(v_m_3084_, 0);
                            leanh::lean_dec(v_unused_3134_);
                            v___x_3111_ = v_m_3084_;
                            v_isShared_3112_ = v_isSharedCheck_3132_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_3084_);
                            v___x_3111_ = leanh::lean_box(0);
                            v_isShared_3112_ = v_isSharedCheck_3132_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_3086_);
                        leanh::lean_dec(v_a_3085_);
                        leanh::lean_dec_ref(v_inst_3082_);
                        v___x_3135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3135_, 0, v___x_3109_);
                        leanh::lean_ctor_set(v___x_3135_, 1, v_m_3084_);
                        return v___x_3135_;
                    }
                }
            }
            1 => {
                v___x_3113_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3114_ = lean_nat_add(v_size_3087_, v___x_3113_);
                leanh::lean_dec(v_size_3087_);
                leanh::lean_inc(v_bkt_3108_);
                v___x_3115_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3115_, 0, v_a_3085_);
                leanh::lean_ctor_set(v___x_3115_, 1, v_b_3086_);
                leanh::lean_ctor_set(v___x_3115_, 2, v_bkt_3108_);
                v_buckets_x27_3116_ = lean_array_uset(v_buckets_3088_, v___x_3107_, v___x_3115_);
                v___x_3117_ = leanh::lean_unsigned_to_nat(4);
                v___x_3118_ = lean_nat_mul(v_size_x27_3114_, v___x_3117_);
                v___x_3119_ = leanh::lean_unsigned_to_nat(3);
                v___x_3120_ = lean_nat_div(v___x_3118_, v___x_3119_);
                leanh::lean_dec(v___x_3118_);
                v___x_3121_ = lean_array_get_size(v_buckets_x27_3116_);
                v___x_3122_ = lean_nat_dec_le(v___x_3120_, v___x_3121_);
                leanh::lean_dec(v___x_3120_);
                if v___x_3122_ == 0 {
                    v_val_3123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3082_,
                        v_buckets_x27_3116_,
                    );
                    if v_isShared_3112_ == 0 {
                        leanh::lean_ctor_set(v___x_3111_, 1, v_val_3123_);
                        leanh::lean_ctor_set(v___x_3111_, 0, v_size_x27_3114_);
                        v___x_3125_ = v___x_3111_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_size_x27_3114_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_val_3123_);
                        v___x_3125_ = v_reuseFailAlloc_3127_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3082_);
                    if v_isShared_3112_ == 0 {
                        leanh::lean_ctor_set(v___x_3111_, 1, v_buckets_x27_3116_);
                        leanh::lean_ctor_set(v___x_3111_, 0, v_size_x27_3114_);
                        v___x_3129_ = v___x_3111_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3131_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_size_x27_3114_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_buckets_x27_3116_);
                        v___x_3129_ = v_reuseFailAlloc_3131_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3126_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3126_, 0, v___x_3109_);
                leanh::lean_ctor_set(v___x_3126_, 1, v___x_3125_);
                return v___x_3126_;
            }
            3 => {
                v___x_3130_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3130_, 0, v___x_3109_);
                leanh::lean_ctor_set(v___x_3130_, 1, v___x_3129_);
                return v___x_3130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(
    mut v_inst_3136_: *mut leanh::LeanObject,
    mut v_inst_3137_: *mut leanh::LeanObject,
    mut v_m_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_b_3140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v_val_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v_unused_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3141_ = leanh::lean_ctor_get(v_m_3138_, 0);
                v_buckets_3142_ = leanh::lean_ctor_get(v_m_3138_, 1);
                v___x_3143_ = leanh::lean_unsigned_to_nat(0);
                v___x_3144_ = lean_array_get_size(v_buckets_3142_);
                v___x_3145_ = lean_nat_dec_lt(v___x_3143_, v___x_3144_);
                if v___x_3145_ == 0 {
                    leanh::lean_dec(v_b_3140_);
                    leanh::lean_dec(v_a_3139_);
                    leanh::lean_dec_ref(v_inst_3137_);
                    leanh::lean_dec_ref(v_inst_3136_);
                    v___x_3146_ = leanh::lean_box((v___x_3145_) as usize);
                    v___x_3147_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3147_, 0, v___x_3146_);
                    leanh::lean_ctor_set(v___x_3147_, 1, v_m_3138_);
                    return v___x_3147_;
                } else {
                    leanh::lean_inc_ref(v_inst_3137_);
                    leanh::lean_inc_n(v_a_3139_, 2);
                    v___x_3148_ = leanh::lean_apply_1(v_inst_3137_, v_a_3139_);
                    v___x_3149_ = 32u64;
                    v___x_3150_ = leanh::lean_unbox_uint64(v___x_3148_);
                    v___x_3151_ = lean_uint64_shift_right(v___x_3150_, v___x_3149_);
                    v___x_3152_ = leanh::lean_unbox_uint64(v___x_3148_);
                    leanh::lean_dec_ref(v___x_3148_);
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
                    leanh::lean_inc(v_bkt_3162_);
                    v___x_3163_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_3136_,
                        v_a_3139_,
                        v_bkt_3162_,
                    );
                    if v___x_3163_ == 0 {
                        leanh::lean_inc_ref(v_buckets_3142_);
                        leanh::lean_inc(v_size_3141_);
                        v_isSharedCheck_3188_ = (!leanh::lean_is_exclusive(v_m_3138_)) as u8;
                        if v_isSharedCheck_3188_ == 0 {
                            v_unused_3189_ = leanh::lean_ctor_get(v_m_3138_, 1);
                            leanh::lean_dec(v_unused_3189_);
                            v_unused_3190_ = leanh::lean_ctor_get(v_m_3138_, 0);
                            leanh::lean_dec(v_unused_3190_);
                            v___x_3165_ = v_m_3138_;
                            v_isShared_3166_ = v_isSharedCheck_3188_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_3138_);
                            v___x_3165_ = leanh::lean_box(0);
                            v_isShared_3166_ = v_isSharedCheck_3188_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_3140_);
                        leanh::lean_dec(v_a_3139_);
                        leanh::lean_dec_ref(v_inst_3137_);
                        v___x_3191_ = leanh::lean_box((v___x_3163_) as usize);
                        v___x_3192_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3192_, 0, v___x_3191_);
                        leanh::lean_ctor_set(v___x_3192_, 1, v_m_3138_);
                        return v___x_3192_;
                    }
                }
            }
            1 => {
                v___x_3167_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3168_ = lean_nat_add(v_size_3141_, v___x_3167_);
                leanh::lean_dec(v_size_3141_);
                leanh::lean_inc(v_bkt_3162_);
                v___x_3169_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3169_, 0, v_a_3139_);
                leanh::lean_ctor_set(v___x_3169_, 1, v_b_3140_);
                leanh::lean_ctor_set(v___x_3169_, 2, v_bkt_3162_);
                v_buckets_x27_3170_ = lean_array_uset(v_buckets_3142_, v___x_3161_, v___x_3169_);
                v___x_3171_ = leanh::lean_unsigned_to_nat(4);
                v___x_3172_ = lean_nat_mul(v_size_x27_3168_, v___x_3171_);
                v___x_3173_ = leanh::lean_unsigned_to_nat(3);
                v___x_3174_ = lean_nat_div(v___x_3172_, v___x_3173_);
                leanh::lean_dec(v___x_3172_);
                v___x_3175_ = lean_array_get_size(v_buckets_x27_3170_);
                v___x_3176_ = lean_nat_dec_le(v___x_3174_, v___x_3175_);
                leanh::lean_dec(v___x_3174_);
                if v___x_3176_ == 0 {
                    v_val_3177_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3137_,
                        v_buckets_x27_3170_,
                    );
                    if v_isShared_3166_ == 0 {
                        leanh::lean_ctor_set(v___x_3165_, 1, v_val_3177_);
                        leanh::lean_ctor_set(v___x_3165_, 0, v_size_x27_3168_);
                        v___x_3179_ = v___x_3165_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3182_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_size_x27_3168_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_val_3177_);
                        v___x_3179_ = v_reuseFailAlloc_3182_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3137_);
                    if v_isShared_3166_ == 0 {
                        leanh::lean_ctor_set(v___x_3165_, 1, v_buckets_x27_3170_);
                        leanh::lean_ctor_set(v___x_3165_, 0, v_size_x27_3168_);
                        v___x_3184_ = v___x_3165_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3187_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_size_x27_3168_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_buckets_x27_3170_);
                        v___x_3184_ = v_reuseFailAlloc_3187_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3180_ = leanh::lean_box((v___x_3163_) as usize);
                v___x_3181_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3181_, 0, v___x_3180_);
                leanh::lean_ctor_set(v___x_3181_, 1, v___x_3179_);
                return v___x_3181_;
            }
            3 => {
                v___x_3185_ = leanh::lean_box((v___x_3163_) as usize);
                v___x_3186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3186_, 0, v___x_3185_);
                leanh::lean_ctor_set(v___x_3186_, 1, v___x_3184_);
                return v___x_3186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_containsThenInsertIfNew(
    mut v_00_u03b1_3193_: *mut leanh::LeanObject,
    mut v_00_u03b2_3194_: *mut leanh::LeanObject,
    mut v_inst_3195_: *mut leanh::LeanObject,
    mut v_inst_3196_: *mut leanh::LeanObject,
    mut v_m_3197_: *mut leanh::LeanObject,
    mut v_a_3198_: *mut leanh::LeanObject,
    mut v_b_3199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u8 = 0;
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: u8 = 0;
    let mut v_val_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_unused_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3200_ = leanh::lean_ctor_get(v_m_3197_, 0);
                v_buckets_3201_ = leanh::lean_ctor_get(v_m_3197_, 1);
                v___x_3202_ = leanh::lean_unsigned_to_nat(0);
                v___x_3203_ = lean_array_get_size(v_buckets_3201_);
                v___x_3204_ = lean_nat_dec_lt(v___x_3202_, v___x_3203_);
                if v___x_3204_ == 0 {
                    leanh::lean_dec(v_b_3199_);
                    leanh::lean_dec(v_a_3198_);
                    leanh::lean_dec_ref(v_inst_3196_);
                    leanh::lean_dec_ref(v_inst_3195_);
                    v___x_3205_ = leanh::lean_box((v___x_3204_) as usize);
                    v___x_3206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3206_, 0, v___x_3205_);
                    leanh::lean_ctor_set(v___x_3206_, 1, v_m_3197_);
                    return v___x_3206_;
                } else {
                    leanh::lean_inc_ref(v_inst_3196_);
                    leanh::lean_inc_n(v_a_3198_, 2);
                    v___x_3207_ = leanh::lean_apply_1(v_inst_3196_, v_a_3198_);
                    v___x_3208_ = 32u64;
                    v___x_3209_ = leanh::lean_unbox_uint64(v___x_3207_);
                    v___x_3210_ = lean_uint64_shift_right(v___x_3209_, v___x_3208_);
                    v___x_3211_ = leanh::lean_unbox_uint64(v___x_3207_);
                    leanh::lean_dec_ref(v___x_3207_);
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
                    leanh::lean_inc(v_bkt_3221_);
                    v___x_3222_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_3195_,
                        v_a_3198_,
                        v_bkt_3221_,
                    );
                    if v___x_3222_ == 0 {
                        leanh::lean_inc_ref(v_buckets_3201_);
                        leanh::lean_inc(v_size_3200_);
                        v_isSharedCheck_3247_ = (!leanh::lean_is_exclusive(v_m_3197_)) as u8;
                        if v_isSharedCheck_3247_ == 0 {
                            v_unused_3248_ = leanh::lean_ctor_get(v_m_3197_, 1);
                            leanh::lean_dec(v_unused_3248_);
                            v_unused_3249_ = leanh::lean_ctor_get(v_m_3197_, 0);
                            leanh::lean_dec(v_unused_3249_);
                            v___x_3224_ = v_m_3197_;
                            v_isShared_3225_ = v_isSharedCheck_3247_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_3197_);
                            v___x_3224_ = leanh::lean_box(0);
                            v_isShared_3225_ = v_isSharedCheck_3247_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_3199_);
                        leanh::lean_dec(v_a_3198_);
                        leanh::lean_dec_ref(v_inst_3196_);
                        v___x_3250_ = leanh::lean_box((v___x_3222_) as usize);
                        v___x_3251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3251_, 0, v___x_3250_);
                        leanh::lean_ctor_set(v___x_3251_, 1, v_m_3197_);
                        return v___x_3251_;
                    }
                }
            }
            1 => {
                v___x_3226_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3227_ = lean_nat_add(v_size_3200_, v___x_3226_);
                leanh::lean_dec(v_size_3200_);
                leanh::lean_inc(v_bkt_3221_);
                v___x_3228_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3228_, 0, v_a_3198_);
                leanh::lean_ctor_set(v___x_3228_, 1, v_b_3199_);
                leanh::lean_ctor_set(v___x_3228_, 2, v_bkt_3221_);
                v_buckets_x27_3229_ = lean_array_uset(v_buckets_3201_, v___x_3220_, v___x_3228_);
                v___x_3230_ = leanh::lean_unsigned_to_nat(4);
                v___x_3231_ = lean_nat_mul(v_size_x27_3227_, v___x_3230_);
                v___x_3232_ = leanh::lean_unsigned_to_nat(3);
                v___x_3233_ = lean_nat_div(v___x_3231_, v___x_3232_);
                leanh::lean_dec(v___x_3231_);
                v___x_3234_ = lean_array_get_size(v_buckets_x27_3229_);
                v___x_3235_ = lean_nat_dec_le(v___x_3233_, v___x_3234_);
                leanh::lean_dec(v___x_3233_);
                if v___x_3235_ == 0 {
                    v_val_3236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3196_,
                        v_buckets_x27_3229_,
                    );
                    if v_isShared_3225_ == 0 {
                        leanh::lean_ctor_set(v___x_3224_, 1, v_val_3236_);
                        leanh::lean_ctor_set(v___x_3224_, 0, v_size_x27_3227_);
                        v___x_3238_ = v___x_3224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3241_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_size_x27_3227_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_val_3236_);
                        v___x_3238_ = v_reuseFailAlloc_3241_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3196_);
                    if v_isShared_3225_ == 0 {
                        leanh::lean_ctor_set(v___x_3224_, 1, v_buckets_x27_3229_);
                        leanh::lean_ctor_set(v___x_3224_, 0, v_size_x27_3227_);
                        v___x_3243_ = v___x_3224_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3246_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_size_x27_3227_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_buckets_x27_3229_);
                        v___x_3243_ = v_reuseFailAlloc_3246_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3239_ = leanh::lean_box((v___x_3222_) as usize);
                v___x_3240_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3240_, 0, v___x_3239_);
                leanh::lean_ctor_set(v___x_3240_, 1, v___x_3238_);
                return v___x_3240_;
            }
            3 => {
                v___x_3244_ = leanh::lean_box((v___x_3222_) as usize);
                v___x_3245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3245_, 0, v___x_3244_);
                leanh::lean_ctor_set(v___x_3245_, 1, v___x_3243_);
                return v___x_3245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_get_x3f___redArg(
    mut v_inst_3252_: *mut leanh::LeanObject,
    mut v_inst_3253_: *mut leanh::LeanObject,
    mut v_m_3254_: *mut leanh::LeanObject,
    mut v_a_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: u8 = 0;
    v_buckets_3256_ = leanh::lean_ctor_get(v_m_3254_, 1);
    v___x_3257_ = leanh::lean_unsigned_to_nat(0);
    v___x_3258_ = lean_array_get_size(v_buckets_3256_);
    v___x_3259_ = lean_nat_dec_lt(v___x_3257_, v___x_3258_);
    if v___x_3259_ == 0 {
        let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3255_);
        leanh::lean_dec_ref(v_inst_3253_);
        leanh::lean_dec_ref(v_inst_3252_);
        v___x_3260_ = leanh::lean_box(0);
        return v___x_3260_;
    } else {
        let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3262_: *mut leanh::LeanObject,
    mut v_inst_3263_: *mut leanh::LeanObject,
    mut v_m_3264_: *mut leanh::LeanObject,
    mut v_a_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ =
        l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_3262_, v_inst_3263_, v_m_3264_, v_a_3265_);
    leanh::lean_dec_ref(v_m_3264_);
    return v_res_3266_;
}
pub unsafe fn l_Std_DHashMap_Raw_get_x3f(
    mut v_00_u03b1_3267_: *mut leanh::LeanObject,
    mut v_00_u03b2_3268_: *mut leanh::LeanObject,
    mut v_inst_3269_: *mut leanh::LeanObject,
    mut v_inst_3270_: *mut leanh::LeanObject,
    mut v_inst_3271_: *mut leanh::LeanObject,
    mut v_m_3272_: *mut leanh::LeanObject,
    mut v_a_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    v_buckets_3274_ = leanh::lean_ctor_get(v_m_3272_, 1);
    v___x_3275_ = leanh::lean_unsigned_to_nat(0);
    v___x_3276_ = lean_array_get_size(v_buckets_3274_);
    v___x_3277_ = lean_nat_dec_lt(v___x_3275_, v___x_3276_);
    if v___x_3277_ == 0 {
        let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3273_);
        leanh::lean_dec_ref(v_inst_3271_);
        leanh::lean_dec_ref(v_inst_3269_);
        v___x_3278_ = leanh::lean_box(0);
        return v___x_3278_;
    } else {
        let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3280_: *mut leanh::LeanObject,
    mut v_00_u03b2_3281_: *mut leanh::LeanObject,
    mut v_inst_3282_: *mut leanh::LeanObject,
    mut v_inst_3283_: *mut leanh::LeanObject,
    mut v_inst_3284_: *mut leanh::LeanObject,
    mut v_m_3285_: *mut leanh::LeanObject,
    mut v_a_3286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3287_ = l_Std_DHashMap_Raw_get_x3f(
        v_00_u03b1_3280_,
        v_00_u03b2_3281_,
        v_inst_3282_,
        v_inst_3283_,
        v_inst_3284_,
        v_m_3285_,
        v_a_3286_,
    );
    leanh::lean_dec_ref(v_m_3285_);
    return v_res_3287_;
}
pub unsafe fn l_Std_DHashMap_Raw_contains___redArg(
    mut v_inst_3288_: *mut leanh::LeanObject,
    mut v_inst_3289_: *mut leanh::LeanObject,
    mut v_m_3290_: *mut leanh::LeanObject,
    mut v_a_3291_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    v_buckets_3292_ = leanh::lean_ctor_get(v_m_3290_, 1);
    v___x_3293_ = leanh::lean_unsigned_to_nat(0);
    v___x_3294_ = lean_array_get_size(v_buckets_3292_);
    v___x_3295_ = lean_nat_dec_lt(v___x_3293_, v___x_3294_);
    if v___x_3295_ == 0 {
        leanh::lean_dec(v_a_3291_);
        leanh::lean_dec_ref(v_inst_3289_);
        leanh::lean_dec_ref(v_inst_3288_);
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
    mut v_inst_3297_: *mut leanh::LeanObject,
    mut v_inst_3298_: *mut leanh::LeanObject,
    mut v_m_3299_: *mut leanh::LeanObject,
    mut v_a_3300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3301_: u8 = 0;
    let mut v_r_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3301_ =
        l_Std_DHashMap_Raw_contains___redArg(v_inst_3297_, v_inst_3298_, v_m_3299_, v_a_3300_);
    leanh::lean_dec_ref(v_m_3299_);
    v_r_3302_ = leanh::lean_box((v_res_3301_) as usize);
    return v_r_3302_;
}
pub unsafe fn l_Std_DHashMap_Raw_contains(
    mut v_00_u03b1_3303_: *mut leanh::LeanObject,
    mut v_00_u03b2_3304_: *mut leanh::LeanObject,
    mut v_inst_3305_: *mut leanh::LeanObject,
    mut v_inst_3306_: *mut leanh::LeanObject,
    mut v_m_3307_: *mut leanh::LeanObject,
    mut v_a_3308_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: u8 = 0;
    v_buckets_3309_ = leanh::lean_ctor_get(v_m_3307_, 1);
    v___x_3310_ = leanh::lean_unsigned_to_nat(0);
    v___x_3311_ = lean_array_get_size(v_buckets_3309_);
    v___x_3312_ = lean_nat_dec_lt(v___x_3310_, v___x_3311_);
    if v___x_3312_ == 0 {
        leanh::lean_dec(v_a_3308_);
        leanh::lean_dec_ref(v_inst_3306_);
        leanh::lean_dec_ref(v_inst_3305_);
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
    mut v_00_u03b1_3314_: *mut leanh::LeanObject,
    mut v_00_u03b2_3315_: *mut leanh::LeanObject,
    mut v_inst_3316_: *mut leanh::LeanObject,
    mut v_inst_3317_: *mut leanh::LeanObject,
    mut v_m_3318_: *mut leanh::LeanObject,
    mut v_a_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3320_: u8 = 0;
    let mut v_r_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Std_DHashMap_Raw_contains(
        v_00_u03b1_3314_,
        v_00_u03b2_3315_,
        v_inst_3316_,
        v_inst_3317_,
        v_m_3318_,
        v_a_3319_,
    );
    leanh::lean_dec_ref(v_m_3318_);
    v_r_3321_ = leanh::lean_box((v_res_3320_) as usize);
    return v_r_3321_;
}
pub unsafe fn l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(
    mut v_00_u03b1_3322_: *mut leanh::LeanObject,
    mut v_00_u03b2_3323_: *mut leanh::LeanObject,
    mut v_inst_3324_: *mut leanh::LeanObject,
    mut v_inst_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3326_ = leanh::lean_box(0);
    return v___x_3326_;
}
pub unsafe fn l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(
    mut v_00_u03b1_3327_: *mut leanh::LeanObject,
    mut v_00_u03b2_3328_: *mut leanh::LeanObject,
    mut v_inst_3329_: *mut leanh::LeanObject,
    mut v_inst_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(
        v_00_u03b1_3327_,
        v_00_u03b2_3328_,
        v_inst_3329_,
        v_inst_3330_,
    );
    leanh::lean_dec_ref(v_inst_3330_);
    leanh::lean_dec_ref(v_inst_3329_);
    return v_res_3331_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableMem___redArg(
    mut v_inst_3332_: *mut leanh::LeanObject,
    mut v_inst_3333_: *mut leanh::LeanObject,
    mut v_m_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    v_buckets_3336_ = leanh::lean_ctor_get(v_m_3334_, 1);
    v___x_3337_ = leanh::lean_unsigned_to_nat(0);
    v___x_3338_ = lean_array_get_size(v_buckets_3336_);
    v___x_3339_ = lean_nat_dec_lt(v___x_3337_, v___x_3338_);
    if v___x_3339_ == 0 {
        leanh::lean_dec(v_a_3335_);
        leanh::lean_dec_ref(v_inst_3333_);
        leanh::lean_dec_ref(v_inst_3332_);
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
    mut v_inst_3341_: *mut leanh::LeanObject,
    mut v_inst_3342_: *mut leanh::LeanObject,
    mut v_m_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3345_: u8 = 0;
    let mut v_r_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3345_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(
        v_inst_3341_,
        v_inst_3342_,
        v_m_3343_,
        v_a_3344_,
    );
    leanh::lean_dec_ref(v_m_3343_);
    v_r_3346_ = leanh::lean_box((v_res_3345_) as usize);
    return v_r_3346_;
}
pub unsafe fn l_Std_DHashMap_Raw_instDecidableMem(
    mut v_00_u03b1_3347_: *mut leanh::LeanObject,
    mut v_00_u03b2_3348_: *mut leanh::LeanObject,
    mut v_inst_3349_: *mut leanh::LeanObject,
    mut v_inst_3350_: *mut leanh::LeanObject,
    mut v_m_3351_: *mut leanh::LeanObject,
    mut v_a_3352_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_3354_: *mut leanh::LeanObject,
    mut v_00_u03b2_3355_: *mut leanh::LeanObject,
    mut v_inst_3356_: *mut leanh::LeanObject,
    mut v_inst_3357_: *mut leanh::LeanObject,
    mut v_m_3358_: *mut leanh::LeanObject,
    mut v_a_3359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3360_: u8 = 0;
    let mut v_r_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3360_ = l_Std_DHashMap_Raw_instDecidableMem(
        v_00_u03b1_3354_,
        v_00_u03b2_3355_,
        v_inst_3356_,
        v_inst_3357_,
        v_m_3358_,
        v_a_3359_,
    );
    leanh::lean_dec_ref(v_m_3358_);
    v_r_3361_ = leanh::lean_box((v_res_3360_) as usize);
    return v_r_3361_;
}
pub unsafe fn l_Std_DHashMap_Raw_get___redArg(
    mut v_inst_3362_: *mut leanh::LeanObject,
    mut v_inst_3363_: *mut leanh::LeanObject,
    mut v_m_3364_: *mut leanh::LeanObject,
    mut v_a_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(
        v_inst_3362_,
        v_inst_3363_,
        v_m_3364_,
        v_a_3365_,
    );
    return v___x_3366_;
}
pub unsafe fn l_Std_DHashMap_Raw_get___redArg___boxed(
    mut v_inst_3367_: *mut leanh::LeanObject,
    mut v_inst_3368_: *mut leanh::LeanObject,
    mut v_m_3369_: *mut leanh::LeanObject,
    mut v_a_3370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3371_ = l_Std_DHashMap_Raw_get___redArg(v_inst_3367_, v_inst_3368_, v_m_3369_, v_a_3370_);
    leanh::lean_dec_ref(v_m_3369_);
    return v_res_3371_;
}
pub unsafe fn l_Std_DHashMap_Raw_get(
    mut v_00_u03b1_3372_: *mut leanh::LeanObject,
    mut v_00_u03b2_3373_: *mut leanh::LeanObject,
    mut v_inst_3374_: *mut leanh::LeanObject,
    mut v_inst_3375_: *mut leanh::LeanObject,
    mut v_inst_3376_: *mut leanh::LeanObject,
    mut v_m_3377_: *mut leanh::LeanObject,
    mut v_a_3378_: *mut leanh::LeanObject,
    mut v_h_3379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3380_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(
        v_inst_3374_,
        v_inst_3375_,
        v_m_3377_,
        v_a_3378_,
    );
    return v___x_3380_;
}
pub unsafe fn l_Std_DHashMap_Raw_get___boxed(
    mut v_00_u03b1_3381_: *mut leanh::LeanObject,
    mut v_00_u03b2_3382_: *mut leanh::LeanObject,
    mut v_inst_3383_: *mut leanh::LeanObject,
    mut v_inst_3384_: *mut leanh::LeanObject,
    mut v_inst_3385_: *mut leanh::LeanObject,
    mut v_m_3386_: *mut leanh::LeanObject,
    mut v_a_3387_: *mut leanh::LeanObject,
    mut v_h_3388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_m_3386_);
    return v_res_3389_;
}
pub unsafe fn l_Std_DHashMap_Raw_getD___redArg(
    mut v_inst_3390_: *mut leanh::LeanObject,
    mut v_inst_3391_: *mut leanh::LeanObject,
    mut v_m_3392_: *mut leanh::LeanObject,
    mut v_a_3393_: *mut leanh::LeanObject,
    mut v_fallback_3394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    v_buckets_3395_ = leanh::lean_ctor_get(v_m_3392_, 1);
    v___x_3396_ = leanh::lean_unsigned_to_nat(0);
    v___x_3397_ = lean_array_get_size(v_buckets_3395_);
    v___x_3398_ = lean_nat_dec_lt(v___x_3396_, v___x_3397_);
    if v___x_3398_ == 0 {
        leanh::lean_dec(v_a_3393_);
        leanh::lean_dec_ref(v_inst_3391_);
        leanh::lean_dec_ref(v_inst_3390_);
        leanh::lean_inc(v_fallback_3394_);
        return v_fallback_3394_;
    } else {
        let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3400_: *mut leanh::LeanObject,
    mut v_inst_3401_: *mut leanh::LeanObject,
    mut v_m_3402_: *mut leanh::LeanObject,
    mut v_a_3403_: *mut leanh::LeanObject,
    mut v_fallback_3404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3405_ = l_Std_DHashMap_Raw_getD___redArg(
        v_inst_3400_,
        v_inst_3401_,
        v_m_3402_,
        v_a_3403_,
        v_fallback_3404_,
    );
    leanh::lean_dec(v_fallback_3404_);
    leanh::lean_dec_ref(v_m_3402_);
    return v_res_3405_;
}
pub unsafe fn l_Std_DHashMap_Raw_getD(
    mut v_00_u03b1_3406_: *mut leanh::LeanObject,
    mut v_00_u03b2_3407_: *mut leanh::LeanObject,
    mut v_inst_3408_: *mut leanh::LeanObject,
    mut v_inst_3409_: *mut leanh::LeanObject,
    mut v_inst_3410_: *mut leanh::LeanObject,
    mut v_m_3411_: *mut leanh::LeanObject,
    mut v_a_3412_: *mut leanh::LeanObject,
    mut v_fallback_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    v_buckets_3414_ = leanh::lean_ctor_get(v_m_3411_, 1);
    v___x_3415_ = leanh::lean_unsigned_to_nat(0);
    v___x_3416_ = lean_array_get_size(v_buckets_3414_);
    v___x_3417_ = lean_nat_dec_lt(v___x_3415_, v___x_3416_);
    if v___x_3417_ == 0 {
        leanh::lean_dec(v_a_3412_);
        leanh::lean_dec_ref(v_inst_3409_);
        leanh::lean_dec_ref(v_inst_3408_);
        leanh::lean_inc(v_fallback_3413_);
        return v_fallback_3413_;
    } else {
        let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3419_: *mut leanh::LeanObject,
    mut v_00_u03b2_3420_: *mut leanh::LeanObject,
    mut v_inst_3421_: *mut leanh::LeanObject,
    mut v_inst_3422_: *mut leanh::LeanObject,
    mut v_inst_3423_: *mut leanh::LeanObject,
    mut v_m_3424_: *mut leanh::LeanObject,
    mut v_a_3425_: *mut leanh::LeanObject,
    mut v_fallback_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_fallback_3426_);
    leanh::lean_dec_ref(v_m_3424_);
    return v_res_3427_;
}
pub unsafe fn l_Std_DHashMap_Raw_get_x21___redArg(
    mut v_inst_3428_: *mut leanh::LeanObject,
    mut v_inst_3429_: *mut leanh::LeanObject,
    mut v_m_3430_: *mut leanh::LeanObject,
    mut v_a_3431_: *mut leanh::LeanObject,
    mut v_inst_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    v_buckets_3433_ = leanh::lean_ctor_get(v_m_3430_, 1);
    v___x_3434_ = leanh::lean_unsigned_to_nat(0);
    v___x_3435_ = lean_array_get_size(v_buckets_3433_);
    v___x_3436_ = lean_nat_dec_lt(v___x_3434_, v___x_3435_);
    if v___x_3436_ == 0 {
        leanh::lean_dec(v_a_3431_);
        leanh::lean_dec_ref(v_inst_3429_);
        leanh::lean_dec_ref(v_inst_3428_);
        leanh::lean_inc(v_inst_3432_);
        return v_inst_3432_;
    } else {
        let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3438_: *mut leanh::LeanObject,
    mut v_inst_3439_: *mut leanh::LeanObject,
    mut v_m_3440_: *mut leanh::LeanObject,
    mut v_a_3441_: *mut leanh::LeanObject,
    mut v_inst_3442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3443_ = l_Std_DHashMap_Raw_get_x21___redArg(
        v_inst_3438_,
        v_inst_3439_,
        v_m_3440_,
        v_a_3441_,
        v_inst_3442_,
    );
    leanh::lean_dec(v_inst_3442_);
    leanh::lean_dec_ref(v_m_3440_);
    return v_res_3443_;
}
pub unsafe fn l_Std_DHashMap_Raw_get_x21(
    mut v_00_u03b1_3444_: *mut leanh::LeanObject,
    mut v_00_u03b2_3445_: *mut leanh::LeanObject,
    mut v_inst_3446_: *mut leanh::LeanObject,
    mut v_inst_3447_: *mut leanh::LeanObject,
    mut v_inst_3448_: *mut leanh::LeanObject,
    mut v_m_3449_: *mut leanh::LeanObject,
    mut v_a_3450_: *mut leanh::LeanObject,
    mut v_inst_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: u8 = 0;
    v_buckets_3452_ = leanh::lean_ctor_get(v_m_3449_, 1);
    v___x_3453_ = leanh::lean_unsigned_to_nat(0);
    v___x_3454_ = lean_array_get_size(v_buckets_3452_);
    v___x_3455_ = lean_nat_dec_lt(v___x_3453_, v___x_3454_);
    if v___x_3455_ == 0 {
        leanh::lean_dec(v_a_3450_);
        leanh::lean_dec_ref(v_inst_3447_);
        leanh::lean_dec_ref(v_inst_3446_);
        leanh::lean_inc(v_inst_3451_);
        return v_inst_3451_;
    } else {
        let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3457_: *mut leanh::LeanObject,
    mut v_00_u03b2_3458_: *mut leanh::LeanObject,
    mut v_inst_3459_: *mut leanh::LeanObject,
    mut v_inst_3460_: *mut leanh::LeanObject,
    mut v_inst_3461_: *mut leanh::LeanObject,
    mut v_m_3462_: *mut leanh::LeanObject,
    mut v_a_3463_: *mut leanh::LeanObject,
    mut v_inst_3464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_inst_3464_);
    leanh::lean_dec_ref(v_m_3462_);
    return v_res_3465_;
}
pub unsafe fn l_Std_DHashMap_Raw_erase___redArg(
    mut v_inst_3466_: *mut leanh::LeanObject,
    mut v_inst_3467_: *mut leanh::LeanObject,
    mut v_m_3468_: *mut leanh::LeanObject,
    mut v_a_3469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: u8 = 0;
    v_buckets_3470_ = leanh::lean_ctor_get(v_m_3468_, 1);
    v___x_3471_ = leanh::lean_unsigned_to_nat(0);
    v___x_3472_ = lean_array_get_size(v_buckets_3470_);
    v___x_3473_ = lean_nat_dec_lt(v___x_3471_, v___x_3472_);
    if v___x_3473_ == 0 {
        leanh::lean_dec(v_a_3469_);
        leanh::lean_dec_ref(v_inst_3467_);
        leanh::lean_dec_ref(v_inst_3466_);
        return v_m_3468_;
    } else {
        let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3475_: *mut leanh::LeanObject,
    mut v_00_u03b2_3476_: *mut leanh::LeanObject,
    mut v_inst_3477_: *mut leanh::LeanObject,
    mut v_inst_3478_: *mut leanh::LeanObject,
    mut v_m_3479_: *mut leanh::LeanObject,
    mut v_a_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: u8 = 0;
    v_buckets_3481_ = leanh::lean_ctor_get(v_m_3479_, 1);
    v___x_3482_ = leanh::lean_unsigned_to_nat(0);
    v___x_3483_ = lean_array_get_size(v_buckets_3481_);
    v___x_3484_ = lean_nat_dec_lt(v___x_3482_, v___x_3483_);
    if v___x_3484_ == 0 {
        leanh::lean_dec(v_a_3480_);
        leanh::lean_dec_ref(v_inst_3478_);
        leanh::lean_dec_ref(v_inst_3477_);
        return v_m_3479_;
    } else {
        let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3486_: *mut leanh::LeanObject,
    mut v_inst_3487_: *mut leanh::LeanObject,
    mut v_m_3488_: *mut leanh::LeanObject,
    mut v_a_3489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: u8 = 0;
    v_buckets_3490_ = leanh::lean_ctor_get(v_m_3488_, 1);
    v___x_3491_ = leanh::lean_unsigned_to_nat(0);
    v___x_3492_ = lean_array_get_size(v_buckets_3490_);
    v___x_3493_ = lean_nat_dec_lt(v___x_3491_, v___x_3492_);
    if v___x_3493_ == 0 {
        let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3489_);
        leanh::lean_dec_ref(v_inst_3487_);
        leanh::lean_dec_ref(v_inst_3486_);
        v___x_3494_ = leanh::lean_box(0);
        return v___x_3494_;
    } else {
        let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3496_: *mut leanh::LeanObject,
    mut v_inst_3497_: *mut leanh::LeanObject,
    mut v_m_3498_: *mut leanh::LeanObject,
    mut v_a_3499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3500_ =
        l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_3496_, v_inst_3497_, v_m_3498_, v_a_3499_);
    leanh::lean_dec_ref(v_m_3498_);
    return v_res_3500_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x3f(
    mut v_00_u03b1_3501_: *mut leanh::LeanObject,
    mut v_00_u03b2_3502_: *mut leanh::LeanObject,
    mut v_inst_3503_: *mut leanh::LeanObject,
    mut v_inst_3504_: *mut leanh::LeanObject,
    mut v_m_3505_: *mut leanh::LeanObject,
    mut v_a_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: u8 = 0;
    v_buckets_3507_ = leanh::lean_ctor_get(v_m_3505_, 1);
    v___x_3508_ = leanh::lean_unsigned_to_nat(0);
    v___x_3509_ = lean_array_get_size(v_buckets_3507_);
    v___x_3510_ = lean_nat_dec_lt(v___x_3508_, v___x_3509_);
    if v___x_3510_ == 0 {
        let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3506_);
        leanh::lean_dec_ref(v_inst_3504_);
        leanh::lean_dec_ref(v_inst_3503_);
        v___x_3511_ = leanh::lean_box(0);
        return v___x_3511_;
    } else {
        let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3513_: *mut leanh::LeanObject,
    mut v_00_u03b2_3514_: *mut leanh::LeanObject,
    mut v_inst_3515_: *mut leanh::LeanObject,
    mut v_inst_3516_: *mut leanh::LeanObject,
    mut v_m_3517_: *mut leanh::LeanObject,
    mut v_a_3518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3519_ = l_Std_DHashMap_Raw_Const_get_x3f(
        v_00_u03b1_3513_,
        v_00_u03b2_3514_,
        v_inst_3515_,
        v_inst_3516_,
        v_m_3517_,
        v_a_3518_,
    );
    leanh::lean_dec_ref(v_m_3517_);
    return v_res_3519_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get___redArg(
    mut v_inst_3520_: *mut leanh::LeanObject,
    mut v_inst_3521_: *mut leanh::LeanObject,
    mut v_m_3522_: *mut leanh::LeanObject,
    mut v_a_3523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_3520_,
        v_inst_3521_,
        v_m_3522_,
        v_a_3523_,
    );
    return v___x_3524_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get___redArg___boxed(
    mut v_inst_3525_: *mut leanh::LeanObject,
    mut v_inst_3526_: *mut leanh::LeanObject,
    mut v_m_3527_: *mut leanh::LeanObject,
    mut v_a_3528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3529_ =
        l_Std_DHashMap_Raw_Const_get___redArg(v_inst_3525_, v_inst_3526_, v_m_3527_, v_a_3528_);
    leanh::lean_dec_ref(v_m_3527_);
    return v_res_3529_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get(
    mut v_00_u03b1_3530_: *mut leanh::LeanObject,
    mut v_00_u03b2_3531_: *mut leanh::LeanObject,
    mut v_inst_3532_: *mut leanh::LeanObject,
    mut v_inst_3533_: *mut leanh::LeanObject,
    mut v_m_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_h_3536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_3532_,
        v_inst_3533_,
        v_m_3534_,
        v_a_3535_,
    );
    return v___x_3537_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get___boxed(
    mut v_00_u03b1_3538_: *mut leanh::LeanObject,
    mut v_00_u03b2_3539_: *mut leanh::LeanObject,
    mut v_inst_3540_: *mut leanh::LeanObject,
    mut v_inst_3541_: *mut leanh::LeanObject,
    mut v_m_3542_: *mut leanh::LeanObject,
    mut v_a_3543_: *mut leanh::LeanObject,
    mut v_h_3544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3545_ = l_Std_DHashMap_Raw_Const_get(
        v_00_u03b1_3538_,
        v_00_u03b2_3539_,
        v_inst_3540_,
        v_inst_3541_,
        v_m_3542_,
        v_a_3543_,
        v_h_3544_,
    );
    leanh::lean_dec_ref(v_m_3542_);
    return v_res_3545_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getD___redArg(
    mut v_inst_3546_: *mut leanh::LeanObject,
    mut v_inst_3547_: *mut leanh::LeanObject,
    mut v_m_3548_: *mut leanh::LeanObject,
    mut v_a_3549_: *mut leanh::LeanObject,
    mut v_fallback_3550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: u8 = 0;
    v_buckets_3551_ = leanh::lean_ctor_get(v_m_3548_, 1);
    v___x_3552_ = leanh::lean_unsigned_to_nat(0);
    v___x_3553_ = lean_array_get_size(v_buckets_3551_);
    v___x_3554_ = lean_nat_dec_lt(v___x_3552_, v___x_3553_);
    if v___x_3554_ == 0 {
        leanh::lean_dec(v_a_3549_);
        leanh::lean_dec_ref(v_inst_3547_);
        leanh::lean_dec_ref(v_inst_3546_);
        leanh::lean_inc(v_fallback_3550_);
        return v_fallback_3550_;
    } else {
        let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3556_: *mut leanh::LeanObject,
    mut v_inst_3557_: *mut leanh::LeanObject,
    mut v_m_3558_: *mut leanh::LeanObject,
    mut v_a_3559_: *mut leanh::LeanObject,
    mut v_fallback_3560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l_Std_DHashMap_Raw_Const_getD___redArg(
        v_inst_3556_,
        v_inst_3557_,
        v_m_3558_,
        v_a_3559_,
        v_fallback_3560_,
    );
    leanh::lean_dec(v_fallback_3560_);
    leanh::lean_dec_ref(v_m_3558_);
    return v_res_3561_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getD(
    mut v_00_u03b1_3562_: *mut leanh::LeanObject,
    mut v_00_u03b2_3563_: *mut leanh::LeanObject,
    mut v_inst_3564_: *mut leanh::LeanObject,
    mut v_inst_3565_: *mut leanh::LeanObject,
    mut v_m_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
    mut v_fallback_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    v_buckets_3569_ = leanh::lean_ctor_get(v_m_3566_, 1);
    v___x_3570_ = leanh::lean_unsigned_to_nat(0);
    v___x_3571_ = lean_array_get_size(v_buckets_3569_);
    v___x_3572_ = lean_nat_dec_lt(v___x_3570_, v___x_3571_);
    if v___x_3572_ == 0 {
        leanh::lean_dec(v_a_3567_);
        leanh::lean_dec_ref(v_inst_3565_);
        leanh::lean_dec_ref(v_inst_3564_);
        leanh::lean_inc(v_fallback_3568_);
        return v_fallback_3568_;
    } else {
        let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3574_: *mut leanh::LeanObject,
    mut v_00_u03b2_3575_: *mut leanh::LeanObject,
    mut v_inst_3576_: *mut leanh::LeanObject,
    mut v_inst_3577_: *mut leanh::LeanObject,
    mut v_m_3578_: *mut leanh::LeanObject,
    mut v_a_3579_: *mut leanh::LeanObject,
    mut v_fallback_3580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Std_DHashMap_Raw_Const_getD(
        v_00_u03b1_3574_,
        v_00_u03b2_3575_,
        v_inst_3576_,
        v_inst_3577_,
        v_m_3578_,
        v_a_3579_,
        v_fallback_3580_,
    );
    leanh::lean_dec(v_fallback_3580_);
    leanh::lean_dec_ref(v_m_3578_);
    return v_res_3581_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x21___redArg(
    mut v_inst_3582_: *mut leanh::LeanObject,
    mut v_inst_3583_: *mut leanh::LeanObject,
    mut v_inst_3584_: *mut leanh::LeanObject,
    mut v_m_3585_: *mut leanh::LeanObject,
    mut v_a_3586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    v_buckets_3587_ = leanh::lean_ctor_get(v_m_3585_, 1);
    v___x_3588_ = leanh::lean_unsigned_to_nat(0);
    v___x_3589_ = lean_array_get_size(v_buckets_3587_);
    v___x_3590_ = lean_nat_dec_lt(v___x_3588_, v___x_3589_);
    if v___x_3590_ == 0 {
        leanh::lean_dec(v_a_3586_);
        leanh::lean_dec_ref(v_inst_3583_);
        leanh::lean_dec_ref(v_inst_3582_);
        leanh::lean_inc(v_inst_3584_);
        return v_inst_3584_;
    } else {
        let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3592_: *mut leanh::LeanObject,
    mut v_inst_3593_: *mut leanh::LeanObject,
    mut v_inst_3594_: *mut leanh::LeanObject,
    mut v_m_3595_: *mut leanh::LeanObject,
    mut v_a_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(
        v_inst_3592_,
        v_inst_3593_,
        v_inst_3594_,
        v_m_3595_,
        v_a_3596_,
    );
    leanh::lean_dec_ref(v_m_3595_);
    leanh::lean_dec(v_inst_3594_);
    return v_res_3597_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_get_x21(
    mut v_00_u03b1_3598_: *mut leanh::LeanObject,
    mut v_00_u03b2_3599_: *mut leanh::LeanObject,
    mut v_inst_3600_: *mut leanh::LeanObject,
    mut v_inst_3601_: *mut leanh::LeanObject,
    mut v_inst_3602_: *mut leanh::LeanObject,
    mut v_m_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: u8 = 0;
    v_buckets_3605_ = leanh::lean_ctor_get(v_m_3603_, 1);
    v___x_3606_ = leanh::lean_unsigned_to_nat(0);
    v___x_3607_ = lean_array_get_size(v_buckets_3605_);
    v___x_3608_ = lean_nat_dec_lt(v___x_3606_, v___x_3607_);
    if v___x_3608_ == 0 {
        leanh::lean_dec(v_a_3604_);
        leanh::lean_dec_ref(v_inst_3601_);
        leanh::lean_dec_ref(v_inst_3600_);
        leanh::lean_inc(v_inst_3602_);
        return v_inst_3602_;
    } else {
        let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3610_: *mut leanh::LeanObject,
    mut v_00_u03b2_3611_: *mut leanh::LeanObject,
    mut v_inst_3612_: *mut leanh::LeanObject,
    mut v_inst_3613_: *mut leanh::LeanObject,
    mut v_inst_3614_: *mut leanh::LeanObject,
    mut v_m_3615_: *mut leanh::LeanObject,
    mut v_a_3616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3617_ = l_Std_DHashMap_Raw_Const_get_x21(
        v_00_u03b1_3610_,
        v_00_u03b2_3611_,
        v_inst_3612_,
        v_inst_3613_,
        v_inst_3614_,
        v_m_3615_,
        v_a_3616_,
    );
    leanh::lean_dec_ref(v_m_3615_);
    leanh::lean_dec(v_inst_3614_);
    return v_res_3617_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(
    mut v_inst_3618_: *mut leanh::LeanObject,
    mut v_inst_3619_: *mut leanh::LeanObject,
    mut v_m_3620_: *mut leanh::LeanObject,
    mut v_a_3621_: *mut leanh::LeanObject,
    mut v_b_3622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: u8 = 0;
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: u8 = 0;
    let mut v_val_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut v_unused_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3623_ = leanh::lean_ctor_get(v_m_3620_, 0);
                v_buckets_3624_ = leanh::lean_ctor_get(v_m_3620_, 1);
                v___x_3625_ = leanh::lean_unsigned_to_nat(0);
                v___x_3626_ = lean_array_get_size(v_buckets_3624_);
                v___x_3627_ = lean_nat_dec_lt(v___x_3625_, v___x_3626_);
                if v___x_3627_ == 0 {
                    leanh::lean_dec(v_b_3622_);
                    leanh::lean_dec(v_a_3621_);
                    leanh::lean_dec_ref(v_inst_3619_);
                    leanh::lean_dec_ref(v_inst_3618_);
                    v___x_3628_ = leanh::lean_box(0);
                    v___x_3629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3629_, 0, v___x_3628_);
                    leanh::lean_ctor_set(v___x_3629_, 1, v_m_3620_);
                    return v___x_3629_;
                } else {
                    leanh::lean_inc_ref(v_inst_3619_);
                    leanh::lean_inc_n(v_a_3621_, 2);
                    v___x_3630_ = leanh::lean_apply_1(v_inst_3619_, v_a_3621_);
                    v___x_3631_ = 32u64;
                    v___x_3632_ = leanh::lean_unbox_uint64(v___x_3630_);
                    v___x_3633_ = lean_uint64_shift_right(v___x_3632_, v___x_3631_);
                    v___x_3634_ = leanh::lean_unbox_uint64(v___x_3630_);
                    leanh::lean_dec_ref(v___x_3630_);
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
                    leanh::lean_inc(v_bkt_3644_);
                    v___x_3645_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_3618_,
                        v_a_3621_,
                        v_bkt_3644_,
                    );
                    if leanh::lean_obj_tag(v___x_3645_) == 0 {
                        leanh::lean_inc_ref(v_buckets_3624_);
                        leanh::lean_inc(v_size_3623_);
                        v_isSharedCheck_3668_ = (!leanh::lean_is_exclusive(v_m_3620_)) as u8;
                        if v_isSharedCheck_3668_ == 0 {
                            v_unused_3669_ = leanh::lean_ctor_get(v_m_3620_, 1);
                            leanh::lean_dec(v_unused_3669_);
                            v_unused_3670_ = leanh::lean_ctor_get(v_m_3620_, 0);
                            leanh::lean_dec(v_unused_3670_);
                            v___x_3647_ = v_m_3620_;
                            v_isShared_3648_ = v_isSharedCheck_3668_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_3620_);
                            v___x_3647_ = leanh::lean_box(0);
                            v_isShared_3648_ = v_isSharedCheck_3668_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_3622_);
                        leanh::lean_dec(v_a_3621_);
                        leanh::lean_dec_ref(v_inst_3619_);
                        v___x_3671_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3671_, 0, v___x_3645_);
                        leanh::lean_ctor_set(v___x_3671_, 1, v_m_3620_);
                        return v___x_3671_;
                    }
                }
            }
            1 => {
                v___x_3649_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3650_ = lean_nat_add(v_size_3623_, v___x_3649_);
                leanh::lean_dec(v_size_3623_);
                leanh::lean_inc(v_bkt_3644_);
                v___x_3651_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3651_, 0, v_a_3621_);
                leanh::lean_ctor_set(v___x_3651_, 1, v_b_3622_);
                leanh::lean_ctor_set(v___x_3651_, 2, v_bkt_3644_);
                v_buckets_x27_3652_ = lean_array_uset(v_buckets_3624_, v___x_3643_, v___x_3651_);
                v___x_3653_ = leanh::lean_unsigned_to_nat(4);
                v___x_3654_ = lean_nat_mul(v_size_x27_3650_, v___x_3653_);
                v___x_3655_ = leanh::lean_unsigned_to_nat(3);
                v___x_3656_ = lean_nat_div(v___x_3654_, v___x_3655_);
                leanh::lean_dec(v___x_3654_);
                v___x_3657_ = lean_array_get_size(v_buckets_x27_3652_);
                v___x_3658_ = lean_nat_dec_le(v___x_3656_, v___x_3657_);
                leanh::lean_dec(v___x_3656_);
                if v___x_3658_ == 0 {
                    v_val_3659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3619_,
                        v_buckets_x27_3652_,
                    );
                    if v_isShared_3648_ == 0 {
                        leanh::lean_ctor_set(v___x_3647_, 1, v_val_3659_);
                        leanh::lean_ctor_set(v___x_3647_, 0, v_size_x27_3650_);
                        v___x_3661_ = v___x_3647_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_size_x27_3650_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_val_3659_);
                        v___x_3661_ = v_reuseFailAlloc_3663_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3619_);
                    if v_isShared_3648_ == 0 {
                        leanh::lean_ctor_set(v___x_3647_, 1, v_buckets_x27_3652_);
                        leanh::lean_ctor_set(v___x_3647_, 0, v_size_x27_3650_);
                        v___x_3665_ = v___x_3647_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_size_x27_3650_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_buckets_x27_3652_);
                        v___x_3665_ = v_reuseFailAlloc_3667_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3662_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3662_, 0, v___x_3645_);
                leanh::lean_ctor_set(v___x_3662_, 1, v___x_3661_);
                return v___x_3662_;
            }
            3 => {
                v___x_3666_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3666_, 0, v___x_3645_);
                leanh::lean_ctor_set(v___x_3666_, 1, v___x_3665_);
                return v___x_3666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_3672_: *mut leanh::LeanObject,
    mut v_00_u03b2_3673_: *mut leanh::LeanObject,
    mut v_inst_3674_: *mut leanh::LeanObject,
    mut v_inst_3675_: *mut leanh::LeanObject,
    mut v_m_3676_: *mut leanh::LeanObject,
    mut v_a_3677_: *mut leanh::LeanObject,
    mut v_b_3678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: u8 = 0;
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v_val_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut v_unused_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3679_ = leanh::lean_ctor_get(v_m_3676_, 0);
                v_buckets_3680_ = leanh::lean_ctor_get(v_m_3676_, 1);
                v___x_3681_ = leanh::lean_unsigned_to_nat(0);
                v___x_3682_ = lean_array_get_size(v_buckets_3680_);
                v___x_3683_ = lean_nat_dec_lt(v___x_3681_, v___x_3682_);
                if v___x_3683_ == 0 {
                    leanh::lean_dec(v_b_3678_);
                    leanh::lean_dec(v_a_3677_);
                    leanh::lean_dec_ref(v_inst_3675_);
                    leanh::lean_dec_ref(v_inst_3674_);
                    v___x_3684_ = leanh::lean_box(0);
                    v___x_3685_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3685_, 0, v___x_3684_);
                    leanh::lean_ctor_set(v___x_3685_, 1, v_m_3676_);
                    return v___x_3685_;
                } else {
                    leanh::lean_inc_ref(v_inst_3675_);
                    leanh::lean_inc_n(v_a_3677_, 2);
                    v___x_3686_ = leanh::lean_apply_1(v_inst_3675_, v_a_3677_);
                    v___x_3687_ = 32u64;
                    v___x_3688_ = leanh::lean_unbox_uint64(v___x_3686_);
                    v___x_3689_ = lean_uint64_shift_right(v___x_3688_, v___x_3687_);
                    v___x_3690_ = leanh::lean_unbox_uint64(v___x_3686_);
                    leanh::lean_dec_ref(v___x_3686_);
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
                    leanh::lean_inc(v_bkt_3700_);
                    v___x_3701_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                        v_inst_3674_,
                        v_a_3677_,
                        v_bkt_3700_,
                    );
                    if leanh::lean_obj_tag(v___x_3701_) == 0 {
                        leanh::lean_inc_ref(v_buckets_3680_);
                        leanh::lean_inc(v_size_3679_);
                        v_isSharedCheck_3724_ = (!leanh::lean_is_exclusive(v_m_3676_)) as u8;
                        if v_isSharedCheck_3724_ == 0 {
                            v_unused_3725_ = leanh::lean_ctor_get(v_m_3676_, 1);
                            leanh::lean_dec(v_unused_3725_);
                            v_unused_3726_ = leanh::lean_ctor_get(v_m_3676_, 0);
                            leanh::lean_dec(v_unused_3726_);
                            v___x_3703_ = v_m_3676_;
                            v_isShared_3704_ = v_isSharedCheck_3724_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_3676_);
                            v___x_3703_ = leanh::lean_box(0);
                            v_isShared_3704_ = v_isSharedCheck_3724_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_b_3678_);
                        leanh::lean_dec(v_a_3677_);
                        leanh::lean_dec_ref(v_inst_3675_);
                        v___x_3727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3727_, 0, v___x_3701_);
                        leanh::lean_ctor_set(v___x_3727_, 1, v_m_3676_);
                        return v___x_3727_;
                    }
                }
            }
            1 => {
                v___x_3705_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3706_ = lean_nat_add(v_size_3679_, v___x_3705_);
                leanh::lean_dec(v_size_3679_);
                leanh::lean_inc(v_bkt_3700_);
                v___x_3707_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3707_, 0, v_a_3677_);
                leanh::lean_ctor_set(v___x_3707_, 1, v_b_3678_);
                leanh::lean_ctor_set(v___x_3707_, 2, v_bkt_3700_);
                v_buckets_x27_3708_ = lean_array_uset(v_buckets_3680_, v___x_3699_, v___x_3707_);
                v___x_3709_ = leanh::lean_unsigned_to_nat(4);
                v___x_3710_ = lean_nat_mul(v_size_x27_3706_, v___x_3709_);
                v___x_3711_ = leanh::lean_unsigned_to_nat(3);
                v___x_3712_ = lean_nat_div(v___x_3710_, v___x_3711_);
                leanh::lean_dec(v___x_3710_);
                v___x_3713_ = lean_array_get_size(v_buckets_x27_3708_);
                v___x_3714_ = lean_nat_dec_le(v___x_3712_, v___x_3713_);
                leanh::lean_dec(v___x_3712_);
                if v___x_3714_ == 0 {
                    v_val_3715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3675_,
                        v_buckets_x27_3708_,
                    );
                    if v_isShared_3704_ == 0 {
                        leanh::lean_ctor_set(v___x_3703_, 1, v_val_3715_);
                        leanh::lean_ctor_set(v___x_3703_, 0, v_size_x27_3706_);
                        v___x_3717_ = v___x_3703_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3719_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_size_x27_3706_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_val_3715_);
                        v___x_3717_ = v_reuseFailAlloc_3719_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3675_);
                    if v_isShared_3704_ == 0 {
                        leanh::lean_ctor_set(v___x_3703_, 1, v_buckets_x27_3708_);
                        leanh::lean_ctor_set(v___x_3703_, 0, v_size_x27_3706_);
                        v___x_3721_ = v___x_3703_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_size_x27_3706_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_buckets_x27_3708_);
                        v___x_3721_ = v_reuseFailAlloc_3723_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3718_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3718_, 0, v___x_3701_);
                leanh::lean_ctor_set(v___x_3718_, 1, v___x_3717_);
                return v___x_3718_;
            }
            3 => {
                v___x_3722_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3722_, 0, v___x_3701_);
                leanh::lean_ctor_set(v___x_3722_, 1, v___x_3721_);
                return v___x_3722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x3f___redArg(
    mut v_inst_3728_: *mut leanh::LeanObject,
    mut v_inst_3729_: *mut leanh::LeanObject,
    mut v_m_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: u8 = 0;
    v_buckets_3732_ = leanh::lean_ctor_get(v_m_3730_, 1);
    v___x_3733_ = leanh::lean_unsigned_to_nat(0);
    v___x_3734_ = lean_array_get_size(v_buckets_3732_);
    v___x_3735_ = lean_nat_dec_lt(v___x_3733_, v___x_3734_);
    if v___x_3735_ == 0 {
        let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3731_);
        leanh::lean_dec_ref(v_inst_3729_);
        leanh::lean_dec_ref(v_inst_3728_);
        v___x_3736_ = leanh::lean_box(0);
        return v___x_3736_;
    } else {
        let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3738_: *mut leanh::LeanObject,
    mut v_inst_3739_: *mut leanh::LeanObject,
    mut v_m_3740_: *mut leanh::LeanObject,
    mut v_a_3741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3742_ =
        l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_3738_, v_inst_3739_, v_m_3740_, v_a_3741_);
    leanh::lean_dec_ref(v_m_3740_);
    return v_res_3742_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x3f(
    mut v_00_u03b1_3743_: *mut leanh::LeanObject,
    mut v_00_u03b2_3744_: *mut leanh::LeanObject,
    mut v_inst_3745_: *mut leanh::LeanObject,
    mut v_inst_3746_: *mut leanh::LeanObject,
    mut v_m_3747_: *mut leanh::LeanObject,
    mut v_a_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    v_buckets_3749_ = leanh::lean_ctor_get(v_m_3747_, 1);
    v___x_3750_ = leanh::lean_unsigned_to_nat(0);
    v___x_3751_ = lean_array_get_size(v_buckets_3749_);
    v___x_3752_ = lean_nat_dec_lt(v___x_3750_, v___x_3751_);
    if v___x_3752_ == 0 {
        let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3748_);
        leanh::lean_dec_ref(v_inst_3746_);
        leanh::lean_dec_ref(v_inst_3745_);
        v___x_3753_ = leanh::lean_box(0);
        return v___x_3753_;
    } else {
        let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3755_: *mut leanh::LeanObject,
    mut v_00_u03b2_3756_: *mut leanh::LeanObject,
    mut v_inst_3757_: *mut leanh::LeanObject,
    mut v_inst_3758_: *mut leanh::LeanObject,
    mut v_m_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Std_DHashMap_Raw_getKey_x3f(
        v_00_u03b1_3755_,
        v_00_u03b2_3756_,
        v_inst_3757_,
        v_inst_3758_,
        v_m_3759_,
        v_a_3760_,
    );
    leanh::lean_dec_ref(v_m_3759_);
    return v_res_3761_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey___redArg(
    mut v_inst_3762_: *mut leanh::LeanObject,
    mut v_inst_3763_: *mut leanh::LeanObject,
    mut v_m_3764_: *mut leanh::LeanObject,
    mut v_a_3765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3762_,
        v_inst_3763_,
        v_m_3764_,
        v_a_3765_,
    );
    return v___x_3766_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey___redArg___boxed(
    mut v_inst_3767_: *mut leanh::LeanObject,
    mut v_inst_3768_: *mut leanh::LeanObject,
    mut v_m_3769_: *mut leanh::LeanObject,
    mut v_a_3770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ =
        l_Std_DHashMap_Raw_getKey___redArg(v_inst_3767_, v_inst_3768_, v_m_3769_, v_a_3770_);
    leanh::lean_dec_ref(v_m_3769_);
    return v_res_3771_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey(
    mut v_00_u03b1_3772_: *mut leanh::LeanObject,
    mut v_00_u03b2_3773_: *mut leanh::LeanObject,
    mut v_inst_3774_: *mut leanh::LeanObject,
    mut v_inst_3775_: *mut leanh::LeanObject,
    mut v_m_3776_: *mut leanh::LeanObject,
    mut v_a_3777_: *mut leanh::LeanObject,
    mut v_h_3778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_3774_,
        v_inst_3775_,
        v_m_3776_,
        v_a_3777_,
    );
    return v___x_3779_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey___boxed(
    mut v_00_u03b1_3780_: *mut leanh::LeanObject,
    mut v_00_u03b2_3781_: *mut leanh::LeanObject,
    mut v_inst_3782_: *mut leanh::LeanObject,
    mut v_inst_3783_: *mut leanh::LeanObject,
    mut v_m_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_h_3786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Std_DHashMap_Raw_getKey(
        v_00_u03b1_3780_,
        v_00_u03b2_3781_,
        v_inst_3782_,
        v_inst_3783_,
        v_m_3784_,
        v_a_3785_,
        v_h_3786_,
    );
    leanh::lean_dec_ref(v_m_3784_);
    return v_res_3787_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKeyD___redArg(
    mut v_inst_3788_: *mut leanh::LeanObject,
    mut v_inst_3789_: *mut leanh::LeanObject,
    mut v_m_3790_: *mut leanh::LeanObject,
    mut v_a_3791_: *mut leanh::LeanObject,
    mut v_fallback_3792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    v_buckets_3793_ = leanh::lean_ctor_get(v_m_3790_, 1);
    v___x_3794_ = leanh::lean_unsigned_to_nat(0);
    v___x_3795_ = lean_array_get_size(v_buckets_3793_);
    v___x_3796_ = lean_nat_dec_lt(v___x_3794_, v___x_3795_);
    if v___x_3796_ == 0 {
        leanh::lean_dec(v_a_3791_);
        leanh::lean_dec_ref(v_inst_3789_);
        leanh::lean_dec_ref(v_inst_3788_);
        leanh::lean_inc(v_fallback_3792_);
        return v_fallback_3792_;
    } else {
        let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3798_: *mut leanh::LeanObject,
    mut v_inst_3799_: *mut leanh::LeanObject,
    mut v_m_3800_: *mut leanh::LeanObject,
    mut v_a_3801_: *mut leanh::LeanObject,
    mut v_fallback_3802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Std_DHashMap_Raw_getKeyD___redArg(
        v_inst_3798_,
        v_inst_3799_,
        v_m_3800_,
        v_a_3801_,
        v_fallback_3802_,
    );
    leanh::lean_dec(v_fallback_3802_);
    leanh::lean_dec_ref(v_m_3800_);
    return v_res_3803_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKeyD(
    mut v_00_u03b1_3804_: *mut leanh::LeanObject,
    mut v_00_u03b2_3805_: *mut leanh::LeanObject,
    mut v_inst_3806_: *mut leanh::LeanObject,
    mut v_inst_3807_: *mut leanh::LeanObject,
    mut v_m_3808_: *mut leanh::LeanObject,
    mut v_a_3809_: *mut leanh::LeanObject,
    mut v_fallback_3810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    v_buckets_3811_ = leanh::lean_ctor_get(v_m_3808_, 1);
    v___x_3812_ = leanh::lean_unsigned_to_nat(0);
    v___x_3813_ = lean_array_get_size(v_buckets_3811_);
    v___x_3814_ = lean_nat_dec_lt(v___x_3812_, v___x_3813_);
    if v___x_3814_ == 0 {
        leanh::lean_dec(v_a_3809_);
        leanh::lean_dec_ref(v_inst_3807_);
        leanh::lean_dec_ref(v_inst_3806_);
        leanh::lean_inc(v_fallback_3810_);
        return v_fallback_3810_;
    } else {
        let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3816_: *mut leanh::LeanObject,
    mut v_00_u03b2_3817_: *mut leanh::LeanObject,
    mut v_inst_3818_: *mut leanh::LeanObject,
    mut v_inst_3819_: *mut leanh::LeanObject,
    mut v_m_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_fallback_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Std_DHashMap_Raw_getKeyD(
        v_00_u03b1_3816_,
        v_00_u03b2_3817_,
        v_inst_3818_,
        v_inst_3819_,
        v_m_3820_,
        v_a_3821_,
        v_fallback_3822_,
    );
    leanh::lean_dec(v_fallback_3822_);
    leanh::lean_dec_ref(v_m_3820_);
    return v_res_3823_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x21___redArg(
    mut v_inst_3824_: *mut leanh::LeanObject,
    mut v_inst_3825_: *mut leanh::LeanObject,
    mut v_inst_3826_: *mut leanh::LeanObject,
    mut v_m_3827_: *mut leanh::LeanObject,
    mut v_a_3828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: u8 = 0;
    v_buckets_3829_ = leanh::lean_ctor_get(v_m_3827_, 1);
    v___x_3830_ = leanh::lean_unsigned_to_nat(0);
    v___x_3831_ = lean_array_get_size(v_buckets_3829_);
    v___x_3832_ = lean_nat_dec_lt(v___x_3830_, v___x_3831_);
    if v___x_3832_ == 0 {
        leanh::lean_dec(v_a_3828_);
        leanh::lean_dec_ref(v_inst_3825_);
        leanh::lean_dec_ref(v_inst_3824_);
        leanh::lean_inc(v_inst_3826_);
        return v_inst_3826_;
    } else {
        let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3834_: *mut leanh::LeanObject,
    mut v_inst_3835_: *mut leanh::LeanObject,
    mut v_inst_3836_: *mut leanh::LeanObject,
    mut v_m_3837_: *mut leanh::LeanObject,
    mut v_a_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Std_DHashMap_Raw_getKey_x21___redArg(
        v_inst_3834_,
        v_inst_3835_,
        v_inst_3836_,
        v_m_3837_,
        v_a_3838_,
    );
    leanh::lean_dec_ref(v_m_3837_);
    leanh::lean_dec(v_inst_3836_);
    return v_res_3839_;
}
pub unsafe fn l_Std_DHashMap_Raw_getKey_x21(
    mut v_00_u03b1_3840_: *mut leanh::LeanObject,
    mut v_00_u03b2_3841_: *mut leanh::LeanObject,
    mut v_inst_3842_: *mut leanh::LeanObject,
    mut v_inst_3843_: *mut leanh::LeanObject,
    mut v_inst_3844_: *mut leanh::LeanObject,
    mut v_m_3845_: *mut leanh::LeanObject,
    mut v_a_3846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: u8 = 0;
    v_buckets_3847_ = leanh::lean_ctor_get(v_m_3845_, 1);
    v___x_3848_ = leanh::lean_unsigned_to_nat(0);
    v___x_3849_ = lean_array_get_size(v_buckets_3847_);
    v___x_3850_ = lean_nat_dec_lt(v___x_3848_, v___x_3849_);
    if v___x_3850_ == 0 {
        leanh::lean_dec(v_a_3846_);
        leanh::lean_dec_ref(v_inst_3843_);
        leanh::lean_dec_ref(v_inst_3842_);
        leanh::lean_inc(v_inst_3844_);
        return v_inst_3844_;
    } else {
        let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3852_: *mut leanh::LeanObject,
    mut v_00_u03b2_3853_: *mut leanh::LeanObject,
    mut v_inst_3854_: *mut leanh::LeanObject,
    mut v_inst_3855_: *mut leanh::LeanObject,
    mut v_inst_3856_: *mut leanh::LeanObject,
    mut v_m_3857_: *mut leanh::LeanObject,
    mut v_a_3858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Std_DHashMap_Raw_getKey_x21(
        v_00_u03b1_3852_,
        v_00_u03b2_3853_,
        v_inst_3854_,
        v_inst_3855_,
        v_inst_3856_,
        v_m_3857_,
        v_a_3858_,
    );
    leanh::lean_dec_ref(v_m_3857_);
    leanh::lean_dec(v_inst_3856_);
    return v_res_3859_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x3f___redArg(
    mut v_inst_3860_: *mut leanh::LeanObject,
    mut v_inst_3861_: *mut leanh::LeanObject,
    mut v_m_3862_: *mut leanh::LeanObject,
    mut v_a_3863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    v_buckets_3864_ = leanh::lean_ctor_get(v_m_3862_, 1);
    v___x_3865_ = leanh::lean_unsigned_to_nat(0);
    v___x_3866_ = lean_array_get_size(v_buckets_3864_);
    v___x_3867_ = lean_nat_dec_lt(v___x_3865_, v___x_3866_);
    if v___x_3867_ == 0 {
        let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3863_);
        leanh::lean_dec_ref(v_inst_3861_);
        leanh::lean_dec_ref(v_inst_3860_);
        v___x_3868_ = leanh::lean_box(0);
        return v___x_3868_;
    } else {
        let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3870_: *mut leanh::LeanObject,
    mut v_inst_3871_: *mut leanh::LeanObject,
    mut v_m_3872_: *mut leanh::LeanObject,
    mut v_a_3873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3874_ =
        l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_3870_, v_inst_3871_, v_m_3872_, v_a_3873_);
    leanh::lean_dec_ref(v_m_3872_);
    return v_res_3874_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x3f(
    mut v_00_u03b1_3875_: *mut leanh::LeanObject,
    mut v_00_u03b2_3876_: *mut leanh::LeanObject,
    mut v_inst_3877_: *mut leanh::LeanObject,
    mut v_inst_3878_: *mut leanh::LeanObject,
    mut v_m_3879_: *mut leanh::LeanObject,
    mut v_a_3880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: u8 = 0;
    v_buckets_3881_ = leanh::lean_ctor_get(v_m_3879_, 1);
    v___x_3882_ = leanh::lean_unsigned_to_nat(0);
    v___x_3883_ = lean_array_get_size(v_buckets_3881_);
    v___x_3884_ = lean_nat_dec_lt(v___x_3882_, v___x_3883_);
    if v___x_3884_ == 0 {
        let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_3880_);
        leanh::lean_dec_ref(v_inst_3878_);
        leanh::lean_dec_ref(v_inst_3877_);
        v___x_3885_ = leanh::lean_box(0);
        return v___x_3885_;
    } else {
        let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3887_: *mut leanh::LeanObject,
    mut v_00_u03b2_3888_: *mut leanh::LeanObject,
    mut v_inst_3889_: *mut leanh::LeanObject,
    mut v_inst_3890_: *mut leanh::LeanObject,
    mut v_m_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3893_ = l_Std_DHashMap_Raw_getEntry_x3f(
        v_00_u03b1_3887_,
        v_00_u03b2_3888_,
        v_inst_3889_,
        v_inst_3890_,
        v_m_3891_,
        v_a_3892_,
    );
    leanh::lean_dec_ref(v_m_3891_);
    return v_res_3893_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry___redArg(
    mut v_inst_3894_: *mut leanh::LeanObject,
    mut v_inst_3895_: *mut leanh::LeanObject,
    mut v_m_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3898_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_inst_3894_,
        v_inst_3895_,
        v_m_3896_,
        v_a_3897_,
    );
    return v___x_3898_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry___redArg___boxed(
    mut v_inst_3899_: *mut leanh::LeanObject,
    mut v_inst_3900_: *mut leanh::LeanObject,
    mut v_m_3901_: *mut leanh::LeanObject,
    mut v_a_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ =
        l_Std_DHashMap_Raw_getEntry___redArg(v_inst_3899_, v_inst_3900_, v_m_3901_, v_a_3902_);
    leanh::lean_dec_ref(v_m_3901_);
    return v_res_3903_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry(
    mut v_00_u03b1_3904_: *mut leanh::LeanObject,
    mut v_00_u03b2_3905_: *mut leanh::LeanObject,
    mut v_inst_3906_: *mut leanh::LeanObject,
    mut v_inst_3907_: *mut leanh::LeanObject,
    mut v_m_3908_: *mut leanh::LeanObject,
    mut v_a_3909_: *mut leanh::LeanObject,
    mut v_h_3910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3911_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_inst_3906_,
        v_inst_3907_,
        v_m_3908_,
        v_a_3909_,
    );
    return v___x_3911_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry___boxed(
    mut v_00_u03b1_3912_: *mut leanh::LeanObject,
    mut v_00_u03b2_3913_: *mut leanh::LeanObject,
    mut v_inst_3914_: *mut leanh::LeanObject,
    mut v_inst_3915_: *mut leanh::LeanObject,
    mut v_m_3916_: *mut leanh::LeanObject,
    mut v_a_3917_: *mut leanh::LeanObject,
    mut v_h_3918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Std_DHashMap_Raw_getEntry(
        v_00_u03b1_3912_,
        v_00_u03b2_3913_,
        v_inst_3914_,
        v_inst_3915_,
        v_m_3916_,
        v_a_3917_,
        v_h_3918_,
    );
    leanh::lean_dec_ref(v_m_3916_);
    return v_res_3919_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntryD___redArg(
    mut v_inst_3920_: *mut leanh::LeanObject,
    mut v_inst_3921_: *mut leanh::LeanObject,
    mut v_m_3922_: *mut leanh::LeanObject,
    mut v_a_3923_: *mut leanh::LeanObject,
    mut v_fallback_3924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    v_buckets_3925_ = leanh::lean_ctor_get(v_m_3922_, 1);
    v___x_3926_ = leanh::lean_unsigned_to_nat(0);
    v___x_3927_ = lean_array_get_size(v_buckets_3925_);
    v___x_3928_ = lean_nat_dec_lt(v___x_3926_, v___x_3927_);
    if v___x_3928_ == 0 {
        leanh::lean_dec(v_a_3923_);
        leanh::lean_dec_ref(v_inst_3921_);
        leanh::lean_dec_ref(v_inst_3920_);
        leanh::lean_inc_ref(v_fallback_3924_);
        return v_fallback_3924_;
    } else {
        let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3930_: *mut leanh::LeanObject,
    mut v_inst_3931_: *mut leanh::LeanObject,
    mut v_m_3932_: *mut leanh::LeanObject,
    mut v_a_3933_: *mut leanh::LeanObject,
    mut v_fallback_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_Std_DHashMap_Raw_getEntryD___redArg(
        v_inst_3930_,
        v_inst_3931_,
        v_m_3932_,
        v_a_3933_,
        v_fallback_3934_,
    );
    leanh::lean_dec_ref(v_fallback_3934_);
    leanh::lean_dec_ref(v_m_3932_);
    return v_res_3935_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntryD(
    mut v_00_u03b1_3936_: *mut leanh::LeanObject,
    mut v_00_u03b2_3937_: *mut leanh::LeanObject,
    mut v_inst_3938_: *mut leanh::LeanObject,
    mut v_inst_3939_: *mut leanh::LeanObject,
    mut v_m_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
    mut v_fallback_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: u8 = 0;
    v_buckets_3943_ = leanh::lean_ctor_get(v_m_3940_, 1);
    v___x_3944_ = leanh::lean_unsigned_to_nat(0);
    v___x_3945_ = lean_array_get_size(v_buckets_3943_);
    v___x_3946_ = lean_nat_dec_lt(v___x_3944_, v___x_3945_);
    if v___x_3946_ == 0 {
        leanh::lean_dec(v_a_3941_);
        leanh::lean_dec_ref(v_inst_3939_);
        leanh::lean_dec_ref(v_inst_3938_);
        leanh::lean_inc_ref(v_fallback_3942_);
        return v_fallback_3942_;
    } else {
        let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3948_: *mut leanh::LeanObject,
    mut v_00_u03b2_3949_: *mut leanh::LeanObject,
    mut v_inst_3950_: *mut leanh::LeanObject,
    mut v_inst_3951_: *mut leanh::LeanObject,
    mut v_m_3952_: *mut leanh::LeanObject,
    mut v_a_3953_: *mut leanh::LeanObject,
    mut v_fallback_3954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3955_ = l_Std_DHashMap_Raw_getEntryD(
        v_00_u03b1_3948_,
        v_00_u03b2_3949_,
        v_inst_3950_,
        v_inst_3951_,
        v_m_3952_,
        v_a_3953_,
        v_fallback_3954_,
    );
    leanh::lean_dec_ref(v_fallback_3954_);
    leanh::lean_dec_ref(v_m_3952_);
    return v_res_3955_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x21___redArg(
    mut v_inst_3956_: *mut leanh::LeanObject,
    mut v_inst_3957_: *mut leanh::LeanObject,
    mut v_inst_3958_: *mut leanh::LeanObject,
    mut v_m_3959_: *mut leanh::LeanObject,
    mut v_a_3960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    v_buckets_3961_ = leanh::lean_ctor_get(v_m_3959_, 1);
    v___x_3962_ = leanh::lean_unsigned_to_nat(0);
    v___x_3963_ = lean_array_get_size(v_buckets_3961_);
    v___x_3964_ = lean_nat_dec_lt(v___x_3962_, v___x_3963_);
    if v___x_3964_ == 0 {
        leanh::lean_dec(v_a_3960_);
        leanh::lean_dec_ref(v_inst_3957_);
        leanh::lean_dec_ref(v_inst_3956_);
        leanh::lean_inc_ref(v_inst_3958_);
        return v_inst_3958_;
    } else {
        let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_3966_: *mut leanh::LeanObject,
    mut v_inst_3967_: *mut leanh::LeanObject,
    mut v_inst_3968_: *mut leanh::LeanObject,
    mut v_m_3969_: *mut leanh::LeanObject,
    mut v_a_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(
        v_inst_3966_,
        v_inst_3967_,
        v_inst_3968_,
        v_m_3969_,
        v_a_3970_,
    );
    leanh::lean_dec_ref(v_m_3969_);
    leanh::lean_dec_ref(v_inst_3968_);
    return v_res_3971_;
}
pub unsafe fn l_Std_DHashMap_Raw_getEntry_x21(
    mut v_00_u03b1_3972_: *mut leanh::LeanObject,
    mut v_00_u03b2_3973_: *mut leanh::LeanObject,
    mut v_inst_3974_: *mut leanh::LeanObject,
    mut v_inst_3975_: *mut leanh::LeanObject,
    mut v_inst_3976_: *mut leanh::LeanObject,
    mut v_m_3977_: *mut leanh::LeanObject,
    mut v_a_3978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    v_buckets_3979_ = leanh::lean_ctor_get(v_m_3977_, 1);
    v___x_3980_ = leanh::lean_unsigned_to_nat(0);
    v___x_3981_ = lean_array_get_size(v_buckets_3979_);
    v___x_3982_ = lean_nat_dec_lt(v___x_3980_, v___x_3981_);
    if v___x_3982_ == 0 {
        leanh::lean_dec(v_a_3978_);
        leanh::lean_dec_ref(v_inst_3975_);
        leanh::lean_dec_ref(v_inst_3974_);
        leanh::lean_inc_ref(v_inst_3976_);
        return v_inst_3976_;
    } else {
        let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3984_: *mut leanh::LeanObject,
    mut v_00_u03b2_3985_: *mut leanh::LeanObject,
    mut v_inst_3986_: *mut leanh::LeanObject,
    mut v_inst_3987_: *mut leanh::LeanObject,
    mut v_inst_3988_: *mut leanh::LeanObject,
    mut v_m_3989_: *mut leanh::LeanObject,
    mut v_a_3990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3991_ = l_Std_DHashMap_Raw_getEntry_x21(
        v_00_u03b1_3984_,
        v_00_u03b2_3985_,
        v_inst_3986_,
        v_inst_3987_,
        v_inst_3988_,
        v_m_3989_,
        v_a_3990_,
    );
    leanh::lean_dec_ref(v_m_3989_);
    leanh::lean_dec_ref(v_inst_3988_);
    return v_res_3991_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty___redArg(
    mut v_m_3992_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    v_size_3993_ = leanh::lean_ctor_get(v_m_3992_, 0);
    v___x_3994_ = leanh::lean_unsigned_to_nat(0);
    v___x_3995_ = lean_nat_dec_eq(v_size_3993_, v___x_3994_);
    return v___x_3995_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty___redArg___boxed(
    mut v_m_3996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3997_: u8 = 0;
    let mut v_r_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3997_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_3996_);
    leanh::lean_dec_ref(v_m_3996_);
    v_r_3998_ = leanh::lean_box((v_res_3997_) as usize);
    return v_r_3998_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty(
    mut v_00_u03b1_3999_: *mut leanh::LeanObject,
    mut v_00_u03b2_4000_: *mut leanh::LeanObject,
    mut v_m_4001_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: u8 = 0;
    v_size_4002_ = leanh::lean_ctor_get(v_m_4001_, 0);
    v___x_4003_ = leanh::lean_unsigned_to_nat(0);
    v___x_4004_ = lean_nat_dec_eq(v_size_4002_, v___x_4003_);
    return v___x_4004_;
}
pub unsafe fn l_Std_DHashMap_Raw_isEmpty___boxed(
    mut v_00_u03b1_4005_: *mut leanh::LeanObject,
    mut v_00_u03b2_4006_: *mut leanh::LeanObject,
    mut v_m_4007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4008_: u8 = 0;
    let mut v_r_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4008_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_4005_, v_00_u03b2_4006_, v_m_4007_);
    leanh::lean_dec_ref(v_m_4007_);
    v_r_4009_ = leanh::lean_box((v_res_4008_) as usize);
    return v_r_4009_;
}
pub unsafe fn l_Std_DHashMap_Raw_modify___redArg(
    mut v_inst_4010_: *mut leanh::LeanObject,
    mut v_inst_4011_: *mut leanh::LeanObject,
    mut v_m_4012_: *mut leanh::LeanObject,
    mut v_a_4013_: *mut leanh::LeanObject,
    mut v_f_4014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: u8 = 0;
    v_buckets_4015_ = leanh::lean_ctor_get(v_m_4012_, 1);
    v___x_4016_ = leanh::lean_unsigned_to_nat(0);
    v___x_4017_ = lean_array_get_size(v_buckets_4015_);
    v___x_4018_ = lean_nat_dec_lt(v___x_4016_, v___x_4017_);
    if v___x_4018_ == 0 {
        let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_4014_);
        leanh::lean_dec(v_a_4013_);
        leanh::lean_dec_ref(v_m_4012_);
        leanh::lean_dec_ref(v_inst_4011_);
        leanh::lean_dec_ref(v_inst_4010_);
        v___x_4019_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4019_;
    } else {
        let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4021_: *mut leanh::LeanObject,
    mut v_00_u03b2_4022_: *mut leanh::LeanObject,
    mut v_inst_4023_: *mut leanh::LeanObject,
    mut v_inst_4024_: *mut leanh::LeanObject,
    mut v_inst_4025_: *mut leanh::LeanObject,
    mut v_m_4026_: *mut leanh::LeanObject,
    mut v_a_4027_: *mut leanh::LeanObject,
    mut v_f_4028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: u8 = 0;
    v_buckets_4029_ = leanh::lean_ctor_get(v_m_4026_, 1);
    v___x_4030_ = leanh::lean_unsigned_to_nat(0);
    v___x_4031_ = lean_array_get_size(v_buckets_4029_);
    v___x_4032_ = lean_nat_dec_lt(v___x_4030_, v___x_4031_);
    if v___x_4032_ == 0 {
        let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_4028_);
        leanh::lean_dec(v_a_4027_);
        leanh::lean_dec_ref(v_m_4026_);
        leanh::lean_dec_ref(v_inst_4025_);
        leanh::lean_dec_ref(v_inst_4023_);
        v___x_4033_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4033_;
    } else {
        let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4035_: *mut leanh::LeanObject,
    mut v_inst_4036_: *mut leanh::LeanObject,
    mut v_m_4037_: *mut leanh::LeanObject,
    mut v_a_4038_: *mut leanh::LeanObject,
    mut v_f_4039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u8 = 0;
    v_buckets_4040_ = leanh::lean_ctor_get(v_m_4037_, 1);
    v___x_4041_ = leanh::lean_unsigned_to_nat(0);
    v___x_4042_ = lean_array_get_size(v_buckets_4040_);
    v___x_4043_ = lean_nat_dec_lt(v___x_4041_, v___x_4042_);
    if v___x_4043_ == 0 {
        let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_4039_);
        leanh::lean_dec(v_a_4038_);
        leanh::lean_dec_ref(v_m_4037_);
        leanh::lean_dec_ref(v_inst_4036_);
        leanh::lean_dec_ref(v_inst_4035_);
        v___x_4044_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4044_;
    } else {
        let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4046_: *mut leanh::LeanObject,
    mut v_inst_4047_: *mut leanh::LeanObject,
    mut v_inst_4048_: *mut leanh::LeanObject,
    mut v_inst_4049_: *mut leanh::LeanObject,
    mut v_00_u03b2_4050_: *mut leanh::LeanObject,
    mut v_m_4051_: *mut leanh::LeanObject,
    mut v_a_4052_: *mut leanh::LeanObject,
    mut v_f_4053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: u8 = 0;
    v_buckets_4054_ = leanh::lean_ctor_get(v_m_4051_, 1);
    v___x_4055_ = leanh::lean_unsigned_to_nat(0);
    v___x_4056_ = lean_array_get_size(v_buckets_4054_);
    v___x_4057_ = lean_nat_dec_lt(v___x_4055_, v___x_4056_);
    if v___x_4057_ == 0 {
        let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_4053_);
        leanh::lean_dec(v_a_4052_);
        leanh::lean_dec_ref(v_m_4051_);
        leanh::lean_dec_ref(v_inst_4049_);
        leanh::lean_dec_ref(v_inst_4047_);
        v___x_4058_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4058_;
    } else {
        let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4060_: *mut leanh::LeanObject,
    mut v_inst_4061_: *mut leanh::LeanObject,
    mut v_m_4062_: *mut leanh::LeanObject,
    mut v_a_4063_: *mut leanh::LeanObject,
    mut v_f_4064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: u8 = 0;
    v_buckets_4065_ = leanh::lean_ctor_get(v_m_4062_, 1);
    v___x_4066_ = leanh::lean_unsigned_to_nat(0);
    v___x_4067_ = lean_array_get_size(v_buckets_4065_);
    v___x_4068_ = lean_nat_dec_lt(v___x_4066_, v___x_4067_);
    if v___x_4068_ == 0 {
        let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_4064_);
        leanh::lean_dec(v_a_4063_);
        leanh::lean_dec_ref(v_m_4062_);
        leanh::lean_dec_ref(v_inst_4061_);
        leanh::lean_dec_ref(v_inst_4060_);
        v___x_4069_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4069_;
    } else {
        let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4071_: *mut leanh::LeanObject,
    mut v_00_u03b2_4072_: *mut leanh::LeanObject,
    mut v_inst_4073_: *mut leanh::LeanObject,
    mut v_inst_4074_: *mut leanh::LeanObject,
    mut v_inst_4075_: *mut leanh::LeanObject,
    mut v_m_4076_: *mut leanh::LeanObject,
    mut v_a_4077_: *mut leanh::LeanObject,
    mut v_f_4078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    v_buckets_4079_ = leanh::lean_ctor_get(v_m_4076_, 1);
    v___x_4080_ = leanh::lean_unsigned_to_nat(0);
    v___x_4081_ = lean_array_get_size(v_buckets_4079_);
    v___x_4082_ = lean_nat_dec_lt(v___x_4080_, v___x_4081_);
    if v___x_4082_ == 0 {
        let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_4078_);
        leanh::lean_dec(v_a_4077_);
        leanh::lean_dec_ref(v_m_4076_);
        leanh::lean_dec_ref(v_inst_4075_);
        leanh::lean_dec_ref(v_inst_4073_);
        v___x_4083_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4083_;
    } else {
        let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4085_: *mut leanh::LeanObject,
    mut v_inst_4086_: *mut leanh::LeanObject,
    mut v_m_4087_: *mut leanh::LeanObject,
    mut v_a_4088_: *mut leanh::LeanObject,
    mut v_f_4089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: u8 = 0;
    v_buckets_4090_ = leanh::lean_ctor_get(v_m_4087_, 1);
    v___x_4091_ = leanh::lean_unsigned_to_nat(0);
    v___x_4092_ = lean_array_get_size(v_buckets_4090_);
    v___x_4093_ = lean_nat_dec_lt(v___x_4091_, v___x_4092_);
    if v___x_4093_ == 0 {
        let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_4089_);
        leanh::lean_dec(v_a_4088_);
        leanh::lean_dec_ref(v_m_4087_);
        leanh::lean_dec_ref(v_inst_4086_);
        leanh::lean_dec_ref(v_inst_4085_);
        v___x_4094_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4094_;
    } else {
        let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4096_: *mut leanh::LeanObject,
    mut v_inst_4097_: *mut leanh::LeanObject,
    mut v_inst_4098_: *mut leanh::LeanObject,
    mut v_inst_4099_: *mut leanh::LeanObject,
    mut v_00_u03b2_4100_: *mut leanh::LeanObject,
    mut v_m_4101_: *mut leanh::LeanObject,
    mut v_a_4102_: *mut leanh::LeanObject,
    mut v_f_4103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: u8 = 0;
    v_buckets_4104_ = leanh::lean_ctor_get(v_m_4101_, 1);
    v___x_4105_ = leanh::lean_unsigned_to_nat(0);
    v___x_4106_ = lean_array_get_size(v_buckets_4104_);
    v___x_4107_ = lean_nat_dec_lt(v___x_4105_, v___x_4106_);
    if v___x_4107_ == 0 {
        let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_4103_);
        leanh::lean_dec(v_a_4102_);
        leanh::lean_dec_ref(v_m_4101_);
        leanh::lean_dec_ref(v_inst_4099_);
        leanh::lean_dec_ref(v_inst_4097_);
        v___x_4108_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4108_;
    } else {
        let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_f_4110_: *mut leanh::LeanObject,
    mut v_a_4111_: *mut leanh::LeanObject,
    mut v_b_4112_: *mut leanh::LeanObject,
    mut v_d_4113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = leanh::lean_apply_3(v_f_4110_, v_d_4113_, v_a_4111_, v_b_4112_);
    return v___x_4114_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1(
    mut v_inst_4115_: *mut leanh::LeanObject,
    mut v___f_4116_: *mut leanh::LeanObject,
    mut v_l_4117_: *mut leanh::LeanObject,
    mut v_acc_4118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v_inst_4115_,
        v___f_4116_,
        v_acc_4118_,
        v_l_4117_,
    );
    return v___x_4119_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRevM___redArg(
    mut v_inst_4120_: *mut leanh::LeanObject,
    mut v_f_4121_: *mut leanh::LeanObject,
    mut v_init_4122_: *mut leanh::LeanObject,
    mut v_b_4123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    v_buckets_4124_ = leanh::lean_ctor_get(v_b_4123_, 1);
    leanh::lean_inc_ref(v_buckets_4124_);
    leanh::lean_dec_ref(v_b_4123_);
    v___x_4125_ = lean_array_get_size(v_buckets_4124_);
    v___x_4126_ = leanh::lean_unsigned_to_nat(0);
    v___x_4127_ = lean_nat_dec_lt(v___x_4126_, v___x_4125_);
    if v___x_4127_ == 0 {
        let mut v_toApplicative_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_4124_);
        leanh::lean_dec(v_f_4121_);
        v_toApplicative_4128_ = leanh::lean_ctor_get(v_inst_4120_, 0);
        leanh::lean_inc_ref(v_toApplicative_4128_);
        leanh::lean_dec_ref(v_inst_4120_);
        v_toPure_4129_ = leanh::lean_ctor_get(v_toApplicative_4128_, 1);
        leanh::lean_inc(v_toPure_4129_);
        leanh::lean_dec_ref(v_toApplicative_4128_);
        v___x_4130_ =
            leanh::lean_apply_2(v_toPure_4129_, leanh::lean_box(0), v_init_4122_);
        return v___x_4130_;
    } else {
        let mut v___f_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4133_: usize = 0;
        let mut v___x_4134_: usize = 0;
        let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4131_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4131_, 0, v_f_4121_);
        leanh::lean_inc_ref(v_inst_4120_);
        v___f_4132_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4132_, 0, v_inst_4120_);
        leanh::lean_closure_set(v___f_4132_, 1, v___f_4131_);
        v___x_4133_ = lean_usize_of_nat(v___x_4125_);
        v___x_4134_ = 0usize;
        v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_4136_: *mut leanh::LeanObject,
    mut v_00_u03b2_4137_: *mut leanh::LeanObject,
    mut v_00_u03b4_4138_: *mut leanh::LeanObject,
    mut v_m_4139_: *mut leanh::LeanObject,
    mut v_inst_4140_: *mut leanh::LeanObject,
    mut v_f_4141_: *mut leanh::LeanObject,
    mut v_init_4142_: *mut leanh::LeanObject,
    mut v_b_4143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    v_buckets_4144_ = leanh::lean_ctor_get(v_b_4143_, 1);
    leanh::lean_inc_ref(v_buckets_4144_);
    leanh::lean_dec_ref(v_b_4143_);
    v___x_4145_ = lean_array_get_size(v_buckets_4144_);
    v___x_4146_ = leanh::lean_unsigned_to_nat(0);
    v___x_4147_ = lean_nat_dec_lt(v___x_4146_, v___x_4145_);
    if v___x_4147_ == 0 {
        let mut v_toApplicative_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_4144_);
        leanh::lean_dec(v_f_4141_);
        v_toApplicative_4148_ = leanh::lean_ctor_get(v_inst_4140_, 0);
        leanh::lean_inc_ref(v_toApplicative_4148_);
        leanh::lean_dec_ref(v_inst_4140_);
        v_toPure_4149_ = leanh::lean_ctor_get(v_toApplicative_4148_, 1);
        leanh::lean_inc(v_toPure_4149_);
        leanh::lean_dec_ref(v_toApplicative_4148_);
        v___x_4150_ =
            leanh::lean_apply_2(v_toPure_4149_, leanh::lean_box(0), v_init_4142_);
        return v___x_4150_;
    } else {
        let mut v___f_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4153_: usize = 0;
        let mut v___x_4154_: usize = 0;
        let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4151_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4151_, 0, v_f_4141_);
        leanh::lean_inc_ref(v_inst_4140_);
        v___f_4152_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4152_, 0, v_inst_4140_);
        leanh::lean_closure_set(v___f_4152_, 1, v___f_4151_);
        v___x_4153_ = lean_usize_of_nat(v___x_4145_);
        v___x_4154_ = 0usize;
        v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v___x_4156_: *mut leanh::LeanObject,
    mut v___f_4157_: *mut leanh::LeanObject,
    mut v_l_4158_: *mut leanh::LeanObject,
    mut v_acc_4159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_4156_,
        v___f_4157_,
        v_acc_4159_,
        v_l_4158_,
    );
    return v___x_4160_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_foldRev___redArg(
    mut v_f_4180_: *mut leanh::LeanObject,
    mut v_init_4181_: *mut leanh::LeanObject,
    mut v_b_4182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: u8 = 0;
    v___x_4183_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4184_ = leanh::lean_ctor_get(v_b_4182_, 1);
    leanh::lean_inc_ref(v_buckets_4184_);
    leanh::lean_dec_ref(v_b_4182_);
    v___x_4185_ = lean_array_get_size(v_buckets_4184_);
    v___x_4186_ = leanh::lean_unsigned_to_nat(0);
    v___x_4187_ = lean_nat_dec_lt(v___x_4186_, v___x_4185_);
    if v___x_4187_ == 0 {
        leanh::lean_dec_ref(v_buckets_4184_);
        leanh::lean_dec(v_f_4180_);
        return v_init_4181_;
    } else {
        let mut v___f_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4190_: usize = 0;
        let mut v___x_4191_: usize = 0;
        let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4188_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4188_, 0, v_f_4180_);
        v___f_4189_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4189_, 0, v___x_4183_);
        leanh::lean_closure_set(v___f_4189_, 1, v___f_4188_);
        v___x_4190_ = lean_usize_of_nat(v___x_4185_);
        v___x_4191_ = 0usize;
        v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_4193_: *mut leanh::LeanObject,
    mut v_00_u03b2_4194_: *mut leanh::LeanObject,
    mut v_00_u03b4_4195_: *mut leanh::LeanObject,
    mut v_f_4196_: *mut leanh::LeanObject,
    mut v_init_4197_: *mut leanh::LeanObject,
    mut v_b_4198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u8 = 0;
    v___x_4199_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4200_ = leanh::lean_ctor_get(v_b_4198_, 1);
    leanh::lean_inc_ref(v_buckets_4200_);
    leanh::lean_dec_ref(v_b_4198_);
    v___x_4201_ = lean_array_get_size(v_buckets_4200_);
    v___x_4202_ = leanh::lean_unsigned_to_nat(0);
    v___x_4203_ = lean_nat_dec_lt(v___x_4202_, v___x_4201_);
    if v___x_4203_ == 0 {
        leanh::lean_dec_ref(v_buckets_4200_);
        leanh::lean_dec(v_f_4196_);
        return v_init_4197_;
    } else {
        let mut v___f_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4206_: usize = 0;
        let mut v___x_4207_: usize = 0;
        let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4204_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4204_, 0, v_f_4196_);
        v___f_4205_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4205_, 0, v___x_4199_);
        leanh::lean_closure_set(v___f_4205_, 1, v___f_4204_);
        v___x_4206_ = lean_usize_of_nat(v___x_4201_);
        v___x_4207_ = 0usize;
        v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_inst_4209_: *mut leanh::LeanObject,
    mut v_f_4210_: *mut leanh::LeanObject,
    mut v_init_4211_: *mut leanh::LeanObject,
    mut v_b_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: u8 = 0;
    v_buckets_4213_ = leanh::lean_ctor_get(v_b_4212_, 1);
    leanh::lean_inc_ref(v_buckets_4213_);
    leanh::lean_dec_ref(v_b_4212_);
    v___x_4214_ = lean_array_get_size(v_buckets_4213_);
    v___x_4215_ = leanh::lean_unsigned_to_nat(0);
    v___x_4216_ = lean_nat_dec_lt(v___x_4215_, v___x_4214_);
    if v___x_4216_ == 0 {
        let mut v_toApplicative_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_4213_);
        leanh::lean_dec(v_f_4210_);
        v_toApplicative_4217_ = leanh::lean_ctor_get(v_inst_4209_, 0);
        leanh::lean_inc_ref(v_toApplicative_4217_);
        leanh::lean_dec_ref(v_inst_4209_);
        v_toPure_4218_ = leanh::lean_ctor_get(v_toApplicative_4217_, 1);
        leanh::lean_inc(v_toPure_4218_);
        leanh::lean_dec_ref(v_toApplicative_4217_);
        v___x_4219_ =
            leanh::lean_apply_2(v_toPure_4218_, leanh::lean_box(0), v_init_4211_);
        return v___x_4219_;
    } else {
        let mut v___f_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4222_: usize = 0;
        let mut v___x_4223_: usize = 0;
        let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4220_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4220_, 0, v_f_4210_);
        leanh::lean_inc_ref(v_inst_4209_);
        v___f_4221_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4221_, 0, v_inst_4209_);
        leanh::lean_closure_set(v___f_4221_, 1, v___f_4220_);
        v___x_4222_ = lean_usize_of_nat(v___x_4214_);
        v___x_4223_ = 0usize;
        v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_4225_: *mut leanh::LeanObject,
    mut v_00_u03b2_4226_: *mut leanh::LeanObject,
    mut v_00_u03b4_4227_: *mut leanh::LeanObject,
    mut v_m_4228_: *mut leanh::LeanObject,
    mut v_inst_4229_: *mut leanh::LeanObject,
    mut v_f_4230_: *mut leanh::LeanObject,
    mut v_init_4231_: *mut leanh::LeanObject,
    mut v_b_4232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    v_buckets_4233_ = leanh::lean_ctor_get(v_b_4232_, 1);
    leanh::lean_inc_ref(v_buckets_4233_);
    leanh::lean_dec_ref(v_b_4232_);
    v___x_4234_ = lean_array_get_size(v_buckets_4233_);
    v___x_4235_ = leanh::lean_unsigned_to_nat(0);
    v___x_4236_ = lean_nat_dec_lt(v___x_4235_, v___x_4234_);
    if v___x_4236_ == 0 {
        let mut v_toApplicative_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_4233_);
        leanh::lean_dec(v_f_4230_);
        v_toApplicative_4237_ = leanh::lean_ctor_get(v_inst_4229_, 0);
        leanh::lean_inc_ref(v_toApplicative_4237_);
        leanh::lean_dec_ref(v_inst_4229_);
        v_toPure_4238_ = leanh::lean_ctor_get(v_toApplicative_4237_, 1);
        leanh::lean_inc(v_toPure_4238_);
        leanh::lean_dec_ref(v_toApplicative_4237_);
        v___x_4239_ =
            leanh::lean_apply_2(v_toPure_4238_, leanh::lean_box(0), v_init_4231_);
        return v___x_4239_;
    } else {
        let mut v___f_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4242_: usize = 0;
        let mut v___x_4243_: usize = 0;
        let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4240_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4240_, 0, v_f_4230_);
        leanh::lean_inc_ref(v_inst_4229_);
        v___f_4241_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4241_, 0, v_inst_4229_);
        leanh::lean_closure_set(v___f_4241_, 1, v___f_4240_);
        v___x_4242_ = lean_usize_of_nat(v___x_4234_);
        v___x_4243_ = 0usize;
        v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_f_4245_: *mut leanh::LeanObject,
    mut v_init_4246_: *mut leanh::LeanObject,
    mut v_b_4247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    v___x_4248_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4249_ = leanh::lean_ctor_get(v_b_4247_, 1);
    leanh::lean_inc_ref(v_buckets_4249_);
    leanh::lean_dec_ref(v_b_4247_);
    v___x_4250_ = lean_array_get_size(v_buckets_4249_);
    v___x_4251_ = leanh::lean_unsigned_to_nat(0);
    v___x_4252_ = lean_nat_dec_lt(v___x_4251_, v___x_4250_);
    if v___x_4252_ == 0 {
        leanh::lean_dec_ref(v_buckets_4249_);
        leanh::lean_dec(v_f_4245_);
        return v_init_4246_;
    } else {
        let mut v___f_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4255_: usize = 0;
        let mut v___x_4256_: usize = 0;
        let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4253_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4253_, 0, v_f_4245_);
        v___f_4254_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4254_, 0, v___x_4248_);
        leanh::lean_closure_set(v___f_4254_, 1, v___f_4253_);
        v___x_4255_ = lean_usize_of_nat(v___x_4250_);
        v___x_4256_ = 0usize;
        v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_4258_: *mut leanh::LeanObject,
    mut v_00_u03b2_4259_: *mut leanh::LeanObject,
    mut v_00_u03b4_4260_: *mut leanh::LeanObject,
    mut v_f_4261_: *mut leanh::LeanObject,
    mut v_init_4262_: *mut leanh::LeanObject,
    mut v_b_4263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    v___x_4264_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4265_ = leanh::lean_ctor_get(v_b_4263_, 1);
    leanh::lean_inc_ref(v_buckets_4265_);
    leanh::lean_dec_ref(v_b_4263_);
    v___x_4266_ = lean_array_get_size(v_buckets_4265_);
    v___x_4267_ = leanh::lean_unsigned_to_nat(0);
    v___x_4268_ = lean_nat_dec_lt(v___x_4267_, v___x_4266_);
    if v___x_4268_ == 0 {
        leanh::lean_dec_ref(v_buckets_4265_);
        leanh::lean_dec(v_f_4261_);
        return v_init_4262_;
    } else {
        let mut v___f_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4271_: usize = 0;
        let mut v___x_4272_: usize = 0;
        let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4269_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRevM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4269_, 0, v_f_4261_);
        v___f_4270_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4270_, 0, v___x_4264_);
        leanh::lean_closure_set(v___f_4270_, 1, v___f_4269_);
        v___x_4271_ = lean_usize_of_nat(v___x_4266_);
        v___x_4272_ = 0usize;
        v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_f_4274_: *mut leanh::LeanObject,
    mut v_x_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4278_, 0, v___y_4276_);
    leanh::lean_ctor_set(v___x_4278_, 1, v___y_4277_);
    v___x_4279_ = leanh::lean_apply_1(v_f_4274_, v___x_4278_);
    return v___x_4279_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1(
    mut v_inst_4280_: *mut leanh::LeanObject,
    mut v___f_4281_: *mut leanh::LeanObject,
    mut v_x_4282_: *mut leanh::LeanObject,
    mut v___y_4283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = leanh::lean_box(0);
    v___x_4285_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_4280_,
        v___f_4281_,
        v___x_4284_,
        v___y_4283_,
    );
    return v___x_4285_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forMUncurried___redArg(
    mut v_inst_4286_: *mut leanh::LeanObject,
    mut v_f_4287_: *mut leanh::LeanObject,
    mut v_b_4288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    v_buckets_4289_ = leanh::lean_ctor_get(v_b_4288_, 1);
    leanh::lean_inc_ref(v_buckets_4289_);
    leanh::lean_dec_ref(v_b_4288_);
    v___x_4290_ = leanh::lean_unsigned_to_nat(0);
    v___x_4291_ = lean_array_get_size(v_buckets_4289_);
    v___x_4292_ = leanh::lean_box(0);
    v___x_4293_ = lean_nat_dec_lt(v___x_4290_, v___x_4291_);
    if v___x_4293_ == 0 {
        let mut v_toApplicative_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_4289_);
        leanh::lean_dec(v_f_4287_);
        v_toApplicative_4294_ = leanh::lean_ctor_get(v_inst_4286_, 0);
        leanh::lean_inc_ref(v_toApplicative_4294_);
        leanh::lean_dec_ref(v_inst_4286_);
        v_toPure_4295_ = leanh::lean_ctor_get(v_toApplicative_4294_, 1);
        leanh::lean_inc(v_toPure_4295_);
        leanh::lean_dec_ref(v_toApplicative_4294_);
        v___x_4296_ =
            leanh::lean_apply_2(v_toPure_4295_, leanh::lean_box(0), v___x_4292_);
        return v___x_4296_;
    } else {
        let mut v___f_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: u8 = 0;
        v___f_4297_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4297_, 0, v_f_4287_);
        leanh::lean_inc_ref(v_inst_4286_);
        v___f_4298_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4298_, 0, v_inst_4286_);
        leanh::lean_closure_set(v___f_4298_, 1, v___f_4297_);
        v___x_4299_ = lean_nat_dec_le(v___x_4291_, v___x_4291_);
        if v___x_4299_ == 0 {
            if v___x_4293_ == 0 {
                let mut v_toApplicative_4300_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_4298_);
                leanh::lean_dec_ref(v_buckets_4289_);
                v_toApplicative_4300_ = leanh::lean_ctor_get(v_inst_4286_, 0);
                leanh::lean_inc_ref(v_toApplicative_4300_);
                leanh::lean_dec_ref(v_inst_4286_);
                v_toPure_4301_ = leanh::lean_ctor_get(v_toApplicative_4300_, 1);
                leanh::lean_inc(v_toPure_4301_);
                leanh::lean_dec_ref(v_toApplicative_4300_);
                v___x_4302_ = leanh::lean_apply_2(
                    v_toPure_4301_,
                    leanh::lean_box(0),
                    v___x_4292_,
                );
                return v___x_4302_;
            } else {
                let mut v___x_4303_: usize = 0;
                let mut v___x_4304_: usize = 0;
                let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4303_ = 0usize;
                v___x_4304_ = lean_usize_of_nat(v___x_4291_);
                v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4306_ = 0usize;
            v___x_4307_ = lean_usize_of_nat(v___x_4291_);
            v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_4309_: *mut leanh::LeanObject,
    mut v_m_4310_: *mut leanh::LeanObject,
    mut v_inst_4311_: *mut leanh::LeanObject,
    mut v_00_u03b2_4312_: *mut leanh::LeanObject,
    mut v_f_4313_: *mut leanh::LeanObject,
    mut v_b_4314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    v_buckets_4315_ = leanh::lean_ctor_get(v_b_4314_, 1);
    leanh::lean_inc_ref(v_buckets_4315_);
    leanh::lean_dec_ref(v_b_4314_);
    v___x_4316_ = leanh::lean_unsigned_to_nat(0);
    v___x_4317_ = lean_array_get_size(v_buckets_4315_);
    v___x_4318_ = leanh::lean_box(0);
    v___x_4319_ = lean_nat_dec_lt(v___x_4316_, v___x_4317_);
    if v___x_4319_ == 0 {
        let mut v_toApplicative_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_4315_);
        leanh::lean_dec(v_f_4313_);
        v_toApplicative_4320_ = leanh::lean_ctor_get(v_inst_4311_, 0);
        leanh::lean_inc_ref(v_toApplicative_4320_);
        leanh::lean_dec_ref(v_inst_4311_);
        v_toPure_4321_ = leanh::lean_ctor_get(v_toApplicative_4320_, 1);
        leanh::lean_inc(v_toPure_4321_);
        leanh::lean_dec_ref(v_toApplicative_4320_);
        v___x_4322_ =
            leanh::lean_apply_2(v_toPure_4321_, leanh::lean_box(0), v___x_4318_);
        return v___x_4322_;
    } else {
        let mut v___f_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4325_: u8 = 0;
        v___f_4323_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_4323_, 0, v_f_4313_);
        leanh::lean_inc_ref(v_inst_4311_);
        v___f_4324_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4324_, 0, v_inst_4311_);
        leanh::lean_closure_set(v___f_4324_, 1, v___f_4323_);
        v___x_4325_ = lean_nat_dec_le(v___x_4317_, v___x_4317_);
        if v___x_4325_ == 0 {
            if v___x_4319_ == 0 {
                let mut v_toApplicative_4326_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_4324_);
                leanh::lean_dec_ref(v_buckets_4315_);
                v_toApplicative_4326_ = leanh::lean_ctor_get(v_inst_4311_, 0);
                leanh::lean_inc_ref(v_toApplicative_4326_);
                leanh::lean_dec_ref(v_inst_4311_);
                v_toPure_4327_ = leanh::lean_ctor_get(v_toApplicative_4326_, 1);
                leanh::lean_inc(v_toPure_4327_);
                leanh::lean_dec_ref(v_toApplicative_4326_);
                v___x_4328_ = leanh::lean_apply_2(
                    v_toPure_4327_,
                    leanh::lean_box(0),
                    v___x_4318_,
                );
                return v___x_4328_;
            } else {
                let mut v___x_4329_: usize = 0;
                let mut v___x_4330_: usize = 0;
                let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4329_ = 0usize;
                v___x_4330_ = lean_usize_of_nat(v___x_4317_);
                v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4332_ = 0usize;
            v___x_4333_ = lean_usize_of_nat(v___x_4317_);
            v___x_4334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_f_4335_: *mut leanh::LeanObject,
    mut v_a_4336_: *mut leanh::LeanObject,
    mut v_b_4337_: *mut leanh::LeanObject,
    mut v_d_4338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4339_, 0, v_a_4336_);
    leanh::lean_ctor_set(v___x_4339_, 1, v_b_4337_);
    v___x_4340_ = leanh::lean_apply_2(v_f_4335_, v___x_4339_, v_d_4338_);
    return v___x_4340_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1(
    mut v_inst_4341_: *mut leanh::LeanObject,
    mut v___f_4342_: *mut leanh::LeanObject,
    mut v_a_4343_: *mut leanh::LeanObject,
    mut v_x_4344_: *mut leanh::LeanObject,
    mut v___y_4345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_inst_4341_, v___f_4342_, v_a_4343_, v___y_4345_);
    return v___x_4346_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_forInUncurried___redArg(
    mut v_inst_4347_: *mut leanh::LeanObject,
    mut v_f_4348_: *mut leanh::LeanObject,
    mut v_init_4349_: *mut leanh::LeanObject,
    mut v_b_4350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4354_: usize = 0;
    let mut v___x_4355_: usize = 0;
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4351_ = leanh::lean_ctor_get(v_b_4350_, 1);
    leanh::lean_inc_ref(v_buckets_4351_);
    leanh::lean_dec_ref(v_b_4350_);
    v___f_4352_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4352_, 0, v_f_4348_);
    leanh::lean_inc_ref(v_inst_4347_);
    v___f_4353_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_4353_, 0, v_inst_4347_);
    leanh::lean_closure_set(v___f_4353_, 1, v___f_4352_);
    v_sz_4354_ = lean_array_size(v_buckets_4351_);
    v___x_4355_ = 0usize;
    v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
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
    mut v_00_u03b1_4357_: *mut leanh::LeanObject,
    mut v_00_u03b4_4358_: *mut leanh::LeanObject,
    mut v_m_4359_: *mut leanh::LeanObject,
    mut v_inst_4360_: *mut leanh::LeanObject,
    mut v_00_u03b2_4361_: *mut leanh::LeanObject,
    mut v_f_4362_: *mut leanh::LeanObject,
    mut v_init_4363_: *mut leanh::LeanObject,
    mut v_b_4364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4368_: usize = 0;
    let mut v___x_4369_: usize = 0;
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4365_ = leanh::lean_ctor_get(v_b_4364_, 1);
    leanh::lean_inc_ref(v_buckets_4365_);
    leanh::lean_dec_ref(v_b_4364_);
    v___f_4366_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4366_, 0, v_f_4362_);
    leanh::lean_inc_ref(v_inst_4360_);
    v___f_4367_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_4367_, 0, v_inst_4360_);
    leanh::lean_closure_set(v___f_4367_, 1, v___f_4366_);
    v_sz_4368_ = lean_array_size(v_buckets_4365_);
    v___x_4369_ = 0usize;
    v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
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
    mut v_f_4371_: *mut leanh::LeanObject,
    mut v_m_4372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    v_buckets_4373_ = leanh::lean_ctor_get(v_m_4372_, 1);
    v___x_4374_ = leanh::lean_unsigned_to_nat(0);
    v___x_4375_ = lean_array_get_size(v_buckets_4373_);
    v___x_4376_ = lean_nat_dec_lt(v___x_4374_, v___x_4375_);
    if v___x_4376_ == 0 {
        let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4372_);
        leanh::lean_dec_ref(v_f_4371_);
        v___x_4377_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4377_;
    } else {
        let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4378_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4371_, v_m_4372_);
        return v___x_4378_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_filterMap(
    mut v_00_u03b1_4379_: *mut leanh::LeanObject,
    mut v_00_u03b2_4380_: *mut leanh::LeanObject,
    mut v_00_u03b3_4381_: *mut leanh::LeanObject,
    mut v_f_4382_: *mut leanh::LeanObject,
    mut v_m_4383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    v_buckets_4384_ = leanh::lean_ctor_get(v_m_4383_, 1);
    v___x_4385_ = leanh::lean_unsigned_to_nat(0);
    v___x_4386_ = lean_array_get_size(v_buckets_4384_);
    v___x_4387_ = lean_nat_dec_lt(v___x_4385_, v___x_4386_);
    if v___x_4387_ == 0 {
        let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4383_);
        leanh::lean_dec_ref(v_f_4382_);
        v___x_4388_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4388_;
    } else {
        let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4389_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_4382_, v_m_4383_);
        return v___x_4389_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_map___redArg(
    mut v_f_4390_: *mut leanh::LeanObject,
    mut v_m_4391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: u8 = 0;
    v_buckets_4392_ = leanh::lean_ctor_get(v_m_4391_, 1);
    v___x_4393_ = leanh::lean_unsigned_to_nat(0);
    v___x_4394_ = lean_array_get_size(v_buckets_4392_);
    v___x_4395_ = lean_nat_dec_lt(v___x_4393_, v___x_4394_);
    if v___x_4395_ == 0 {
        let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4391_);
        leanh::lean_dec(v_f_4390_);
        v___x_4396_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4396_;
    } else {
        let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4397_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4390_, v_m_4391_);
        return v___x_4397_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_map(
    mut v_00_u03b1_4398_: *mut leanh::LeanObject,
    mut v_00_u03b2_4399_: *mut leanh::LeanObject,
    mut v_00_u03b3_4400_: *mut leanh::LeanObject,
    mut v_f_4401_: *mut leanh::LeanObject,
    mut v_m_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: u8 = 0;
    v_buckets_4403_ = leanh::lean_ctor_get(v_m_4402_, 1);
    v___x_4404_ = leanh::lean_unsigned_to_nat(0);
    v___x_4405_ = lean_array_get_size(v_buckets_4403_);
    v___x_4406_ = lean_nat_dec_lt(v___x_4404_, v___x_4405_);
    if v___x_4406_ == 0 {
        let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4402_);
        leanh::lean_dec(v_f_4401_);
        v___x_4407_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4407_;
    } else {
        let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4408_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_4401_, v_m_4402_);
        return v___x_4408_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_filter___redArg(
    mut v_f_4409_: *mut leanh::LeanObject,
    mut v_m_4410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    v_buckets_4411_ = leanh::lean_ctor_get(v_m_4410_, 1);
    v___x_4412_ = leanh::lean_unsigned_to_nat(0);
    v___x_4413_ = lean_array_get_size(v_buckets_4411_);
    v___x_4414_ = lean_nat_dec_lt(v___x_4412_, v___x_4413_);
    if v___x_4414_ == 0 {
        let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4410_);
        leanh::lean_dec_ref(v_f_4409_);
        v___x_4415_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4415_;
    } else {
        let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4416_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4409_, v_m_4410_);
        return v___x_4416_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_filter(
    mut v_00_u03b1_4417_: *mut leanh::LeanObject,
    mut v_00_u03b2_4418_: *mut leanh::LeanObject,
    mut v_f_4419_: *mut leanh::LeanObject,
    mut v_m_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: u8 = 0;
    v_buckets_4421_ = leanh::lean_ctor_get(v_m_4420_, 1);
    v___x_4422_ = leanh::lean_unsigned_to_nat(0);
    v___x_4423_ = lean_array_get_size(v_buckets_4421_);
    v___x_4424_ = lean_nat_dec_lt(v___x_4422_, v___x_4423_);
    if v___x_4424_ == 0 {
        let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_m_4420_);
        leanh::lean_dec_ref(v_f_4419_);
        v___x_4425_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
        );
        return v___x_4425_;
    } else {
        let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4426_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_4419_, v_m_4420_);
        return v___x_4426_;
    }
}
pub unsafe fn l_Std_DHashMap_Raw_toArray___redArg___lam__0(
    mut v_x1_4427_: *mut leanh::LeanObject,
    mut v_x2_4428_: *mut leanh::LeanObject,
    mut v_x3_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4430_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4430_, 0, v_x2_4428_);
    leanh::lean_ctor_set(v___x_4430_, 1, v_x3_4429_);
    v___x_4431_ = lean_array_push(v_x1_4427_, v___x_4430_);
    return v___x_4431_;
}
pub unsafe fn l_Std_DHashMap_Raw_toArray___redArg___lam__1(
    mut v___x_4432_: *mut leanh::LeanObject,
    mut v___f_4433_: *mut leanh::LeanObject,
    mut v_acc_4434_: *mut leanh::LeanObject,
    mut v_l_4435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4436_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4432_,
        v___f_4433_,
        v_acc_4434_,
        v_l_4435_,
    );
    return v___x_4436_;
}
pub unsafe fn l_Std_DHashMap_Raw_toArray___redArg(
    mut v_m_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    v_size_4442_ = leanh::lean_ctor_get(v_m_4441_, 0);
    leanh::lean_inc(v_size_4442_);
    v_buckets_4443_ = leanh::lean_ctor_get(v_m_4441_, 1);
    leanh::lean_inc_ref(v_buckets_4443_);
    leanh::lean_dec_ref(v_m_4441_);
    v___x_4444_ = lean_mk_empty_array_with_capacity(v_size_4442_);
    leanh::lean_dec(v_size_4442_);
    v___x_4445_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4446_ = leanh::lean_unsigned_to_nat(0);
    v___x_4447_ = lean_array_get_size(v_buckets_4443_);
    v___x_4448_ = lean_nat_dec_lt(v___x_4446_, v___x_4447_);
    if v___x_4448_ == 0 {
        leanh::lean_dec_ref(v_buckets_4443_);
        return v___x_4444_;
    } else {
        let mut v___f_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4450_: u8 = 0;
        v___f_4449_ = l_Std_DHashMap_Raw_toArray___redArg___closed__1;
        v___x_4450_ = lean_nat_dec_le(v___x_4447_, v___x_4447_);
        if v___x_4450_ == 0 {
            if v___x_4448_ == 0 {
                leanh::lean_dec_ref(v_buckets_4443_);
                return v___x_4444_;
            } else {
                let mut v___x_4451_: usize = 0;
                let mut v___x_4452_: usize = 0;
                let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4451_ = 0usize;
                v___x_4452_ = lean_usize_of_nat(v___x_4447_);
                v___x_4453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4454_ = 0usize;
            v___x_4455_ = lean_usize_of_nat(v___x_4447_);
            v___x_4456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_4457_: *mut leanh::LeanObject,
    mut v_00_u03b2_4458_: *mut leanh::LeanObject,
    mut v_m_4459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: u8 = 0;
    v_size_4460_ = leanh::lean_ctor_get(v_m_4459_, 0);
    leanh::lean_inc(v_size_4460_);
    v_buckets_4461_ = leanh::lean_ctor_get(v_m_4459_, 1);
    leanh::lean_inc_ref(v_buckets_4461_);
    leanh::lean_dec_ref(v_m_4459_);
    v___x_4462_ = lean_mk_empty_array_with_capacity(v_size_4460_);
    leanh::lean_dec(v_size_4460_);
    v___x_4463_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4464_ = leanh::lean_unsigned_to_nat(0);
    v___x_4465_ = lean_array_get_size(v_buckets_4461_);
    v___x_4466_ = lean_nat_dec_lt(v___x_4464_, v___x_4465_);
    if v___x_4466_ == 0 {
        leanh::lean_dec_ref(v_buckets_4461_);
        return v___x_4462_;
    } else {
        let mut v___f_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4468_: u8 = 0;
        v___f_4467_ = l_Std_DHashMap_Raw_toArray___redArg___closed__1;
        v___x_4468_ = lean_nat_dec_le(v___x_4465_, v___x_4465_);
        if v___x_4468_ == 0 {
            if v___x_4466_ == 0 {
                leanh::lean_dec_ref(v_buckets_4461_);
                return v___x_4462_;
            } else {
                let mut v___x_4469_: usize = 0;
                let mut v___x_4470_: usize = 0;
                let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4469_ = 0usize;
                v___x_4470_ = lean_usize_of_nat(v___x_4465_);
                v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4472_ = 0usize;
            v___x_4473_ = lean_usize_of_nat(v___x_4465_);
            v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_x1_4475_: *mut leanh::LeanObject,
    mut v_x2_4476_: *mut leanh::LeanObject,
    mut v_x3_4477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4478_, 0, v_x2_4476_);
    leanh::lean_ctor_set(v___x_4478_, 1, v_x3_4477_);
    v___x_4479_ = lean_array_push(v_x1_4475_, v___x_4478_);
    return v___x_4479_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toArray___redArg___lam__1(
    mut v___x_4480_: *mut leanh::LeanObject,
    mut v___f_4481_: *mut leanh::LeanObject,
    mut v_acc_4482_: *mut leanh::LeanObject,
    mut v_l_4483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4480_,
        v___f_4481_,
        v_acc_4482_,
        v_l_4483_,
    );
    return v___x_4484_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toArray___redArg(
    mut v_m_4489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    v_size_4490_ = leanh::lean_ctor_get(v_m_4489_, 0);
    leanh::lean_inc(v_size_4490_);
    v_buckets_4491_ = leanh::lean_ctor_get(v_m_4489_, 1);
    leanh::lean_inc_ref(v_buckets_4491_);
    leanh::lean_dec_ref(v_m_4489_);
    v___x_4492_ = lean_mk_empty_array_with_capacity(v_size_4490_);
    leanh::lean_dec(v_size_4490_);
    v___x_4493_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4494_ = leanh::lean_unsigned_to_nat(0);
    v___x_4495_ = lean_array_get_size(v_buckets_4491_);
    v___x_4496_ = lean_nat_dec_lt(v___x_4494_, v___x_4495_);
    if v___x_4496_ == 0 {
        leanh::lean_dec_ref(v_buckets_4491_);
        return v___x_4492_;
    } else {
        let mut v___f_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4498_: u8 = 0;
        v___f_4497_ = l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1;
        v___x_4498_ = lean_nat_dec_le(v___x_4495_, v___x_4495_);
        if v___x_4498_ == 0 {
            if v___x_4496_ == 0 {
                leanh::lean_dec_ref(v_buckets_4491_);
                return v___x_4492_;
            } else {
                let mut v___x_4499_: usize = 0;
                let mut v___x_4500_: usize = 0;
                let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4499_ = 0usize;
                v___x_4500_ = lean_usize_of_nat(v___x_4495_);
                v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4502_ = 0usize;
            v___x_4503_ = lean_usize_of_nat(v___x_4495_);
            v___x_4504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_4505_: *mut leanh::LeanObject,
    mut v_00_u03b2_4506_: *mut leanh::LeanObject,
    mut v_m_4507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    v_size_4508_ = leanh::lean_ctor_get(v_m_4507_, 0);
    leanh::lean_inc(v_size_4508_);
    v_buckets_4509_ = leanh::lean_ctor_get(v_m_4507_, 1);
    leanh::lean_inc_ref(v_buckets_4509_);
    leanh::lean_dec_ref(v_m_4507_);
    v___x_4510_ = lean_mk_empty_array_with_capacity(v_size_4508_);
    leanh::lean_dec(v_size_4508_);
    v___x_4511_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4512_ = leanh::lean_unsigned_to_nat(0);
    v___x_4513_ = lean_array_get_size(v_buckets_4509_);
    v___x_4514_ = lean_nat_dec_lt(v___x_4512_, v___x_4513_);
    if v___x_4514_ == 0 {
        leanh::lean_dec_ref(v_buckets_4509_);
        return v___x_4510_;
    } else {
        let mut v___f_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4516_: u8 = 0;
        v___f_4515_ = l_Std_DHashMap_Raw_Const_toArray___redArg___closed__1;
        v___x_4516_ = lean_nat_dec_le(v___x_4513_, v___x_4513_);
        if v___x_4516_ == 0 {
            if v___x_4514_ == 0 {
                leanh::lean_dec_ref(v_buckets_4509_);
                return v___x_4510_;
            } else {
                let mut v___x_4517_: usize = 0;
                let mut v___x_4518_: usize = 0;
                let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4517_ = 0usize;
                v___x_4518_ = lean_usize_of_nat(v___x_4513_);
                v___x_4519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4520_ = 0usize;
            v___x_4521_ = lean_usize_of_nat(v___x_4513_);
            v___x_4522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_x1_4523_: *mut leanh::LeanObject,
    mut v_x2_4524_: *mut leanh::LeanObject,
    mut v_x3_4525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = lean_array_push(v_x1_4523_, v_x2_4524_);
    return v___x_4526_;
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(
    mut v_x1_4527_: *mut leanh::LeanObject,
    mut v_x2_4528_: *mut leanh::LeanObject,
    mut v_x3_4529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4530_ =
        l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_4527_, v_x2_4528_, v_x3_4529_);
    leanh::lean_dec(v_x3_4529_);
    return v_res_4530_;
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray___redArg___lam__1(
    mut v___x_4531_: *mut leanh::LeanObject,
    mut v___f_4532_: *mut leanh::LeanObject,
    mut v_acc_4533_: *mut leanh::LeanObject,
    mut v_l_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4531_,
        v___f_4532_,
        v_acc_4533_,
        v_l_4534_,
    );
    return v___x_4535_;
}
pub unsafe fn l_Std_DHashMap_Raw_keysArray___redArg(
    mut v_m_4540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    v_size_4541_ = leanh::lean_ctor_get(v_m_4540_, 0);
    leanh::lean_inc(v_size_4541_);
    v_buckets_4542_ = leanh::lean_ctor_get(v_m_4540_, 1);
    leanh::lean_inc_ref(v_buckets_4542_);
    leanh::lean_dec_ref(v_m_4540_);
    v___x_4543_ = lean_mk_empty_array_with_capacity(v_size_4541_);
    leanh::lean_dec(v_size_4541_);
    v___x_4544_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4545_ = leanh::lean_unsigned_to_nat(0);
    v___x_4546_ = lean_array_get_size(v_buckets_4542_);
    v___x_4547_ = lean_nat_dec_lt(v___x_4545_, v___x_4546_);
    if v___x_4547_ == 0 {
        leanh::lean_dec_ref(v_buckets_4542_);
        return v___x_4543_;
    } else {
        let mut v___f_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4549_: u8 = 0;
        v___f_4548_ = l_Std_DHashMap_Raw_keysArray___redArg___closed__1;
        v___x_4549_ = lean_nat_dec_le(v___x_4546_, v___x_4546_);
        if v___x_4549_ == 0 {
            if v___x_4547_ == 0 {
                leanh::lean_dec_ref(v_buckets_4542_);
                return v___x_4543_;
            } else {
                let mut v___x_4550_: usize = 0;
                let mut v___x_4551_: usize = 0;
                let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4550_ = 0usize;
                v___x_4551_ = lean_usize_of_nat(v___x_4546_);
                v___x_4552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4553_ = 0usize;
            v___x_4554_ = lean_usize_of_nat(v___x_4546_);
            v___x_4555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_4556_: *mut leanh::LeanObject,
    mut v_00_u03b2_4557_: *mut leanh::LeanObject,
    mut v_m_4558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: u8 = 0;
    v_size_4559_ = leanh::lean_ctor_get(v_m_4558_, 0);
    leanh::lean_inc(v_size_4559_);
    v_buckets_4560_ = leanh::lean_ctor_get(v_m_4558_, 1);
    leanh::lean_inc_ref(v_buckets_4560_);
    leanh::lean_dec_ref(v_m_4558_);
    v___x_4561_ = lean_mk_empty_array_with_capacity(v_size_4559_);
    leanh::lean_dec(v_size_4559_);
    v___x_4562_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4563_ = leanh::lean_unsigned_to_nat(0);
    v___x_4564_ = lean_array_get_size(v_buckets_4560_);
    v___x_4565_ = lean_nat_dec_lt(v___x_4563_, v___x_4564_);
    if v___x_4565_ == 0 {
        leanh::lean_dec_ref(v_buckets_4560_);
        return v___x_4561_;
    } else {
        let mut v___f_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4567_: u8 = 0;
        v___f_4566_ = l_Std_DHashMap_Raw_keysArray___redArg___closed__1;
        v___x_4567_ = lean_nat_dec_le(v___x_4564_, v___x_4564_);
        if v___x_4567_ == 0 {
            if v___x_4565_ == 0 {
                leanh::lean_dec_ref(v_buckets_4560_);
                return v___x_4561_;
            } else {
                let mut v___x_4568_: usize = 0;
                let mut v___x_4569_: usize = 0;
                let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4568_ = 0usize;
                v___x_4569_ = lean_usize_of_nat(v___x_4564_);
                v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4571_ = 0usize;
            v___x_4572_ = lean_usize_of_nat(v___x_4564_);
            v___x_4573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_inst_4574_: *mut leanh::LeanObject,
    mut v_inst_4575_: *mut leanh::LeanObject,
    mut v_a_4576_: *mut leanh::LeanObject,
    mut v_b_4577_: *mut leanh::LeanObject,
    mut v_acc_4578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_4579_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_4574_,
        v_inst_4575_,
        v_acc_4578_,
        v_a_4576_,
        v_b_4577_,
    );
    v___x_4580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4580_, 0, v_r_4579_);
    return v___x_4580_;
}
pub unsafe fn l_Std_DHashMap_Raw_union___redArg___lam__1(
    mut v___x_4581_: *mut leanh::LeanObject,
    mut v___f_4582_: *mut leanh::LeanObject,
    mut v_a_4583_: *mut leanh::LeanObject,
    mut v_x_4584_: *mut leanh::LeanObject,
    mut v___y_4585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4586_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_4581_, v___f_4582_, v_a_4583_, v___y_4585_);
    return v___x_4586_;
}
pub unsafe fn l_Std_DHashMap_Raw_union___redArg(
    mut v_inst_4589_: *mut leanh::LeanObject,
    mut v_inst_4590_: *mut leanh::LeanObject,
    mut v_m_u2081_4591_: *mut leanh::LeanObject,
    mut v_m_u2082_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: u8 = 0;
    v_size_4593_ = leanh::lean_ctor_get(v_m_u2081_4591_, 0);
    v_buckets_4594_ = leanh::lean_ctor_get(v_m_u2081_4591_, 1);
    v___x_4595_ = leanh::lean_unsigned_to_nat(0);
    v___x_4596_ = lean_array_get_size(v_buckets_4594_);
    v___x_4597_ = lean_nat_dec_lt(v___x_4595_, v___x_4596_);
    if v___x_4597_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_4591_);
        leanh::lean_dec_ref(v_inst_4590_);
        leanh::lean_dec_ref(v_inst_4589_);
        return v_m_u2082_4592_;
    } else {
        let mut v_size_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4601_: u8 = 0;
        v_size_4598_ = leanh::lean_ctor_get(v_m_u2082_4592_, 0);
        v_buckets_4599_ = leanh::lean_ctor_get(v_m_u2082_4592_, 1);
        v___x_4600_ = lean_array_get_size(v_buckets_4599_);
        v___x_4601_ = lean_nat_dec_lt(v___x_4595_, v___x_4600_);
        if v___x_4601_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4592_);
            leanh::lean_dec_ref(v_inst_4590_);
            leanh::lean_dec_ref(v_inst_4589_);
            return v_m_u2081_4591_;
        } else {
            let mut v___x_4602_: u8 = 0;
            v___x_4602_ = lean_nat_dec_le(v_size_4593_, v_size_4598_);
            if v___x_4602_ == 0 {
                let mut v___f_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___f_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_4608_: usize = 0;
                let mut v___x_4609_: usize = 0;
                let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_buckets_4594_);
                leanh::lean_dec_ref(v_m_u2081_4591_);
                v___f_4605_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_4605_, 0, v_inst_4589_);
                leanh::lean_closure_set(v___f_4605_, 1, v_inst_4590_);
                v___x_4606_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
                v___f_4607_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_4607_, 0, v___x_4606_);
                leanh::lean_closure_set(v___f_4607_, 1, v___f_4605_);
                v_sz_4608_ = lean_array_size(v_buckets_4594_);
                v___x_4609_ = 0usize;
                v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_00_u03b1_4611_: *mut leanh::LeanObject,
    mut v_00_u03b2_4612_: *mut leanh::LeanObject,
    mut v_inst_4613_: *mut leanh::LeanObject,
    mut v_inst_4614_: *mut leanh::LeanObject,
    mut v_m_u2081_4615_: *mut leanh::LeanObject,
    mut v_m_u2082_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    v_size_4617_ = leanh::lean_ctor_get(v_m_u2081_4615_, 0);
    v_buckets_4618_ = leanh::lean_ctor_get(v_m_u2081_4615_, 1);
    v___x_4619_ = leanh::lean_unsigned_to_nat(0);
    v___x_4620_ = lean_array_get_size(v_buckets_4618_);
    v___x_4621_ = lean_nat_dec_lt(v___x_4619_, v___x_4620_);
    if v___x_4621_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_4615_);
        leanh::lean_dec_ref(v_inst_4614_);
        leanh::lean_dec_ref(v_inst_4613_);
        return v_m_u2082_4616_;
    } else {
        let mut v_size_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4625_: u8 = 0;
        v_size_4622_ = leanh::lean_ctor_get(v_m_u2082_4616_, 0);
        v_buckets_4623_ = leanh::lean_ctor_get(v_m_u2082_4616_, 1);
        v___x_4624_ = lean_array_get_size(v_buckets_4623_);
        v___x_4625_ = lean_nat_dec_lt(v___x_4619_, v___x_4624_);
        if v___x_4625_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4616_);
            leanh::lean_dec_ref(v_inst_4614_);
            leanh::lean_dec_ref(v_inst_4613_);
            return v_m_u2081_4615_;
        } else {
            let mut v___x_4626_: u8 = 0;
            v___x_4626_ = lean_nat_dec_le(v_size_4617_, v_size_4622_);
            if v___x_4626_ == 0 {
                let mut v___f_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___f_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_sz_4632_: usize = 0;
                let mut v___x_4633_: usize = 0;
                let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_buckets_4618_);
                leanh::lean_dec_ref(v_m_u2081_4615_);
                v___f_4629_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_4629_, 0, v_inst_4613_);
                leanh::lean_closure_set(v___f_4629_, 1, v_inst_4614_);
                v___x_4630_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
                v___f_4631_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_4631_, 0, v___x_4630_);
                leanh::lean_closure_set(v___f_4631_, 1, v___f_4629_);
                v_sz_4632_ = lean_array_size(v_buckets_4618_);
                v___x_4633_ = 0usize;
                v___x_4634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_inst_4635_: *mut leanh::LeanObject,
    mut v_inst_4636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ =
        leanh::lean_alloc_closure(l_Std_DHashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4637_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4637_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4637_, 2, v_inst_4635_);
    leanh::lean_closure_set(v___x_4637_, 3, v_inst_4636_);
    return v___x_4637_;
}
pub unsafe fn l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(
    mut v_00_u03b1_4638_: *mut leanh::LeanObject,
    mut v_00_u03b2_4639_: *mut leanh::LeanObject,
    mut v_inst_4640_: *mut leanh::LeanObject,
    mut v_inst_4641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4642_ =
        leanh::lean_alloc_closure(l_Std_DHashMap_Raw_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4642_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4642_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4642_, 2, v_inst_4640_);
    leanh::lean_closure_set(v___x_4642_, 3, v_inst_4641_);
    return v___x_4642_;
}
pub unsafe fn l_Std_DHashMap_Raw_inter___redArg(
    mut v_inst_4643_: *mut leanh::LeanObject,
    mut v_inst_4644_: *mut leanh::LeanObject,
    mut v_m_u2081_4645_: *mut leanh::LeanObject,
    mut v_m_u2082_4646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: u8 = 0;
    v_buckets_4647_ = leanh::lean_ctor_get(v_m_u2081_4645_, 1);
    v___x_4648_ = leanh::lean_unsigned_to_nat(0);
    v___x_4649_ = lean_array_get_size(v_buckets_4647_);
    v___x_4650_ = lean_nat_dec_lt(v___x_4648_, v___x_4649_);
    if v___x_4650_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_4645_);
        leanh::lean_dec_ref(v_inst_4644_);
        leanh::lean_dec_ref(v_inst_4643_);
        return v_m_u2082_4646_;
    } else {
        let mut v_buckets_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4653_: u8 = 0;
        v_buckets_4651_ = leanh::lean_ctor_get(v_m_u2082_4646_, 1);
        v___x_4652_ = lean_array_get_size(v_buckets_4651_);
        v___x_4653_ = lean_nat_dec_lt(v___x_4648_, v___x_4652_);
        if v___x_4653_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4646_);
            leanh::lean_dec_ref(v_inst_4644_);
            leanh::lean_dec_ref(v_inst_4643_);
            return v_m_u2081_4645_;
        } else {
            let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4655_: *mut leanh::LeanObject,
    mut v_00_u03b2_4656_: *mut leanh::LeanObject,
    mut v_inst_4657_: *mut leanh::LeanObject,
    mut v_inst_4658_: *mut leanh::LeanObject,
    mut v_m_u2081_4659_: *mut leanh::LeanObject,
    mut v_m_u2082_4660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: u8 = 0;
    v_buckets_4661_ = leanh::lean_ctor_get(v_m_u2081_4659_, 1);
    v___x_4662_ = leanh::lean_unsigned_to_nat(0);
    v___x_4663_ = lean_array_get_size(v_buckets_4661_);
    v___x_4664_ = lean_nat_dec_lt(v___x_4662_, v___x_4663_);
    if v___x_4664_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_4659_);
        leanh::lean_dec_ref(v_inst_4658_);
        leanh::lean_dec_ref(v_inst_4657_);
        return v_m_u2082_4660_;
    } else {
        let mut v_buckets_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4667_: u8 = 0;
        v_buckets_4665_ = leanh::lean_ctor_get(v_m_u2082_4660_, 1);
        v___x_4666_ = lean_array_get_size(v_buckets_4665_);
        v___x_4667_ = lean_nat_dec_lt(v___x_4662_, v___x_4666_);
        if v___x_4667_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4660_);
            leanh::lean_dec_ref(v_inst_4658_);
            leanh::lean_dec_ref(v_inst_4657_);
            return v_m_u2081_4659_;
        } else {
            let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4669_: *mut leanh::LeanObject,
    mut v_inst_4670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4671_ =
        leanh::lean_alloc_closure(l_Std_DHashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4671_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4671_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4671_, 2, v_inst_4669_);
    leanh::lean_closure_set(v___x_4671_, 3, v_inst_4670_);
    return v___x_4671_;
}
pub unsafe fn l_Std_DHashMap_Raw_instInterOfBEqOfHashable(
    mut v_00_u03b1_4672_: *mut leanh::LeanObject,
    mut v_00_u03b2_4673_: *mut leanh::LeanObject,
    mut v_inst_4674_: *mut leanh::LeanObject,
    mut v_inst_4675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4676_ =
        leanh::lean_alloc_closure(l_Std_DHashMap_Raw_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4676_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4676_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4676_, 2, v_inst_4674_);
    leanh::lean_closure_set(v___x_4676_, 3, v_inst_4675_);
    return v___x_4676_;
}
pub unsafe fn l_Std_DHashMap_Raw_beq___redArg(
    mut v_inst_4677_: *mut leanh::LeanObject,
    mut v_inst_4678_: *mut leanh::LeanObject,
    mut v_inst_4679_: *mut leanh::LeanObject,
    mut v_m_u2081_4680_: *mut leanh::LeanObject,
    mut v_m_u2082_4681_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: u8 = 0;
    v_buckets_4682_ = leanh::lean_ctor_get(v_m_u2081_4680_, 1);
    v___x_4683_ = leanh::lean_unsigned_to_nat(0);
    v___x_4684_ = lean_array_get_size(v_buckets_4682_);
    v___x_4685_ = lean_nat_dec_lt(v___x_4683_, v___x_4684_);
    if v___x_4685_ == 0 {
        leanh::lean_dec_ref(v_m_u2082_4681_);
        leanh::lean_dec_ref(v_m_u2081_4680_);
        leanh::lean_dec_ref(v_inst_4679_);
        leanh::lean_dec_ref(v_inst_4678_);
        leanh::lean_dec_ref(v_inst_4677_);
        return v___x_4685_;
    } else {
        let mut v_buckets_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4688_: u8 = 0;
        v_buckets_4686_ = leanh::lean_ctor_get(v_m_u2082_4681_, 1);
        v___x_4687_ = lean_array_get_size(v_buckets_4686_);
        v___x_4688_ = lean_nat_dec_lt(v___x_4683_, v___x_4687_);
        if v___x_4688_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4681_);
            leanh::lean_dec_ref(v_m_u2081_4680_);
            leanh::lean_dec_ref(v_inst_4679_);
            leanh::lean_dec_ref(v_inst_4678_);
            leanh::lean_dec_ref(v_inst_4677_);
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
    mut v_inst_4690_: *mut leanh::LeanObject,
    mut v_inst_4691_: *mut leanh::LeanObject,
    mut v_inst_4692_: *mut leanh::LeanObject,
    mut v_m_u2081_4693_: *mut leanh::LeanObject,
    mut v_m_u2082_4694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4695_: u8 = 0;
    let mut v_r_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4695_ = l_Std_DHashMap_Raw_beq___redArg(
        v_inst_4690_,
        v_inst_4691_,
        v_inst_4692_,
        v_m_u2081_4693_,
        v_m_u2082_4694_,
    );
    v_r_4696_ = leanh::lean_box((v_res_4695_) as usize);
    return v_r_4696_;
}
pub unsafe fn l_Std_DHashMap_Raw_beq(
    mut v_00_u03b1_4697_: *mut leanh::LeanObject,
    mut v_00_u03b2_4698_: *mut leanh::LeanObject,
    mut v_inst_4699_: *mut leanh::LeanObject,
    mut v_inst_4700_: *mut leanh::LeanObject,
    mut v_inst_4701_: *mut leanh::LeanObject,
    mut v_inst_4702_: *mut leanh::LeanObject,
    mut v_m_u2081_4703_: *mut leanh::LeanObject,
    mut v_m_u2082_4704_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_4706_: *mut leanh::LeanObject,
    mut v_00_u03b2_4707_: *mut leanh::LeanObject,
    mut v_inst_4708_: *mut leanh::LeanObject,
    mut v_inst_4709_: *mut leanh::LeanObject,
    mut v_inst_4710_: *mut leanh::LeanObject,
    mut v_inst_4711_: *mut leanh::LeanObject,
    mut v_m_u2081_4712_: *mut leanh::LeanObject,
    mut v_m_u2082_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4714_: u8 = 0;
    let mut v_r_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    v_r_4715_ = leanh::lean_box((v_res_4714_) as usize);
    return v_r_4715_;
}
pub unsafe fn l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(
    mut v_inst_4716_: *mut leanh::LeanObject,
    mut v_inst_4717_: *mut leanh::LeanObject,
    mut v_inst_4718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4719_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_4719_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4719_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4719_, 2, v_inst_4716_);
    leanh::lean_closure_set(v___x_4719_, 3, v_inst_4717_);
    leanh::lean_closure_set(v___x_4719_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4719_, 5, v_inst_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(
    mut v_00_u03b1_4720_: *mut leanh::LeanObject,
    mut v_00_u03b2_4721_: *mut leanh::LeanObject,
    mut v_inst_4722_: *mut leanh::LeanObject,
    mut v_inst_4723_: *mut leanh::LeanObject,
    mut v_inst_4724_: *mut leanh::LeanObject,
    mut v_inst_4725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4726_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_beq___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_4726_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4726_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4726_, 2, v_inst_4722_);
    leanh::lean_closure_set(v___x_4726_, 3, v_inst_4723_);
    leanh::lean_closure_set(v___x_4726_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4726_, 5, v_inst_4725_);
    return v___x_4726_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_beq___redArg(
    mut v_inst_4727_: *mut leanh::LeanObject,
    mut v_inst_4728_: *mut leanh::LeanObject,
    mut v_inst_4729_: *mut leanh::LeanObject,
    mut v_m_u2081_4730_: *mut leanh::LeanObject,
    mut v_m_u2082_4731_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: u8 = 0;
    v_buckets_4732_ = leanh::lean_ctor_get(v_m_u2081_4730_, 1);
    v___x_4733_ = leanh::lean_unsigned_to_nat(0);
    v___x_4734_ = lean_array_get_size(v_buckets_4732_);
    v___x_4735_ = lean_nat_dec_lt(v___x_4733_, v___x_4734_);
    if v___x_4735_ == 0 {
        leanh::lean_dec_ref(v_m_u2082_4731_);
        leanh::lean_dec_ref(v_m_u2081_4730_);
        leanh::lean_dec_ref(v_inst_4729_);
        leanh::lean_dec_ref(v_inst_4728_);
        leanh::lean_dec_ref(v_inst_4727_);
        return v___x_4735_;
    } else {
        let mut v_buckets_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4738_: u8 = 0;
        v_buckets_4736_ = leanh::lean_ctor_get(v_m_u2082_4731_, 1);
        v___x_4737_ = lean_array_get_size(v_buckets_4736_);
        v___x_4738_ = lean_nat_dec_lt(v___x_4733_, v___x_4737_);
        if v___x_4738_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4731_);
            leanh::lean_dec_ref(v_m_u2081_4730_);
            leanh::lean_dec_ref(v_inst_4729_);
            leanh::lean_dec_ref(v_inst_4728_);
            leanh::lean_dec_ref(v_inst_4727_);
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
    mut v_inst_4740_: *mut leanh::LeanObject,
    mut v_inst_4741_: *mut leanh::LeanObject,
    mut v_inst_4742_: *mut leanh::LeanObject,
    mut v_m_u2081_4743_: *mut leanh::LeanObject,
    mut v_m_u2082_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4745_: u8 = 0;
    let mut v_r_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4745_ = l_Std_DHashMap_Raw_Const_beq___redArg(
        v_inst_4740_,
        v_inst_4741_,
        v_inst_4742_,
        v_m_u2081_4743_,
        v_m_u2082_4744_,
    );
    v_r_4746_ = leanh::lean_box((v_res_4745_) as usize);
    return v_r_4746_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_beq(
    mut v_00_u03b1_4747_: *mut leanh::LeanObject,
    mut v_00_u03b2_4748_: *mut leanh::LeanObject,
    mut v_inst_4749_: *mut leanh::LeanObject,
    mut v_inst_4750_: *mut leanh::LeanObject,
    mut v_inst_4751_: *mut leanh::LeanObject,
    mut v_m_u2081_4752_: *mut leanh::LeanObject,
    mut v_m_u2082_4753_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_4755_: *mut leanh::LeanObject,
    mut v_00_u03b2_4756_: *mut leanh::LeanObject,
    mut v_inst_4757_: *mut leanh::LeanObject,
    mut v_inst_4758_: *mut leanh::LeanObject,
    mut v_inst_4759_: *mut leanh::LeanObject,
    mut v_m_u2081_4760_: *mut leanh::LeanObject,
    mut v_m_u2082_4761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4762_: u8 = 0;
    let mut v_r_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4762_ = l_Std_DHashMap_Raw_Const_beq(
        v_00_u03b1_4755_,
        v_00_u03b2_4756_,
        v_inst_4757_,
        v_inst_4758_,
        v_inst_4759_,
        v_m_u2081_4760_,
        v_m_u2082_4761_,
    );
    v_r_4763_ = leanh::lean_box((v_res_4762_) as usize);
    return v_r_4763_;
}
pub unsafe fn l_Std_DHashMap_Raw_diff___redArg___lam__0(
    mut v_inst_4764_: *mut leanh::LeanObject,
    mut v_inst_4765_: *mut leanh::LeanObject,
    mut v_m_u2082_4766_: *mut leanh::LeanObject,
    mut v___x_4767_: u8,
    mut v_k_4768_: *mut leanh::LeanObject,
    mut v_x_4769_: *mut leanh::LeanObject,
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
    mut v_inst_4772_: *mut leanh::LeanObject,
    mut v_inst_4773_: *mut leanh::LeanObject,
    mut v_m_u2082_4774_: *mut leanh::LeanObject,
    mut v___x_4775_: *mut leanh::LeanObject,
    mut v_k_4776_: *mut leanh::LeanObject,
    mut v_x_4777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_92__boxed_4778_: u8 = 0;
    let mut v_res_4779_: u8 = 0;
    let mut v_r_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_92__boxed_4778_ = (leanh::lean_unbox(v___x_4775_) as u8);
    v_res_4779_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(
        v_inst_4772_,
        v_inst_4773_,
        v_m_u2082_4774_,
        v___x_92__boxed_4778_,
        v_k_4776_,
        v_x_4777_,
    );
    leanh::lean_dec(v_x_4777_);
    leanh::lean_dec_ref(v_m_u2082_4774_);
    v_r_4780_ = leanh::lean_box((v_res_4779_) as usize);
    return v_r_4780_;
}
pub unsafe fn l_Std_DHashMap_Raw_diff___redArg(
    mut v_inst_4781_: *mut leanh::LeanObject,
    mut v_inst_4782_: *mut leanh::LeanObject,
    mut v_m_u2081_4783_: *mut leanh::LeanObject,
    mut v_m_u2082_4784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: u8 = 0;
    v_size_4785_ = leanh::lean_ctor_get(v_m_u2081_4783_, 0);
    v_buckets_4786_ = leanh::lean_ctor_get(v_m_u2081_4783_, 1);
    v___x_4787_ = leanh::lean_unsigned_to_nat(0);
    v___x_4788_ = lean_array_get_size(v_buckets_4786_);
    v___x_4789_ = lean_nat_dec_lt(v___x_4787_, v___x_4788_);
    if v___x_4789_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_4783_);
        leanh::lean_dec_ref(v_inst_4782_);
        leanh::lean_dec_ref(v_inst_4781_);
        return v_m_u2082_4784_;
    } else {
        let mut v_size_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4793_: u8 = 0;
        v_size_4790_ = leanh::lean_ctor_get(v_m_u2082_4784_, 0);
        v_buckets_4791_ = leanh::lean_ctor_get(v_m_u2082_4784_, 1);
        v___x_4792_ = lean_array_get_size(v_buckets_4791_);
        v___x_4793_ = lean_nat_dec_lt(v___x_4787_, v___x_4792_);
        if v___x_4793_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4784_);
            leanh::lean_dec_ref(v_inst_4782_);
            leanh::lean_dec_ref(v_inst_4781_);
            return v_m_u2081_4783_;
        } else {
            let mut v___x_4794_: u8 = 0;
            v___x_4794_ = lean_nat_dec_le(v_size_4785_, v_size_4790_);
            if v___x_4794_ == 0 {
                let mut v___f_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4797_ = leanh::lean_box((v___x_4794_) as usize);
                v___f_4798_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_4798_, 0, v_inst_4781_);
                leanh::lean_closure_set(v___f_4798_, 1, v_inst_4782_);
                leanh::lean_closure_set(v___f_4798_, 2, v_m_u2082_4784_);
                leanh::lean_closure_set(v___f_4798_, 3, v___x_4797_);
                v___x_4799_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4798_, v_m_u2081_4783_);
                return v___x_4799_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_diff(
    mut v_00_u03b1_4800_: *mut leanh::LeanObject,
    mut v_00_u03b2_4801_: *mut leanh::LeanObject,
    mut v_inst_4802_: *mut leanh::LeanObject,
    mut v_inst_4803_: *mut leanh::LeanObject,
    mut v_m_u2081_4804_: *mut leanh::LeanObject,
    mut v_m_u2082_4805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    v_size_4806_ = leanh::lean_ctor_get(v_m_u2081_4804_, 0);
    v_buckets_4807_ = leanh::lean_ctor_get(v_m_u2081_4804_, 1);
    v___x_4808_ = leanh::lean_unsigned_to_nat(0);
    v___x_4809_ = lean_array_get_size(v_buckets_4807_);
    v___x_4810_ = lean_nat_dec_lt(v___x_4808_, v___x_4809_);
    if v___x_4810_ == 0 {
        leanh::lean_dec_ref(v_m_u2081_4804_);
        leanh::lean_dec_ref(v_inst_4803_);
        leanh::lean_dec_ref(v_inst_4802_);
        return v_m_u2082_4805_;
    } else {
        let mut v_size_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buckets_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4814_: u8 = 0;
        v_size_4811_ = leanh::lean_ctor_get(v_m_u2082_4805_, 0);
        v_buckets_4812_ = leanh::lean_ctor_get(v_m_u2082_4805_, 1);
        v___x_4813_ = lean_array_get_size(v_buckets_4812_);
        v___x_4814_ = lean_nat_dec_lt(v___x_4808_, v___x_4813_);
        if v___x_4814_ == 0 {
            leanh::lean_dec_ref(v_m_u2082_4805_);
            leanh::lean_dec_ref(v_inst_4803_);
            leanh::lean_dec_ref(v_inst_4802_);
            return v_m_u2081_4804_;
        } else {
            let mut v___x_4815_: u8 = 0;
            v___x_4815_ = lean_nat_dec_le(v_size_4806_, v_size_4811_);
            if v___x_4815_ == 0 {
                let mut v___f_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4818_ = leanh::lean_box((v___x_4815_) as usize);
                v___f_4819_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_4819_, 0, v_inst_4802_);
                leanh::lean_closure_set(v___f_4819_, 1, v_inst_4803_);
                leanh::lean_closure_set(v___f_4819_, 2, v_m_u2082_4805_);
                leanh::lean_closure_set(v___f_4819_, 3, v___x_4818_);
                v___x_4820_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4819_, v_m_u2081_4804_);
                return v___x_4820_;
            }
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(
    mut v_inst_4821_: *mut leanh::LeanObject,
    mut v_inst_4822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ =
        leanh::lean_alloc_closure(l_Std_DHashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4823_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4823_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4823_, 2, v_inst_4821_);
    leanh::lean_closure_set(v___x_4823_, 3, v_inst_4822_);
    return v___x_4823_;
}
pub unsafe fn l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(
    mut v_00_u03b1_4824_: *mut leanh::LeanObject,
    mut v_00_u03b2_4825_: *mut leanh::LeanObject,
    mut v_inst_4826_: *mut leanh::LeanObject,
    mut v_inst_4827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ =
        leanh::lean_alloc_closure(l_Std_DHashMap_Raw_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4828_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4828_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4828_, 2, v_inst_4826_);
    leanh::lean_closure_set(v___x_4828_, 3, v_inst_4827_);
    return v___x_4828_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg___lam__0(
    mut v_a_4829_: *mut leanh::LeanObject,
    mut v_b_4830_: *mut leanh::LeanObject,
    mut v_d_4831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4832_, 0, v_b_4830_);
    leanh::lean_ctor_set(v___x_4832_, 1, v_d_4831_);
    return v___x_4832_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(
    mut v_a_4833_: *mut leanh::LeanObject,
    mut v_b_4834_: *mut leanh::LeanObject,
    mut v_d_4835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4836_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_a_4833_, v_b_4834_, v_d_4835_);
    leanh::lean_dec(v_a_4833_);
    return v_res_4836_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg___lam__1(
    mut v___x_4837_: *mut leanh::LeanObject,
    mut v___f_4838_: *mut leanh::LeanObject,
    mut v_l_4839_: *mut leanh::LeanObject,
    mut v_acc_4840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4841_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_4837_,
        v___f_4838_,
        v_acc_4840_,
        v_l_4839_,
    );
    return v___x_4841_;
}
pub unsafe fn l_Std_DHashMap_Raw_values___redArg(
    mut v_m_4846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    v___x_4847_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4848_ = leanh::lean_ctor_get(v_m_4846_, 1);
    leanh::lean_inc_ref(v_buckets_4848_);
    leanh::lean_dec_ref(v_m_4846_);
    v___x_4849_ = leanh::lean_box(0);
    v___x_4850_ = lean_array_get_size(v_buckets_4848_);
    v___x_4851_ = leanh::lean_unsigned_to_nat(0);
    v___x_4852_ = lean_nat_dec_lt(v___x_4851_, v___x_4850_);
    if v___x_4852_ == 0 {
        leanh::lean_dec_ref(v_buckets_4848_);
        return v___x_4849_;
    } else {
        let mut v___f_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4854_: usize = 0;
        let mut v___x_4855_: usize = 0;
        let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4853_ = l_Std_DHashMap_Raw_values___redArg___closed__1;
        v___x_4854_ = lean_usize_of_nat(v___x_4850_);
        v___x_4855_ = 0usize;
        v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_4857_: *mut leanh::LeanObject,
    mut v_00_u03b2_4858_: *mut leanh::LeanObject,
    mut v_m_4859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: u8 = 0;
    v___x_4860_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_4861_ = leanh::lean_ctor_get(v_m_4859_, 1);
    leanh::lean_inc_ref(v_buckets_4861_);
    leanh::lean_dec_ref(v_m_4859_);
    v___x_4862_ = leanh::lean_box(0);
    v___x_4863_ = lean_array_get_size(v_buckets_4861_);
    v___x_4864_ = leanh::lean_unsigned_to_nat(0);
    v___x_4865_ = lean_nat_dec_lt(v___x_4864_, v___x_4863_);
    if v___x_4865_ == 0 {
        leanh::lean_dec_ref(v_buckets_4861_);
        return v___x_4862_;
    } else {
        let mut v___f_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4867_: usize = 0;
        let mut v___x_4868_: usize = 0;
        let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4866_ = l_Std_DHashMap_Raw_values___redArg___closed__1;
        v___x_4867_ = lean_usize_of_nat(v___x_4863_);
        v___x_4868_ = 0usize;
        v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_x1_4870_: *mut leanh::LeanObject,
    mut v_x2_4871_: *mut leanh::LeanObject,
    mut v_x3_4872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4873_ = lean_array_push(v_x1_4870_, v_x3_4872_);
    return v___x_4873_;
}
pub unsafe fn l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(
    mut v_x1_4874_: *mut leanh::LeanObject,
    mut v_x2_4875_: *mut leanh::LeanObject,
    mut v_x3_4876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4877_ =
        l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_4874_, v_x2_4875_, v_x3_4876_);
    leanh::lean_dec(v_x2_4875_);
    return v_res_4877_;
}
pub unsafe fn l_Std_DHashMap_Raw_valuesArray___redArg(
    mut v_m_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: u8 = 0;
    v_size_4883_ = leanh::lean_ctor_get(v_m_4882_, 0);
    leanh::lean_inc(v_size_4883_);
    v_buckets_4884_ = leanh::lean_ctor_get(v_m_4882_, 1);
    leanh::lean_inc_ref(v_buckets_4884_);
    leanh::lean_dec_ref(v_m_4882_);
    v___x_4885_ = lean_mk_empty_array_with_capacity(v_size_4883_);
    leanh::lean_dec(v_size_4883_);
    v___x_4886_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4887_ = leanh::lean_unsigned_to_nat(0);
    v___x_4888_ = lean_array_get_size(v_buckets_4884_);
    v___x_4889_ = lean_nat_dec_lt(v___x_4887_, v___x_4888_);
    if v___x_4889_ == 0 {
        leanh::lean_dec_ref(v_buckets_4884_);
        return v___x_4885_;
    } else {
        let mut v___f_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4891_: u8 = 0;
        v___f_4890_ = l_Std_DHashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4891_ = lean_nat_dec_le(v___x_4888_, v___x_4888_);
        if v___x_4891_ == 0 {
            if v___x_4889_ == 0 {
                leanh::lean_dec_ref(v_buckets_4884_);
                return v___x_4885_;
            } else {
                let mut v___x_4892_: usize = 0;
                let mut v___x_4893_: usize = 0;
                let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4892_ = 0usize;
                v___x_4893_ = lean_usize_of_nat(v___x_4888_);
                v___x_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4895_ = 0usize;
            v___x_4896_ = lean_usize_of_nat(v___x_4888_);
            v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_4898_: *mut leanh::LeanObject,
    mut v_00_u03b2_4899_: *mut leanh::LeanObject,
    mut v_m_4900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: u8 = 0;
    v_size_4901_ = leanh::lean_ctor_get(v_m_4900_, 0);
    leanh::lean_inc(v_size_4901_);
    v_buckets_4902_ = leanh::lean_ctor_get(v_m_4900_, 1);
    leanh::lean_inc_ref(v_buckets_4902_);
    leanh::lean_dec_ref(v_m_4900_);
    v___x_4903_ = lean_mk_empty_array_with_capacity(v_size_4901_);
    leanh::lean_dec(v_size_4901_);
    v___x_4904_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v___x_4905_ = leanh::lean_unsigned_to_nat(0);
    v___x_4906_ = lean_array_get_size(v_buckets_4902_);
    v___x_4907_ = lean_nat_dec_lt(v___x_4905_, v___x_4906_);
    if v___x_4907_ == 0 {
        leanh::lean_dec_ref(v_buckets_4902_);
        return v___x_4903_;
    } else {
        let mut v___f_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4909_: u8 = 0;
        v___f_4908_ = l_Std_DHashMap_Raw_valuesArray___redArg___closed__1;
        v___x_4909_ = lean_nat_dec_le(v___x_4906_, v___x_4906_);
        if v___x_4909_ == 0 {
            if v___x_4907_ == 0 {
                leanh::lean_dec_ref(v_buckets_4902_);
                return v___x_4903_;
            } else {
                let mut v___x_4910_: usize = 0;
                let mut v___x_4911_: usize = 0;
                let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4910_ = 0usize;
                v___x_4911_ = lean_usize_of_nat(v___x_4906_);
                v___x_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4913_ = 0usize;
            v___x_4914_ = lean_usize_of_nat(v___x_4906_);
            v___x_4915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_inst_4916_: *mut leanh::LeanObject,
    mut v_inst_4917_: *mut leanh::LeanObject,
    mut v_inst_4918_: *mut leanh::LeanObject,
    mut v_m_4919_: *mut leanh::LeanObject,
    mut v_l_4920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: u8 = 0;
    v_buckets_4921_ = leanh::lean_ctor_get(v_m_4919_, 1);
    v___x_4922_ = leanh::lean_unsigned_to_nat(0);
    v___x_4923_ = lean_array_get_size(v_buckets_4921_);
    v___x_4924_ = lean_nat_dec_lt(v___x_4922_, v___x_4923_);
    if v___x_4924_ == 0 {
        leanh::lean_dec(v_l_4920_);
        leanh::lean_dec(v_inst_4918_);
        leanh::lean_dec_ref(v_inst_4917_);
        leanh::lean_dec_ref(v_inst_4916_);
        return v_m_4919_;
    } else {
        let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4926_: *mut leanh::LeanObject,
    mut v_00_u03b2_4927_: *mut leanh::LeanObject,
    mut v_inst_4928_: *mut leanh::LeanObject,
    mut v_inst_4929_: *mut leanh::LeanObject,
    mut v_00_u03c1_4930_: *mut leanh::LeanObject,
    mut v_inst_4931_: *mut leanh::LeanObject,
    mut v_m_4932_: *mut leanh::LeanObject,
    mut v_l_4933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u8 = 0;
    v_buckets_4934_ = leanh::lean_ctor_get(v_m_4932_, 1);
    v___x_4935_ = leanh::lean_unsigned_to_nat(0);
    v___x_4936_ = lean_array_get_size(v_buckets_4934_);
    v___x_4937_ = lean_nat_dec_lt(v___x_4935_, v___x_4936_);
    if v___x_4937_ == 0 {
        leanh::lean_dec(v_l_4933_);
        leanh::lean_dec(v_inst_4931_);
        leanh::lean_dec_ref(v_inst_4929_);
        leanh::lean_dec_ref(v_inst_4928_);
        return v_m_4932_;
    } else {
        let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4939_: *mut leanh::LeanObject,
    mut v_inst_4940_: *mut leanh::LeanObject,
    mut v_inst_4941_: *mut leanh::LeanObject,
    mut v_m_4942_: *mut leanh::LeanObject,
    mut v_l_4943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    v_buckets_4944_ = leanh::lean_ctor_get(v_m_4942_, 1);
    v___x_4945_ = leanh::lean_unsigned_to_nat(0);
    v___x_4946_ = lean_array_get_size(v_buckets_4944_);
    v___x_4947_ = lean_nat_dec_lt(v___x_4945_, v___x_4946_);
    if v___x_4947_ == 0 {
        leanh::lean_dec(v_l_4943_);
        leanh::lean_dec(v_inst_4941_);
        leanh::lean_dec_ref(v_inst_4940_);
        leanh::lean_dec_ref(v_inst_4939_);
        return v_m_4942_;
    } else {
        let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4949_: *mut leanh::LeanObject,
    mut v_00_u03b2_4950_: *mut leanh::LeanObject,
    mut v_inst_4951_: *mut leanh::LeanObject,
    mut v_inst_4952_: *mut leanh::LeanObject,
    mut v_00_u03c1_4953_: *mut leanh::LeanObject,
    mut v_inst_4954_: *mut leanh::LeanObject,
    mut v_m_4955_: *mut leanh::LeanObject,
    mut v_l_4956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: u8 = 0;
    v_buckets_4957_ = leanh::lean_ctor_get(v_m_4955_, 1);
    v___x_4958_ = leanh::lean_unsigned_to_nat(0);
    v___x_4959_ = lean_array_get_size(v_buckets_4957_);
    v___x_4960_ = lean_nat_dec_lt(v___x_4958_, v___x_4959_);
    if v___x_4960_ == 0 {
        leanh::lean_dec(v_l_4956_);
        leanh::lean_dec(v_inst_4954_);
        leanh::lean_dec_ref(v_inst_4952_);
        leanh::lean_dec_ref(v_inst_4951_);
        return v_m_4955_;
    } else {
        let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4962_: *mut leanh::LeanObject,
    mut v_inst_4963_: *mut leanh::LeanObject,
    mut v_inst_4964_: *mut leanh::LeanObject,
    mut v_m_4965_: *mut leanh::LeanObject,
    mut v_l_4966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: u8 = 0;
    v_buckets_4967_ = leanh::lean_ctor_get(v_m_4965_, 1);
    v___x_4968_ = leanh::lean_unsigned_to_nat(0);
    v___x_4969_ = lean_array_get_size(v_buckets_4967_);
    v___x_4970_ = lean_nat_dec_lt(v___x_4968_, v___x_4969_);
    if v___x_4970_ == 0 {
        leanh::lean_dec(v_l_4966_);
        leanh::lean_dec(v_inst_4964_);
        leanh::lean_dec_ref(v_inst_4963_);
        leanh::lean_dec_ref(v_inst_4962_);
        return v_m_4965_;
    } else {
        let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4972_: *mut leanh::LeanObject,
    mut v_00_u03b2_4973_: *mut leanh::LeanObject,
    mut v_inst_4974_: *mut leanh::LeanObject,
    mut v_inst_4975_: *mut leanh::LeanObject,
    mut v_00_u03c1_4976_: *mut leanh::LeanObject,
    mut v_inst_4977_: *mut leanh::LeanObject,
    mut v_m_4978_: *mut leanh::LeanObject,
    mut v_l_4979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: u8 = 0;
    v_buckets_4980_ = leanh::lean_ctor_get(v_m_4978_, 1);
    v___x_4981_ = leanh::lean_unsigned_to_nat(0);
    v___x_4982_ = lean_array_get_size(v_buckets_4980_);
    v___x_4983_ = lean_nat_dec_lt(v___x_4981_, v___x_4982_);
    if v___x_4983_ == 0 {
        leanh::lean_dec(v_l_4979_);
        leanh::lean_dec(v_inst_4977_);
        leanh::lean_dec_ref(v_inst_4975_);
        leanh::lean_dec_ref(v_inst_4974_);
        return v_m_4978_;
    } else {
        let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4985_: *mut leanh::LeanObject,
    mut v_inst_4986_: *mut leanh::LeanObject,
    mut v_inst_4987_: *mut leanh::LeanObject,
    mut v_m_4988_: *mut leanh::LeanObject,
    mut v_l_4989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: u8 = 0;
    v_buckets_4990_ = leanh::lean_ctor_get(v_m_4988_, 1);
    v___x_4991_ = leanh::lean_unsigned_to_nat(0);
    v___x_4992_ = lean_array_get_size(v_buckets_4990_);
    v___x_4993_ = lean_nat_dec_lt(v___x_4991_, v___x_4992_);
    if v___x_4993_ == 0 {
        leanh::lean_dec(v_l_4989_);
        leanh::lean_dec(v_inst_4987_);
        leanh::lean_dec_ref(v_inst_4986_);
        leanh::lean_dec_ref(v_inst_4985_);
        return v_m_4988_;
    } else {
        let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4995_: *mut leanh::LeanObject,
    mut v_inst_4996_: *mut leanh::LeanObject,
    mut v_inst_4997_: *mut leanh::LeanObject,
    mut v_00_u03c1_4998_: *mut leanh::LeanObject,
    mut v_inst_4999_: *mut leanh::LeanObject,
    mut v_m_5000_: *mut leanh::LeanObject,
    mut v_l_5001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: u8 = 0;
    v_buckets_5002_ = leanh::lean_ctor_get(v_m_5000_, 1);
    v___x_5003_ = leanh::lean_unsigned_to_nat(0);
    v___x_5004_ = lean_array_get_size(v_buckets_5002_);
    v___x_5005_ = lean_nat_dec_lt(v___x_5003_, v___x_5004_);
    if v___x_5005_ == 0 {
        leanh::lean_dec(v_l_5001_);
        leanh::lean_dec(v_inst_4999_);
        leanh::lean_dec_ref(v_inst_4997_);
        leanh::lean_dec_ref(v_inst_4996_);
        return v_m_5000_;
    } else {
        let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_5011_: *mut leanh::LeanObject,
    mut v_inst_5012_: *mut leanh::LeanObject,
    mut v_l_5013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: u8 = 0;
    v___x_5014_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5015_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5015_ == 0 {
        leanh::lean_dec_ref(v_l_5013_);
        leanh::lean_dec_ref(v_inst_5012_);
        leanh::lean_dec_ref(v_inst_5011_);
        return v___x_5014_;
    } else {
        let mut v___f_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5018_: *mut leanh::LeanObject,
    mut v_inst_5019_: *mut leanh::LeanObject,
    mut v_inst_5020_: *mut leanh::LeanObject,
    mut v_l_5021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: u8 = 0;
    v___x_5022_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5023_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5023_ == 0 {
        leanh::lean_dec_ref(v_l_5021_);
        leanh::lean_dec_ref(v_inst_5020_);
        leanh::lean_dec_ref(v_inst_5019_);
        return v___x_5022_;
    } else {
        let mut v___f_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_5026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5027_ = leanh::lean_ctor_get(v_m_5026_, 1);
    v___x_5028_ = lean_array_get_size(v_buckets_5027_);
    return v___x_5028_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(
    mut v_m_5029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5030_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_5029_);
    leanh::lean_dec_ref(v_m_5029_);
    return v_res_5030_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_numBuckets(
    mut v_00_u03b1_5031_: *mut leanh::LeanObject,
    mut v_00_u03b2_5032_: *mut leanh::LeanObject,
    mut v_m_5033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5034_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_5033_);
    return v___x_5034_;
}
pub unsafe fn l_Std_DHashMap_Raw_Internal_numBuckets___boxed(
    mut v_00_u03b1_5035_: *mut leanh::LeanObject,
    mut v_00_u03b2_5036_: *mut leanh::LeanObject,
    mut v_m_5037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5038_ =
        l_Std_DHashMap_Raw_Internal_numBuckets(v_00_u03b1_5035_, v_00_u03b2_5036_, v_m_5037_);
    leanh::lean_dec_ref(v_m_5037_);
    return v_res_5038_;
}
pub unsafe fn l_Std_DHashMap_Raw_toList___redArg___lam__0(
    mut v_a_5039_: *mut leanh::LeanObject,
    mut v_b_5040_: *mut leanh::LeanObject,
    mut v_d_5041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5042_, 0, v_a_5039_);
    leanh::lean_ctor_set(v___x_5042_, 1, v_b_5040_);
    v___x_5043_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5043_, 0, v___x_5042_);
    leanh::lean_ctor_set(v___x_5043_, 1, v_d_5041_);
    return v___x_5043_;
}
pub unsafe fn l_Std_DHashMap_Raw_toList___redArg___lam__1(
    mut v___x_5044_: *mut leanh::LeanObject,
    mut v___f_5045_: *mut leanh::LeanObject,
    mut v_l_5046_: *mut leanh::LeanObject,
    mut v_acc_5047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5048_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_5044_,
        v___f_5045_,
        v_acc_5047_,
        v_l_5046_,
    );
    return v___x_5048_;
}
pub unsafe fn l_Std_DHashMap_Raw_toList___redArg(
    mut v_m_5053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: u8 = 0;
    v___x_5054_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5055_ = leanh::lean_ctor_get(v_m_5053_, 1);
    leanh::lean_inc_ref(v_buckets_5055_);
    leanh::lean_dec_ref(v_m_5053_);
    v___x_5056_ = leanh::lean_box(0);
    v___x_5057_ = lean_array_get_size(v_buckets_5055_);
    v___x_5058_ = leanh::lean_unsigned_to_nat(0);
    v___x_5059_ = lean_nat_dec_lt(v___x_5058_, v___x_5057_);
    if v___x_5059_ == 0 {
        leanh::lean_dec_ref(v_buckets_5055_);
        return v___x_5056_;
    } else {
        let mut v___f_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5061_: usize = 0;
        let mut v___x_5062_: usize = 0;
        let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5060_ = l_Std_DHashMap_Raw_toList___redArg___closed__1;
        v___x_5061_ = lean_usize_of_nat(v___x_5057_);
        v___x_5062_ = 0usize;
        v___x_5063_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_5064_: *mut leanh::LeanObject,
    mut v_00_u03b2_5065_: *mut leanh::LeanObject,
    mut v_m_5066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: u8 = 0;
    v___x_5067_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5068_ = leanh::lean_ctor_get(v_m_5066_, 1);
    leanh::lean_inc_ref(v_buckets_5068_);
    leanh::lean_dec_ref(v_m_5066_);
    v___x_5069_ = leanh::lean_box(0);
    v___x_5070_ = lean_array_get_size(v_buckets_5068_);
    v___x_5071_ = leanh::lean_unsigned_to_nat(0);
    v___x_5072_ = lean_nat_dec_lt(v___x_5071_, v___x_5070_);
    if v___x_5072_ == 0 {
        leanh::lean_dec_ref(v_buckets_5068_);
        return v___x_5069_;
    } else {
        let mut v___f_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5074_: usize = 0;
        let mut v___x_5075_: usize = 0;
        let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5073_ = l_Std_DHashMap_Raw_toList___redArg___closed__1;
        v___x_5074_ = lean_usize_of_nat(v___x_5070_);
        v___x_5075_ = 0usize;
        v___x_5076_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_a_5077_: *mut leanh::LeanObject,
    mut v_b_5078_: *mut leanh::LeanObject,
    mut v_d_5079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5080_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5080_, 0, v_a_5077_);
    leanh::lean_ctor_set(v___x_5080_, 1, v_b_5078_);
    v___x_5081_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5081_, 0, v___x_5080_);
    leanh::lean_ctor_set(v___x_5081_, 1, v_d_5079_);
    return v___x_5081_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toList___redArg___lam__1(
    mut v___x_5082_: *mut leanh::LeanObject,
    mut v___f_5083_: *mut leanh::LeanObject,
    mut v_l_5084_: *mut leanh::LeanObject,
    mut v_acc_5085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_5082_,
        v___f_5083_,
        v_acc_5085_,
        v_l_5084_,
    );
    return v___x_5086_;
}
pub unsafe fn l_Std_DHashMap_Raw_Const_toList___redArg(
    mut v_m_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: u8 = 0;
    v___x_5092_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5093_ = leanh::lean_ctor_get(v_m_5091_, 1);
    leanh::lean_inc_ref(v_buckets_5093_);
    leanh::lean_dec_ref(v_m_5091_);
    v___x_5094_ = leanh::lean_box(0);
    v___x_5095_ = lean_array_get_size(v_buckets_5093_);
    v___x_5096_ = leanh::lean_unsigned_to_nat(0);
    v___x_5097_ = lean_nat_dec_lt(v___x_5096_, v___x_5095_);
    if v___x_5097_ == 0 {
        leanh::lean_dec_ref(v_buckets_5093_);
        return v___x_5094_;
    } else {
        let mut v___f_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5099_: usize = 0;
        let mut v___x_5100_: usize = 0;
        let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5098_ = l_Std_DHashMap_Raw_Const_toList___redArg___closed__1;
        v___x_5099_ = lean_usize_of_nat(v___x_5095_);
        v___x_5100_ = 0usize;
        v___x_5101_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_5102_: *mut leanh::LeanObject,
    mut v_00_u03b2_5103_: *mut leanh::LeanObject,
    mut v_m_5104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    v___x_5105_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5106_ = leanh::lean_ctor_get(v_m_5104_, 1);
    leanh::lean_inc_ref(v_buckets_5106_);
    leanh::lean_dec_ref(v_m_5104_);
    v___x_5107_ = leanh::lean_box(0);
    v___x_5108_ = lean_array_get_size(v_buckets_5106_);
    v___x_5109_ = leanh::lean_unsigned_to_nat(0);
    v___x_5110_ = lean_nat_dec_lt(v___x_5109_, v___x_5108_);
    if v___x_5110_ == 0 {
        leanh::lean_dec_ref(v_buckets_5106_);
        return v___x_5107_;
    } else {
        let mut v___f_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5112_: usize = 0;
        let mut v___x_5113_: usize = 0;
        let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5111_ = l_Std_DHashMap_Raw_Const_toList___redArg___closed__1;
        v___x_5112_ = lean_usize_of_nat(v___x_5108_);
        v___x_5113_ = 0usize;
        v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v___x_5118_: *mut leanh::LeanObject,
    mut v___f_5119_: *mut leanh::LeanObject,
    mut v_m_5120_: *mut leanh::LeanObject,
    mut v_prec_5121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: u8 = 0;
    let mut v___f_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: usize = 0;
    let mut v___x_5141_: usize = 0;
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5143_: u8 = 0;
    let mut v_unused_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5122_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
                v_buckets_5123_ = leanh::lean_ctor_get(v_m_5120_, 1);
                v_isSharedCheck_5143_ = (!leanh::lean_is_exclusive(v_m_5120_)) as u8;
                if v_isSharedCheck_5143_ == 0 {
                    v_unused_5144_ = leanh::lean_ctor_get(v_m_5120_, 0);
                    leanh::lean_dec(v_unused_5144_);
                    v___x_5125_ = v_m_5120_;
                    v_isShared_5126_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_5123_);
                    leanh::lean_dec(v_m_5120_);
                    v___x_5125_ = leanh::lean_box(0);
                    v_isShared_5126_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5127_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2___closed__1;
                v___x_5135_ = leanh::lean_box(0);
                v___x_5136_ = lean_array_get_size(v_buckets_5123_);
                v___x_5137_ = leanh::lean_unsigned_to_nat(0);
                v___x_5138_ = lean_nat_dec_lt(v___x_5137_, v___x_5136_);
                if v___x_5138_ == 0 {
                    leanh::lean_dec_ref(v_buckets_5123_);
                    leanh::lean_dec_ref(v___f_5119_);
                    v___y_5129_ = v___x_5135_;
                    state = 2;
                    continue;
                } else {
                    v___f_5139_ = leanh::lean_alloc_closure(
                        l_Std_DHashMap_Raw_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_5139_, 0, v___x_5122_);
                    leanh::lean_closure_set(v___f_5139_, 1, v___f_5119_);
                    v___x_5140_ = lean_usize_of_nat(v___x_5136_);
                    v___x_5141_ = 0usize;
                    v___x_5142_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
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
                    leanh::lean_ctor_set_tag(v___x_5125_, 5);
                    leanh::lean_ctor_set(v___x_5125_, 1, v___x_5130_);
                    leanh::lean_ctor_set(v___x_5125_, 0, v___x_5127_);
                    v___x_5132_ = v___x_5125_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5134_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 0, v___x_5127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 1, v___x_5130_);
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
    mut v___x_5145_: *mut leanh::LeanObject,
    mut v___f_5146_: *mut leanh::LeanObject,
    mut v_m_5147_: *mut leanh::LeanObject,
    mut v_prec_5148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5149_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__2(
        v___x_5145_,
        v___f_5146_,
        v_m_5147_,
        v_prec_5148_,
    );
    leanh::lean_dec(v_prec_5148_);
    return v_res_5149_;
}
pub unsafe fn l_Std_DHashMap_Raw_instRepr___redArg(
    mut v_inst_5150_: *mut leanh::LeanObject,
    mut v_inst_5151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5152_ = l_Std_DHashMap_Raw_toList___redArg___closed__0;
    v___x_5153_ =
        leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_5153_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5153_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5153_, 2, v_inst_5150_);
    leanh::lean_closure_set(v___x_5153_, 3, v_inst_5151_);
    v___f_5154_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Raw_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_5154_, 0, v___x_5153_);
    leanh::lean_closure_set(v___f_5154_, 1, v___f_5152_);
    return v___f_5154_;
}
pub unsafe fn l_Std_DHashMap_Raw_instRepr(
    mut v_00_u03b1_5155_: *mut leanh::LeanObject,
    mut v_00_u03b2_5156_: *mut leanh::LeanObject,
    mut v_inst_5157_: *mut leanh::LeanObject,
    mut v_inst_5158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5159_ = l_Std_DHashMap_Raw_instRepr___redArg(v_inst_5157_, v_inst_5158_);
    return v___x_5159_;
}
pub unsafe fn l_Std_DHashMap_Raw_keys___redArg___lam__0(
    mut v_a_5160_: *mut leanh::LeanObject,
    mut v_b_5161_: *mut leanh::LeanObject,
    mut v_d_5162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5163_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5163_, 0, v_a_5160_);
    leanh::lean_ctor_set(v___x_5163_, 1, v_d_5162_);
    return v___x_5163_;
}
pub unsafe fn l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(
    mut v_a_5164_: *mut leanh::LeanObject,
    mut v_b_5165_: *mut leanh::LeanObject,
    mut v_d_5166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5167_ = l_Std_DHashMap_Raw_keys___redArg___lam__0(v_a_5164_, v_b_5165_, v_d_5166_);
    leanh::lean_dec(v_b_5165_);
    return v_res_5167_;
}
pub unsafe fn l_Std_DHashMap_Raw_keys___redArg(
    mut v_m_5172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: u8 = 0;
    v___x_5173_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5174_ = leanh::lean_ctor_get(v_m_5172_, 1);
    leanh::lean_inc_ref(v_buckets_5174_);
    leanh::lean_dec_ref(v_m_5172_);
    v___x_5175_ = leanh::lean_box(0);
    v___x_5176_ = lean_array_get_size(v_buckets_5174_);
    v___x_5177_ = leanh::lean_unsigned_to_nat(0);
    v___x_5178_ = lean_nat_dec_lt(v___x_5177_, v___x_5176_);
    if v___x_5178_ == 0 {
        leanh::lean_dec_ref(v_buckets_5174_);
        return v___x_5175_;
    } else {
        let mut v___f_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5180_: usize = 0;
        let mut v___x_5181_: usize = 0;
        let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5179_ = l_Std_DHashMap_Raw_keys___redArg___closed__1;
        v___x_5180_ = lean_usize_of_nat(v___x_5176_);
        v___x_5181_ = 0usize;
        v___x_5182_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_5183_: *mut leanh::LeanObject,
    mut v_00_u03b2_5184_: *mut leanh::LeanObject,
    mut v_m_5185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: u8 = 0;
    v___x_5186_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9;
    v_buckets_5187_ = leanh::lean_ctor_get(v_m_5185_, 1);
    leanh::lean_inc_ref(v_buckets_5187_);
    leanh::lean_dec_ref(v_m_5185_);
    v___x_5188_ = leanh::lean_box(0);
    v___x_5189_ = lean_array_get_size(v_buckets_5187_);
    v___x_5190_ = leanh::lean_unsigned_to_nat(0);
    v___x_5191_ = lean_nat_dec_lt(v___x_5190_, v___x_5189_);
    if v___x_5191_ == 0 {
        leanh::lean_dec_ref(v_buckets_5187_);
        return v___x_5188_;
    } else {
        let mut v___f_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5193_: usize = 0;
        let mut v___x_5194_: usize = 0;
        let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5192_ = l_Std_DHashMap_Raw_keys___redArg___closed__1;
        v___x_5193_ = lean_usize_of_nat(v___x_5189_);
        v___x_5194_ = 0usize;
        v___x_5195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_inst_5200_: *mut leanh::LeanObject,
    mut v_inst_5201_: *mut leanh::LeanObject,
    mut v_l_5202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: u8 = 0;
    v___x_5203_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5204_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5204_ == 0 {
        leanh::lean_dec(v_l_5202_);
        leanh::lean_dec_ref(v_inst_5201_);
        leanh::lean_dec_ref(v_inst_5200_);
        return v___x_5203_;
    } else {
        let mut v___f_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5207_: *mut leanh::LeanObject,
    mut v_00_u03b2_5208_: *mut leanh::LeanObject,
    mut v_inst_5209_: *mut leanh::LeanObject,
    mut v_inst_5210_: *mut leanh::LeanObject,
    mut v_l_5211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    v___x_5212_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5213_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5213_ == 0 {
        leanh::lean_dec(v_l_5211_);
        leanh::lean_dec_ref(v_inst_5210_);
        leanh::lean_dec_ref(v_inst_5209_);
        return v___x_5212_;
    } else {
        let mut v___f_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_5216_: *mut leanh::LeanObject,
    mut v_inst_5217_: *mut leanh::LeanObject,
    mut v_l_5218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: u8 = 0;
    v___x_5219_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5220_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5220_ == 0 {
        leanh::lean_dec_ref(v_l_5218_);
        leanh::lean_dec_ref(v_inst_5217_);
        leanh::lean_dec_ref(v_inst_5216_);
        return v___x_5219_;
    } else {
        let mut v___f_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5223_: *mut leanh::LeanObject,
    mut v_00_u03b2_5224_: *mut leanh::LeanObject,
    mut v_inst_5225_: *mut leanh::LeanObject,
    mut v_inst_5226_: *mut leanh::LeanObject,
    mut v_l_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: u8 = 0;
    v___x_5228_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5229_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5229_ == 0 {
        leanh::lean_dec_ref(v_l_5227_);
        leanh::lean_dec_ref(v_inst_5226_);
        leanh::lean_dec_ref(v_inst_5225_);
        return v___x_5228_;
    } else {
        let mut v___f_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_5232_: *mut leanh::LeanObject,
    mut v_inst_5233_: *mut leanh::LeanObject,
    mut v_l_5234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    v___x_5235_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5236_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5236_ == 0 {
        leanh::lean_dec(v_l_5234_);
        leanh::lean_dec_ref(v_inst_5233_);
        leanh::lean_dec_ref(v_inst_5232_);
        return v___x_5235_;
    } else {
        let mut v___f_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5239_: *mut leanh::LeanObject,
    mut v_00_u03b2_5240_: *mut leanh::LeanObject,
    mut v_inst_5241_: *mut leanh::LeanObject,
    mut v_inst_5242_: *mut leanh::LeanObject,
    mut v_l_5243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    v___x_5244_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5245_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5245_ == 0 {
        leanh::lean_dec(v_l_5243_);
        leanh::lean_dec_ref(v_inst_5242_);
        leanh::lean_dec_ref(v_inst_5241_);
        return v___x_5244_;
    } else {
        let mut v___f_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_5248_: *mut leanh::LeanObject,
    mut v_inst_5249_: *mut leanh::LeanObject,
    mut v_l_5250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    v___x_5251_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5252_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5252_ == 0 {
        leanh::lean_dec_ref(v_l_5250_);
        leanh::lean_dec_ref(v_inst_5249_);
        leanh::lean_dec_ref(v_inst_5248_);
        return v___x_5251_;
    } else {
        let mut v___f_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5255_: *mut leanh::LeanObject,
    mut v_00_u03b2_5256_: *mut leanh::LeanObject,
    mut v_inst_5257_: *mut leanh::LeanObject,
    mut v_inst_5258_: *mut leanh::LeanObject,
    mut v_l_5259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    v___x_5260_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5261_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5261_ == 0 {
        leanh::lean_dec_ref(v_l_5259_);
        leanh::lean_dec_ref(v_inst_5258_);
        leanh::lean_dec_ref(v_inst_5257_);
        return v___x_5260_;
    } else {
        let mut v___f_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_5264_: *mut leanh::LeanObject,
    mut v_inst_5265_: *mut leanh::LeanObject,
    mut v_l_5266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: u8 = 0;
    v___x_5267_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5268_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5268_ == 0 {
        leanh::lean_dec(v_l_5266_);
        leanh::lean_dec_ref(v_inst_5265_);
        leanh::lean_dec_ref(v_inst_5264_);
        return v___x_5267_;
    } else {
        let mut v___f_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5271_: *mut leanh::LeanObject,
    mut v_inst_5272_: *mut leanh::LeanObject,
    mut v_inst_5273_: *mut leanh::LeanObject,
    mut v_l_5274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    v___x_5275_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1,
    );
    v___x_5276_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_5276_ == 0 {
        leanh::lean_dec(v_l_5274_);
        leanh::lean_dec_ref(v_inst_5273_);
        leanh::lean_dec_ref(v_inst_5272_);
        return v___x_5275_;
    } else {
        let mut v___f_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_LawfulHashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_LawfulHashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Raw(builtin);
}